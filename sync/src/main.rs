use inotify::{Event, EventMask, Inotify, WatchDescriptor, WatchMask};
use serde::Deserialize;
use std::collections::HashMap;
use std::error::Error;
use std::ffi::OsStr;
use std::fs::File;
use std::io::Write;
use std::os::unix::ffi::OsStrExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::time::{Duration, Instant};
use std::{fs, thread};
use tracing::{debug, error, info, trace, warn};

#[derive(Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct System {
    short_name: String,
}

#[derive(Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct Config {
    systems: Vec<System>,
    capture_dir: PathBuf,
}

pub fn watch_mask() -> WatchMask {
    return WatchMask::CREATE | WatchMask::DELETE_SELF | WatchMask::CLOSE_WRITE;
}

pub fn handle_event(
    watcher: &mut Inotify,
    tx: &mpsc::Sender<(PathBuf, Instant)>,
    paths: &mut HashMap<WatchDescriptor, PathBuf>,
    event: Event<&OsStr>,
) -> Result<(), Box<dyn Error>> {
    if event.mask.contains(EventMask::DELETE_SELF) {
        if paths.remove(&event.wd).is_none() {
            warn!("Received {:?} for unknown handler", event.mask);
        }

        if let Err(e) = watcher.rm_watch(event.wd) {
            // this is normal for DELETE_SELF
            debug!("Error removing watch {}", e);
        }
    } else if let Some(root) = paths.get_mut(&event.wd) {
        let path = root.join(event.name.expect("Entries to have a name"));
        handle_path(watcher, tx, paths, path, event.mask)?;
    } else {
        info!("Ignoring {:?}", event);
    }

    Ok(())
}

pub fn handle_path(
    watcher: &mut Inotify,
    tx: &mpsc::Sender<(PathBuf, Instant)>,
    paths: &mut HashMap<WatchDescriptor, PathBuf>,
    path: impl AsRef<Path>,
    mask: EventMask,
) -> Result<(), Box<dyn Error>> {
    let path = path.as_ref();

    if mask.contains(EventMask::CREATE) {
        let metadata = fs::metadata(path)?;
        if metadata.is_dir() {
            let wd = watcher.add_watch(path, watch_mask())?;
            let mut path = path.to_owned();
            let mut file_name = path.file_name().unwrap().to_owned();
            file_name.push("/");
            path.set_file_name(file_name);

            debug!("Adding manager for {:?}", path);

            for entry in fs::read_dir(&path)? {
                let entry = entry?;
                handle_path(watcher, tx, paths, entry.path(), EventMask::CREATE)?;
            }

            paths.insert(wd, path);
        }
    } else if mask.contains(EventMask::CLOSE_WRITE) {
        if path.extension() == Some(OsStr::new("wav")) {
            let media_path = pathdiff::diff_paths(path, "/media").unwrap();

            tx.send((media_path, Instant::now()))?;
        } else {
            debug!("Unsupported file {:?}", path);
        }
    } else {
        debug!("Unsupported event {:?}", mask);
    }

    Ok(())
}

fn sync(rx: mpsc::Receiver<(PathBuf, Instant)>) {
    let program = Path::new("/app/sync.sh");
    if !program.exists() {
        panic!("Sync script at {:?} does not exist", program);
    }

    for (wav, instant) in rx {
        info!("Processing {:?}", wav);

        if let Some(sleep_duration) =
            Duration::from_millis(100).checked_sub(Instant::now().duration_since(instant))
        {
            trace!("Sleeping for {:?}", sleep_duration);
            thread::sleep(sleep_duration);
        }

        let json = wav.with_extension("json");

        let mut sync = Command::new(program).stdin(Stdio::piped()).spawn().unwrap();

        let mut stdin = sync.stdin.take().unwrap();
        stdin.write_all(wav.into_os_string().as_bytes()).unwrap();
        stdin.write_all(b"\0").unwrap();
        stdin.write_all(json.into_os_string().as_bytes()).unwrap();
        stdin.write_all(b"\0").unwrap();
        drop(stdin);

        if let Err(e) = sync.wait() {
            error!("Failed running {:?} {}", program, e);
        }
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    tracing_subscriber::fmt::init();

    let config = Path::new("/app/config.json");
    info!("Loading config {:?}", config);
    let reader = File::open(config)?;

    let config = serde_json::from_reader::<_, Config>(reader)?;
    let capture_dir = config.capture_dir;
    info!("Capture directory {:?}", capture_dir);

    let systems = config
        .systems
        .into_iter()
        .map(|s| capture_dir.join(s.short_name))
        .collect::<Vec<_>>();

    let (tx, rx) = mpsc::channel();
    thread::Builder::new()
        .name("sync".to_string())
        .spawn(move || sync(rx))?;

    let mut watcher = Inotify::init()?;
    let mut paths = HashMap::<WatchDescriptor, PathBuf>::new();

    for system in systems.iter() {
        if !system.exists() {
            info!("Creating media directory {:?}", system);
            fs::create_dir(system)?;
        }

        info!("Adding system watch {:?}", system);
        handle_path(&mut watcher, &tx, &mut paths, system, EventMask::CREATE)?;
    }

    let mut buffer = [0; 4096];

    loop {
        for event in watcher.read_events_blocking(&mut buffer)? {
            trace!("Received event {:?}", event);
            handle_event(&mut watcher, &tx, &mut paths, event)?;
        }
    }
}
