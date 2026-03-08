
#include "sigmf_recorder_impl.h"
#include <boost/log/trivial.hpp>
#include <stdexcept>

// static int rec_counter=0;



sigmf_recorder_sptr make_sigmf_recorder(const std::shared_ptr<Source> &src, Recorder_Type type) {
  sigmf_recorder *recorder = new sigmf_recorder_impl(src, type);

  return gnuradio::get_initial_sptr(recorder);
}

sigmf_recorder_impl::sigmf_recorder_impl(const std::shared_ptr<Source> &src, Recorder_Type type)
    : gr::hier_block2("sigmf_recorder",
                      gr::io_signature::make(1, 1, sizeof(gr_complex)),
                      gr::io_signature::make(0, 0, sizeof(float))),
      Recorder(type),
      config(src->get_config()) {

        if (type == SIGMFC) {
          conventional = true;
        } else if (type == SIGMF) {
          conventional = false;
        } else {
          throw std::runtime_error("Cannot create SIGMF recorder with incompatible type");
        }
  source = src;
  freq = source->get_center();
  center = source->get_center();
  silence_frames = source->get_silence_frames();
  squelch_db = 0;
  input_rate = source->get_rate();
  talkgroup = 0;

  rec_num = rec_counter++;

  state = REC_INACTIVE;

  // double symbol_rate         = 4800;

  starttime = std::chrono::steady_clock::now();



  // tm *ltm = localtime(&starttime);

  int nchars = snprintf(filename, 160, "%ld-%lld_%g.raw", talkgroup, static_cast<long long>(starttime.time_since_epoch().count()), freq);

  if (nchars >= 160) {
    BOOST_LOG_TRIVIAL(error) << "Analog Recorder: Path longer than 160 charecters";
  }
  raw_sink = gr::blocks::file_sink::make(sizeof(gr_complex), filename);

  //initialize_prefilter();
  //initialize_prefilter_xlat();
  
  prefilter = xlat_channelizer::make(input_rate, channelizer::phase1_samples_per_symbol, channelizer::phase1_symbol_rate, xlat_channelizer::channel_bandwidth, center, conventional);
  set_enabled(false);
  connect(squelch, 0, raw_sink, 0);
}

void sigmf_recorder_impl::tune_offset(double f) { prefilter->tune_offset(f); }
void sigmf_recorder_impl::tune_freq(double) {}
void sigmf_recorder_impl::set_source(long) {}
void sigmf_recorder_impl::set_system(const std::shared_ptr<System> &) {}
double sigmf_recorder_impl::get_pwr() const { return prefilter->get_pwr(); }
std::vector<Transmission> sigmf_recorder_impl::get_transmission_list() { return {}; }

int sigmf_recorder_impl::get_num() const {
  return rec_num;
}

void sigmf_recorder_impl::set_enabled(bool enabled) {
  source->set_selector_port_enabled(selector_port, enabled);
}

int sigmf_recorder_impl::get_freq_error() const { // get frequency error from FLL and convert to Hz
  return prefilter->get_freq_error();
}

std::chrono::duration<double> sigmf_recorder_impl::since_last_write() const {
  return std::chrono::duration<double>::zero(); // sigmf recorders write continuously and never time out
}

/*
void sigmf_recorder_impl::tune_offset(double f) {
  // have to flip this for 3.7
  // BOOST_LOG_TRIVIAL(info) << "Offset set to: " << offset_amount << " Freq: "
  //  << freq;
  freq_xlat->set_center_freq(-f);
}*/

RecorderState sigmf_recorder_impl::get_state() const {
  return state;
}

void sigmf_recorder_impl::set_squelch_callback(std::function<void(bool, double)> cb) {
  prefilter->set_squelch_callback(std::move(cb));
}

void sigmf_recorder_impl::stop() {
  if (state == REC_ACTIVE) {
    BOOST_LOG_TRIVIAL(info) << "\u001b[32mStopping SigMF Recorder Num [" << rec_num << "]\u001b[0m TG: " << talkgroup << " Freq: " << freq;

    state = REC_INACTIVE;
    set_enabled(false);
    raw_sink->close();
  } else {
    BOOST_LOG_TRIVIAL(error) << "sigmf_recorder.cc: Trying to Stop an Inactive Logger!!!";
  }
}

void sigmf_recorder_impl::flush_audio() {
  // No plugin_wrapper — SigMF records raw IQ, not decoded audio.
}

bool sigmf_recorder_impl::start(const RecorderConfig &config) {
  if (state == REC_INACTIVE) {
    starttime = std::chrono::steady_clock::now();
    int nchars;
    time_t wall_time = std::chrono::system_clock::to_time_t(std::chrono::system_clock::now());
    tm *ltm = localtime(&wall_time);
    talkgroup = config.talkgroup;
    freq = config.freq;
    rust_call_id = config.rust_call_id;

    int offset_amount = (center - freq);
    prefilter->tune_offset(offset_amount);

    std::stringstream path_stream;

    path_stream << config.temp_dir << "/" << config.short_name << "/" << 1900 + ltm->tm_year << "/" << 1 + ltm->tm_mon << "/" << ltm->tm_mday;
    std::string path_string = path_stream.str();
    std::filesystem::create_directories(path_string);

    nchars = snprintf(filename, 255, "%s/%ld-%ld_%.0f-call_%lu.sigmf-data", path_string.c_str(), talkgroup, (long)wall_time, config.freq, config.call_num);
    if (nchars >= 255) {
      BOOST_LOG_TRIVIAL(error) << "SigMF-meta: Path longer than 255 charecters";
    }

    raw_sink->open(filename);
    state = REC_ACTIVE;

    squelch_db = config.squelch_db;
    if (!conventional) {
      set_enabled(true);
    }
    prefilter->set_squelch_db(squelch_db);

    std::string src_description = source->get_driver() + ": " + source->get_device() + " - " + source->get_antenna();
    time_t now;
    time(&now);
    char buf[sizeof "2011-10-08T07:07:09Z"];
    strftime(buf, sizeof buf, "%FT%TZ", gmtime(&now));
    std::string start_time(buf);
    nlohmann::json j = {
      {"global", {
        {"core:datatype", "cf32_le"},
        {"core:sample_rate", channelizer::phase1_samples_per_symbol * channelizer::phase1_symbol_rate},
        {"core:hw", src_description},
        {"core:recorder", "Trunk Recorder"},
        {"core:version", "1.0.0"}
      }},
      {"captures", nlohmann::json::array(
        { nlohmann::json::object({
          {"core:sample_start", 0},
          {"core:frequency", freq},
          {"core:datetime", start_time}
        })
        }
      )},
      {"annotations", nlohmann::json::array({})}
    };

    nchars = snprintf(filename, 255, "%s/%ld-%lld_%.0f-call_%lu.sigmf-meta", path_string.c_str(), talkgroup, static_cast<long long>(starttime.time_since_epoch().count()), config.freq, config.call_num);
    if (nchars >= 255) {
      BOOST_LOG_TRIVIAL(error) << "SigMF-meta: Path longer than 255 charecters";
    }
    std::ofstream o(filename);
    o << std::setw(4) << j << std::endl;
    o.close();

  } else {
    BOOST_LOG_TRIVIAL(error) << "sigmf_recorder.cc: Trying to Start an already Active Logger!!!";
  }
  return true;
}

std::vector<gr::block_sptr> sigmf_recorder_impl::get_metric_blocks() const {
  std::vector<gr::block_sptr> blocks;
  if (prefilter) {
    auto inner = prefilter->get_metric_blocks();
    blocks.insert(blocks.end(), inner.begin(), inner.end());
  }
  return blocks;
}
