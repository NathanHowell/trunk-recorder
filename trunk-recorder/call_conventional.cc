
#include "call_conventional.h"
#include "formatter.h"
#include "recorder_config.h"
#include "recorders/recorder.h"
#include <boost/algorithm/string.hpp>

Call_conventional::Call_conventional(long t, double f, const std::shared_ptr<System> &s, Config c, double squelch_db, bool signal_detection) : Call(t, f, s, c) {
  this->squelch_db = squelch_db;
  this->signal_detection = signal_detection;
  BOOST_LOG_TRIVIAL(info) << "[" << sys->get_short_name() << "]\tFreq: " << format_freq(f) << "\tSquelch: " << squelch_db << " dB\tSignal Detection: " << signal_detection;
}

void Call_conventional::restart_call() {
  call_num = call_counter++;
  curr_src_id = -1;
  start_time = std::chrono::system_clock::now();
  debug_recording = false;
  phase2_tdma = false;
  tdma_slot = 0;
  auto rec = recorder.lock();
  if (rec) {
    rec->start(RecorderConfig{
        .talkgroup = talkgroup,
        .call_num = call_num,
        .freq = curr_freq,
        .short_name = sys->get_short_name(),
        .temp_dir = config.temp_dir,
        .squelch_db = squelch_db,
        .digital_levels = sys->get_digital_levels(),
        .rust_call_id = rust_call_id,
    });
  }
}

time_t Call_conventional::get_start_time() const {
  return std::chrono::system_clock::to_time_t(start_time);
}

void Call_conventional::set_recorder(const std::shared_ptr<Recorder> &r) {
  recorder = r;
  BOOST_LOG_TRIVIAL(info) << "[" << sys->get_short_name() << "]\tTG: " << this->get_talkgroup() << "\tFreq: " << format_freq(this->get_freq());
}

double Call_conventional::get_squelch_db() const {
  return squelch_db;
}

bool Call_conventional::get_signal_detection() const {
  return signal_detection;
}
