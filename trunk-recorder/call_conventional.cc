
#include "call_conventional.h"
#include "formatter.h"
#include "recorders/recorder.h"
#include <boost/algorithm/string.hpp>

Call_conventional::Call_conventional(long t, double f, const std::shared_ptr<System> &s, Config c, double squelch_db, bool signal_detection) : Call_impl(t, f, s, c) {
  this->squelch_db = squelch_db;
  this->signal_detection = signal_detection;
  BOOST_LOG_TRIVIAL(info) << "[" << sys->get_short_name() << "]\tFreq: " << format_freq(f) << "\tSquelch: " << squelch_db << " dB\tSignal Detection: " << signal_detection;
}

void Call_conventional::restart_call() {
  call_num = call_counter++;
  idle_count = 0;
  signal = DB_UNSET;
  noise = DB_UNSET;
  curr_src_id = -1;
  start_time = std::chrono::system_clock::now();
  stop_time = std::chrono::system_clock::now();
  last_update = std::chrono::steady_clock::now();
  state = RECORDING;
  debug_recording = false;
  phase2_tdma = false;
  tdma_slot = 0;
  encrypted = false;
  emergency = false;
  this->update_talkgroup_display();
  auto rec = recorder.lock();
  if (rec) {
    rec->start(shared_from_this());
  }
}

time_t Call_conventional::get_start_time() {
  // Fixes https://github.com/robotastic/trunk-recorder/issues/103#issuecomment-284825841
  start_time = stop_time - std::chrono::duration_cast<std::chrono::system_clock::duration>(std::chrono::duration<double>(final_length));
  return std::chrono::system_clock::to_time_t(start_time);
}

void Call_conventional::set_recorder(const std::shared_ptr<Recorder> &r) {
  recorder = r;
  BOOST_LOG_TRIVIAL(info) << "[" << sys->get_short_name() << "]\tTG: " << this->get_talkgroup_display() << "\tFreq: " << format_freq(this->get_freq());
}

void Call_conventional::recording_started() {
  start_time = std::chrono::system_clock::now();
}

double Call_conventional::get_squelch_db() {
  return squelch_db;
}

bool Call_conventional::get_signal_detection() {
  return signal_detection;
}