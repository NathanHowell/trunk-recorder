
#include "call_conventional.h"
#include "formatter.h"
#include "recorder_config.h"
#include "recorders/recorder.h"
#include <boost/algorithm/string.hpp>

Call_conventional::Call_conventional(long t, double f, const std::shared_ptr<System> &s, Config c, double squelch_db, bool signal_detection) : Call(s, c) {
  this->squelch_db = squelch_db;
  this->signal_detection = signal_detection;
  this->talkgroup = t;
  this->freq = f;
  BOOST_LOG_TRIVIAL(info) << "[" << sys->get_short_name() << "]\tFreq: " << format_freq(f) << "\tSquelch: " << squelch_db << " dB\tSignal Detection: " << signal_detection;
}

void Call_conventional::restart_call(const RecorderConfig &cfg) {
  debug_recording = false;
  auto rec = recorder.lock();
  if (rec) {
    rec->start(cfg);
  }
}

void Call_conventional::set_recorder(const std::shared_ptr<Recorder> &r) {
  recorder = r;
  BOOST_LOG_TRIVIAL(info) << "[" << sys->get_short_name() << "]\tTG: " << talkgroup << "\tFreq: " << format_freq(freq);
}
