#include "call_impl.h"
#include "call.h"
#include "event_sink.h"
#include "formatter.h"
#include "recorders/recorder.h"
#include "source.h"
#include <signal.h>
#include <stdio.h>

std::string Call_impl::get_temp_dir() {
  return this->config.temp_dir;
}

std::shared_ptr<Call> Call::make(TrunkMessage message, const std::shared_ptr<System> &s, Config c) {
  auto call = std::make_shared<Call_impl>(message, s, c);
  // add_source must be called after make_shared so that shared_from_this() works
  call->add_source(message.source);
  return call;
}

Call_impl::Call_impl(long t, double f, const std::shared_ptr<System> &s, Config c) {
  config = c;
  call_num = call_counter++;
  noise = DB_UNSET;
  signal = DB_UNSET;
  final_length = 0;
  idle_count = 0;
  curr_freq = 0;
  freq_error = 0;
  curr_src_id = -1;
  talkgroup = t;
  sys = s;
  start_time = std::chrono::system_clock::now();
  stop_time = std::chrono::system_clock::now();
  last_update = std::chrono::steady_clock::now();
  state = MONITORING;
  monitoringState = UNSPECIFIED;
  debug_recording = false;
  sigmf_recording = false;
  phase2_tdma = false;
  tdma_slot = 0;
  encrypted = false;
  emergency = false;
  duplex = false;
  mode = false;
  is_analog = false;
  was_update = false;
  priority = 0;
  set_freq(f);
}

Call_impl::Call_impl(TrunkMessage message, const std::shared_ptr<System> &s, Config c) {
  config = c;
  call_num = call_counter++;
  noise = DB_UNSET;
  signal = DB_UNSET;
  final_length = 0;
  idle_count = 0;
  curr_src_id = -1;
  curr_freq = 0;
  freq_error = 0;
  talkgroup = message.talkgroup;
  sys = s;
  start_time = std::chrono::system_clock::now();
  stop_time = std::chrono::system_clock::now();
  last_update = std::chrono::steady_clock::now();
  state = MONITORING;
  monitoringState = UNSPECIFIED;
  debug_recording = false;
  sigmf_recording = false;
  phase2_tdma = message.phase2_tdma;
  tdma_slot = message.tdma_slot;
  encrypted = message.encrypted;
  emergency = message.emergency;
  duplex = message.duplex;
  mode = message.mode;
  is_analog = false;
  priority = message.priority;
  if (message.message_type == GRANT) {
    was_update = false;
  } else {
    was_update = true;
  }
  set_freq(message.freq);
}
/*
Call_impl::~Call_impl() {

}*/

void Call_impl::restart_call() {
}

void Call_impl::stop_call() {

  if (this->get_recorder()) {
    // If the call is being recorded, check to see if the recorder is currently in an INACTIVE state. This means that the recorder is not
    // doing anything and can be stopped.
    if ((state == RECORDING) && this->get_recorder()->is_idle()) {
      std::string loghdr = log_header( sys->get_short_name(), this->get_call_num(), this->get_talkgroup(), this->get_freq());
      BOOST_LOG_TRIVIAL(info) << loghdr << "Stopping Recorded Call_impl - Last Update: " << this->since_last_update().count() << "s";
    }
  }
}
long Call_impl::get_call_num() {
  return call_num;
}
void Call_impl::conclude_call() {

  // BOOST_LOG_TRIVIAL(info) << "conclude_call()";
  stop_time = std::chrono::system_clock::now();

  if (state == RECORDING || (state == MONITORING && monitoringState == SUPERSEDED)) {
    auto rec = recorder.lock();
    if (!rec) {
      BOOST_LOG_TRIVIAL(error) << "Call_impl::end_call() State is recording, but no recorder assigned!";
    } else {
      final_length = rec->get_current_length();

      if (this->is_conventional()) {
        // Update the signal and noise levels for the call
        // the squelch could be open if the program is being forced to stop
        if (rec->is_idle()) {
          this->set_noise(rec->get_pwr());
        } else {
          this->set_signal(rec->get_pwr());
        }
          std::string loghdr = log_header( sys->get_short_name(), this->get_call_num(), this->get_talkgroup(), this->get_freq());
          BOOST_LOG_TRIVIAL(info) << loghdr << "\u001b[33mConcluding Recorded Call\u001b[0m - Last Update: " << this->since_last_update().count() << "s\tRecorder last write:" << rec->since_last_write().count() << "s\tCall Elapsed: " << this->elapsed().count() << "s\t Signal: " << floor(this->get_signal()) << "dBm\t Noise: " << floor(this->get_noise()) << "dBm";
      } else {
          std::string loghdr = log_header( sys->get_short_name(), this->get_call_num(), this->get_talkgroup(), this->get_freq());
          BOOST_LOG_TRIVIAL(info) << loghdr << "\u001b[33mConcluding Recorded Call\u001b[0m - Last Update: " << this->since_last_update().count() << "s\tRecorder last write:" << rec->since_last_write().count() << "s\tCall Elapsed: " << this->elapsed().count() << "s";
      }
      if (was_update) {
        std::string loghdr = log_header( sys->get_short_name(), this->get_call_num(), this->get_talkgroup(), this->get_freq());
        BOOST_LOG_TRIVIAL(info) << loghdr << "\u001b[33mCall was UPDATE not GRANT\u001b[0m";
      }
      freq_error = rec->get_freq_error();
      rec->stop();

      if (auto sigmf_rec = sigmf_recorder.lock()) {
        if (this->get_sigmf_recording()) {
          sigmf_rec->stop();
        }
      }

      if (auto debug_rec = debug_recorder.lock()) {
        if (this->get_debug_recording()) {
          debug_rec->stop();
        }
      }

      if (this->sys->get_system_type() == SYS_CONVENTIONAL_DMR) {
        auto dmr_rec = std::dynamic_pointer_cast<dmr_recorder>(rec);
        if (!dmr_rec) {
          BOOST_LOG_TRIVIAL(error) << "Call_impl::conclude_call() conventionalDMR system but recorder is not a dmr_recorder!";
        } else {
          // Conventional DMR is recorded on two slots, so we need to conclude the call for each slot
          transmission_list = dmr_rec->get_transmission_list(0);
          tdma_slot = 0;
          config.event_sink->conclude_call(shared_from_this(), sys, config);
          transmission_list = dmr_rec->get_transmission_list(1);
          tdma_slot = 1;
          config.event_sink->conclude_call(shared_from_this(), sys, config);
        }
      } else {
        // All other system types do not have multiple recorders
        transmission_list = rec->get_transmission_list();
        config.event_sink->conclude_call(shared_from_this(), sys, config);
      }
    }

  } else if (state == MONITORING) {
    // Monitored-only calls (encrypted, no source, etc.) never got a recorder,
    // but plugins still need to know the call ended.
    config.event_sink->conclude_call(shared_from_this(), sys, config);
  }
}
void Call_impl::set_sigmf_recorder(const std::shared_ptr<Recorder> &r) {
  sigmf_recorder = r;
}

std::shared_ptr<Recorder> Call_impl::get_sigmf_recorder() {
  return sigmf_recorder.lock();
}

void Call_impl::set_debug_recorder(const std::shared_ptr<Recorder> &r) {
  debug_recorder = r;
}

std::shared_ptr<Recorder> Call_impl::get_debug_recorder() {
  return debug_recorder.lock();
}

void Call_impl::set_recorder(const std::shared_ptr<Recorder> &r) {
  recorder = r;
}

std::shared_ptr<Recorder> Call_impl::get_recorder() {
  return recorder.lock();
}

double Call_impl::get_freq() {
  return curr_freq;
}

int Call_impl::get_freq_error() {
  return freq_error;
}

double Call_impl::get_current_length() {
  if (state == RECORDING) {
    auto rec = recorder.lock();
    if (rec) {
      return rec->get_current_length();
    }
  }
  return 0;
}

std::shared_ptr<System> Call_impl::get_system() {
  return sys;
}

void Call_impl::set_freq(double f) {
  if (f != curr_freq) {
    curr_freq = f;
  }
}

int Call_impl::get_sys_num() {
  return sys->get_sys_num();
}
std::string Call_impl::get_short_name() {
  return sys->get_short_name();
}
long Call_impl::get_talkgroup() {
  return talkgroup;
}

std::vector<Transmission> Call_impl::get_transmissions() {
  return transmission_list;
}

void Call_impl::set_debug_recording(bool m) {
  debug_recording = m;
}

bool Call_impl::get_debug_recording() {
  return debug_recording;
}

void Call_impl::set_sigmf_recording(bool m) {
  sigmf_recording = m;
}

void Call_impl::set_is_analog(bool a) {
  is_analog = a;
}

bool Call_impl::get_is_analog() {
  return is_analog;
}

bool Call_impl::get_sigmf_recording() {
  return sigmf_recording;
}

void Call_impl::set_state(State s) {
  state = s;
}

State Call_impl::get_state() {
  return state;
}

void Call_impl::set_monitoring_state(MonitoringState s) {
  monitoringState = s;
}

MonitoringState Call_impl::get_monitoring_state() {
  return monitoringState;
}

void Call_impl::set_encrypted(bool m) {
  encrypted = m;
}

bool Call_impl::get_encrypted() {
  return encrypted;
}

void Call_impl::set_emergency(bool m) {
  emergency |= m;
}

bool Call_impl::get_emergency() {
  return emergency;
}

int Call_impl::get_priority() {
  return priority;
}

bool Call_impl::get_mode() {
  return mode;
}

bool Call_impl::get_duplex() {
  return duplex;
}

double Call_impl::get_signal() {
  return signal;
}

double Call_impl::get_noise() {
  return noise;
}

void Call_impl::set_signal(double s) {
  signal = s;
}

void Call_impl::set_noise(double n) {
  noise = n;
}

void Call_impl::set_tdma_slot(int m) {
  tdma_slot = m;
  if (!phase2_tdma && tdma_slot) {
    BOOST_LOG_TRIVIAL(error) << "WHAT! SLot is 1 and TDMA is off";
  }
}

int Call_impl::get_tdma_slot() {
  return tdma_slot;
}

void Call_impl::set_phase2_tdma(bool p) {
  phase2_tdma = p;
}

bool Call_impl::get_phase2_tdma() {
  return phase2_tdma;
}

const std::string& Call_impl::get_xor_mask() {
  return sys->get_xor_mask();
}

long Call_impl::get_current_source_id() {
  return curr_src_id;
}

bool Call_impl::add_source(long src) {
  if (src == -1) {
    return false;
  }

  if (src == curr_src_id) {
    return false;
  }

  curr_src_id = src;

  if (state == RECORDING) {
    auto rec = this->get_recorder();
    if (rec) {
      rec->set_source(src);
    }
  }

  config.event_sink->signal(src, nullptr, gr::blocks::SignalType::Normal, shared_from_this(), this->get_system(), nullptr);

  return true;
}

bool Call_impl::update(TrunkMessage message) {
  last_update = std::chrono::steady_clock::now();
  if ((message.freq != this->curr_freq) || (message.talkgroup != this->talkgroup)) {
    std::string loghdr = log_header( sys->get_short_name(), this->get_call_num(), this->get_talkgroup(), this->get_freq());
    BOOST_LOG_TRIVIAL(error) << loghdr << "C\033[0m\tCall_impl Update, message mismatch - \ttMsg Tg: " << message.talkgroup << "\tMsg Freq: " << message.freq;
  } else {
    return add_source(message.source);
  }
  return false;
}

std::chrono::duration<double> Call_impl::since_last_update() {
  return std::chrono::steady_clock::now() - last_update;
}

std::chrono::duration<double> Call_impl::elapsed() {
  return std::chrono::system_clock::now() - start_time;
}

int Call_impl::get_idle_count() {
  return idle_count;
}

void Call_impl::reset_idle_count() {
  idle_count = 0;
}

void Call_impl::increase_idle_count() {
  idle_count++;
}

SystemType Call_impl::get_system_type() {
  return sys->get_system_type();
}


bool Call_impl::get_conversation_mode() {
  if (!sys) {
    BOOST_LOG_TRIVIAL(error) << "\tWEIRD! for some reason, call has no sys - Call_impl TG: " << get_talkgroup() << "\t Call_impl Freq: " << get_freq();
    return false;
  }
  return sys->get_conversation_mode();
}

long Call_impl::call_counter = 0;