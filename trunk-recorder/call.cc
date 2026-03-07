#include "call.h"
#include "formatter.h"
#include "recorders/recorder.h"
#include "source.h"

std::shared_ptr<Call> Call::make(TrunkMessage message, const std::shared_ptr<System> &s, Config c) {
  return std::make_shared<Call>(message, s, c);
}

Call::Call(long t, double f, const std::shared_ptr<System> &s, Config c) {
  config = c;
  call_num = call_counter++;
  freq_error = 0;
  curr_freq = 0;
  curr_src_id = -1;
  talkgroup = t;
  sys = s;
  start_time = std::chrono::system_clock::now();
  debug_recording = false;
  sigmf_recording = false;
  phase2_tdma = false;
  tdma_slot = 0;
  rust_call_id = 0;
  set_freq(f);
}

Call::Call(TrunkMessage message, const std::shared_ptr<System> &s, Config c) {
  config = c;
  call_num = call_counter++;
  freq_error = 0;
  curr_freq = 0;
  curr_src_id = -1;
  talkgroup = message.talkgroup;
  sys = s;
  start_time = std::chrono::system_clock::now();
  debug_recording = false;
  sigmf_recording = false;
  phase2_tdma = message.phase2_tdma;
  tdma_slot = message.tdma_slot;
  rust_call_id = 0;
  set_freq(message.freq);
}

void Call::restart_call() {
}

void Call::set_sigmf_recorder(const std::shared_ptr<Recorder> &r) {
  sigmf_recorder = r;
}

std::shared_ptr<Recorder> Call::get_sigmf_recorder() const {
  return sigmf_recorder.lock();
}

void Call::set_debug_recorder(const std::shared_ptr<Recorder> &r) {
  debug_recorder = r;
}

std::shared_ptr<Recorder> Call::get_debug_recorder() const {
  return debug_recorder.lock();
}

void Call::set_recorder(const std::shared_ptr<Recorder> &r) {
  recorder = r;
}

std::shared_ptr<Recorder> Call::get_recorder() const {
  return recorder.lock();
}

int Call::get_freq_error() const {
  return freq_error;
}

std::shared_ptr<System> Call::get_system() const {
  return sys;
}

void Call::set_freq(double f) {
  if (f != curr_freq) {
    curr_freq = f;
  }
}

void Call::set_debug_recording(bool m) {
  debug_recording = m;
}

bool Call::get_debug_recording() const {
  return debug_recording;
}

void Call::set_sigmf_recording(bool m) {
  sigmf_recording = m;
}

bool Call::get_sigmf_recording() const {
  return sigmf_recording;
}

void Call::set_rust_call_id(uint64_t id) {
  rust_call_id = id;
}

uint64_t Call::get_rust_call_id() const {
  return rust_call_id;
}

long Call::call_counter = 0;
