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

long Call::get_call_num() const {
  return call_num;
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

double Call::get_freq() const {
  return curr_freq;
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

int Call::get_sys_num() const {
  return sys->get_sys_num();
}

std::string Call::get_short_name() const {
  return sys->get_short_name();
}

std::string Call::get_temp_dir() const {
  return config.temp_dir;
}

long Call::get_talkgroup() const {
  return talkgroup;
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

void Call::set_tdma_slot(int m) {
  tdma_slot = m;
}

int Call::get_tdma_slot() const {
  return tdma_slot;
}

void Call::set_phase2_tdma(bool p) {
  phase2_tdma = p;
}

bool Call::get_phase2_tdma() const {
  return phase2_tdma;
}

const std::string &Call::get_xor_mask() const {
  return sys->get_xor_mask();
}

long Call::get_current_source_id() const {
  return curr_src_id;
}

void Call::set_current_source_id(long src) {
  curr_src_id = src;
}

time_t Call::get_start_time() const {
  return std::chrono::system_clock::to_time_t(start_time);
}

double Call::get_squelch_db() const {
  return sys->get_squelch_db();
}

void Call::set_rust_call_id(uint64_t id) {
  rust_call_id = id;
}

uint64_t Call::get_rust_call_id() const {
  return rust_call_id;
}

long Call::call_counter = 0;
