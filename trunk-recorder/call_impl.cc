#include "call_impl.h"
#include "call.h"
#include "formatter.h"
#include "recorders/recorder.h"
#include "source.h"

std::string Call_impl::get_temp_dir() {
  return this->config.temp_dir;
}

std::shared_ptr<Call> Call::make(TrunkMessage message, const std::shared_ptr<System> &s, Config c) {
  auto call = std::make_shared<Call_impl>(message, s, c);
  return call;
}

Call_impl::Call_impl(long t, double f, const std::shared_ptr<System> &s, Config c) {
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

Call_impl::Call_impl(TrunkMessage message, const std::shared_ptr<System> &s, Config c) {
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

void Call_impl::restart_call() {
}

long Call_impl::get_call_num() {
  return call_num;
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

void Call_impl::set_debug_recording(bool m) {
  debug_recording = m;
}

bool Call_impl::get_debug_recording() {
  return debug_recording;
}

void Call_impl::set_sigmf_recording(bool m) {
  sigmf_recording = m;
}

bool Call_impl::get_sigmf_recording() {
  return sigmf_recording;
}

void Call_impl::set_tdma_slot(int m) {
  tdma_slot = m;
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

void Call_impl::set_current_source_id(long src) {
  curr_src_id = src;
}

void Call_impl::set_rust_call_id(uint64_t id) {
  rust_call_id = id;
}

uint64_t Call_impl::get_rust_call_id() {
  return rust_call_id;
}

long Call_impl::call_counter = 0;
