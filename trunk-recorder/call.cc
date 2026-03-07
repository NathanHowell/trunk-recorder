#include "call.h"
#include "recorders/recorder.h"

std::shared_ptr<Call> Call::make(const std::shared_ptr<System> &s) {
  return std::make_shared<Call>(s);
}

Call::Call(const std::shared_ptr<System> &s) {
  sys = s;
  rust_call_id = 0;
}

void Call::restart_call(const RecorderConfig &cfg) {
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

std::shared_ptr<System> Call::get_system() const {
  return sys;
}

void Call::set_rust_call_id(uint64_t id) {
  rust_call_id = id;
}

uint64_t Call::get_rust_call_id() const {
  return rust_call_id;
}
