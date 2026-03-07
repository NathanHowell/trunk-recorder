#ifndef CALL_H
#define CALL_H

#include "./global_structs.h"
#include <memory>
#include <string>

class Recorder;
class System;

#include "recorder_config.h"
#include "state.h"
#include "systems/parser.h"
#include "systems/system.h"

class Call : public std::enable_shared_from_this<Call> {
public:
  Call(const std::shared_ptr<System> &s, Config c);
  Call(TrunkMessage message, const std::shared_ptr<System> &s, Config c);
  virtual ~Call() {}

  static std::shared_ptr<Call> make(TrunkMessage message, const std::shared_ptr<System> &s, Config c);

  // Recorder plumbing (C++ owns shared_ptrs)
  virtual void set_recorder(const std::shared_ptr<Recorder> &r);
  std::shared_ptr<Recorder> get_recorder() const;
  void set_debug_recorder(const std::shared_ptr<Recorder> &r);
  std::shared_ptr<Recorder> get_debug_recorder() const;
  void set_sigmf_recorder(const std::shared_ptr<Recorder> &r);
  std::shared_ptr<Recorder> get_sigmf_recorder() const;
  bool get_debug_recording() const;
  void set_debug_recording(bool m);
  bool get_sigmf_recording() const;
  void set_sigmf_recording(bool m);

  // Identity
  std::shared_ptr<System> get_system() const;

  // Conventional (virtual for Call_conventional override)
  virtual void restart_call(const RecorderConfig &cfg);

  // Rust call ID for round-tripping through audio callbacks
  void set_rust_call_id(uint64_t id);
  uint64_t get_rust_call_id() const;

protected:
  bool debug_recording;
  bool sigmf_recording;

  std::shared_ptr<System> sys;
  Config config;
  std::weak_ptr<Recorder> recorder;
  std::weak_ptr<Recorder> debug_recorder;
  std::weak_ptr<Recorder> sigmf_recorder;

  uint64_t rust_call_id;
};

#endif
