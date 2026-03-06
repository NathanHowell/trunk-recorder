#ifndef CALL_H
#define CALL_H

#include "./global_structs.h"
#include <boost/log/trivial.hpp>
#include <memory>
#include <string>
#include <sys/time.h>
#include <vector>

class Recorder;
class System;

#include "state.h"
#include "systems/parser.h"
#include "systems/system.h"

class Call : public std::enable_shared_from_this<Call> {
public:
  static std::shared_ptr<Call> make(TrunkMessage message, const std::shared_ptr<System> &s, Config c);
  virtual ~Call(){};

  // Recorder plumbing (C++ owns shared_ptrs)
  virtual void set_recorder(const std::shared_ptr<Recorder> &r) = 0;
  virtual std::shared_ptr<Recorder> get_recorder() = 0;
  virtual void set_debug_recorder(const std::shared_ptr<Recorder> &r) = 0;
  virtual std::shared_ptr<Recorder> get_debug_recorder() = 0;
  virtual void set_sigmf_recorder(const std::shared_ptr<Recorder> &r) = 0;
  virtual std::shared_ptr<Recorder> get_sigmf_recorder() = 0;
  virtual void set_debug_recording(bool m) = 0;
  virtual bool get_debug_recording() = 0;
  virtual void set_sigmf_recording(bool m) = 0;
  virtual bool get_sigmf_recording() = 0;

  // Identity (read by recorders via weak_ptr<Call>)
  virtual long get_talkgroup() = 0;
  virtual long get_call_num() = 0;
  virtual double get_freq() = 0;
  virtual void set_freq(double f) = 0;
  virtual int get_sys_num() = 0;
  virtual std::string get_short_name() = 0;
  virtual std::string get_temp_dir() = 0;
  virtual const std::string& get_xor_mask() = 0;
  virtual std::shared_ptr<System> get_system() = 0;
  virtual long get_current_source_id() = 0;
  virtual void set_current_source_id(long src) = 0;

  // P25/DMR fields (read by recorders at start time)
  virtual void set_phase2_tdma(bool m) = 0;
  virtual bool get_phase2_tdma() = 0;
  virtual void set_tdma_slot(int s) = 0;
  virtual int get_tdma_slot() = 0;

  // Conventional
  virtual void restart_call() = 0;
  virtual time_t get_start_time() = 0;
  virtual bool is_conventional() = 0;
  virtual int get_freq_error() = 0;

  // Rust call ID for round-tripping through audio callbacks
  virtual void set_rust_call_id(uint64_t id) = 0;
  virtual uint64_t get_rust_call_id() = 0;
};

#endif
