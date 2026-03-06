#ifndef CALL_H
#define CALL_H

#include "./global_structs.h"
#include <boost/log/trivial.hpp>
#include <chrono>
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
  Call(long t, double f, const std::shared_ptr<System> &s, Config c);
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
  void set_debug_recording(bool m);
  bool get_debug_recording() const;
  void set_sigmf_recording(bool m);
  bool get_sigmf_recording() const;

  // Identity
  long get_talkgroup() const;
  long get_call_num() const;
  double get_freq() const;
  void set_freq(double f);
  int get_sys_num() const;
  std::string get_short_name() const;
  std::string get_temp_dir() const;
  const std::string &get_xor_mask() const;
  std::shared_ptr<System> get_system() const;
  long get_current_source_id() const;
  void set_current_source_id(long src);

  // P25/DMR fields
  void set_phase2_tdma(bool m);
  bool get_phase2_tdma() const;
  void set_tdma_slot(int s);
  int get_tdma_slot() const;

  // Conventional (virtual for Call_conventional override)
  virtual void restart_call();
  virtual time_t get_start_time() const;
  virtual bool is_conventional() const { return false; }
  virtual double get_squelch_db() const;
  int get_freq_error() const;

  // Rust call ID for round-tripping through audio callbacks
  void set_rust_call_id(uint64_t id);
  uint64_t get_rust_call_id() const;

protected:
  static long call_counter;
  long call_num;
  long talkgroup;
  double curr_freq;
  int freq_error;
  long curr_src_id;
  bool phase2_tdma;
  int tdma_slot;

  std::chrono::system_clock::time_point start_time;

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
