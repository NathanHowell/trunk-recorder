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
  // static Call * make(long t, double f, const std::shared_ptr<System> &s, Config c);
  static std::shared_ptr<Call> make(TrunkMessage message, const std::shared_ptr<System> &s, Config c);
  virtual ~Call(){};
  virtual long get_call_num() = 0;
  virtual void restart_call() = 0;
  virtual void conclude_call() = 0;
  virtual void set_sigmf_recorder(const std::shared_ptr<Recorder> &r) = 0;
  virtual std::shared_ptr<Recorder> get_sigmf_recorder() = 0;
  virtual void set_debug_recorder(const std::shared_ptr<Recorder> &r) = 0;
  virtual std::shared_ptr<Recorder> get_debug_recorder() = 0;
  virtual void set_recorder(const std::shared_ptr<Recorder> &r) = 0;
  virtual std::shared_ptr<Recorder> get_recorder() = 0;
  virtual double get_freq() = 0;
  virtual int get_sys_num() = 0;
  virtual std::string get_short_name() = 0;
  virtual std::string get_temp_dir() = 0;
  virtual void set_freq(double f) = 0;
  virtual long get_talkgroup() = 0;

  virtual bool update(TrunkMessage message) = 0;
  virtual int get_idle_count() = 0;
  virtual void increase_idle_count() = 0;
  virtual void reset_idle_count() = 0;
  virtual std::chrono::duration<double> since_last_update() = 0;
  virtual std::chrono::duration<double> elapsed() = 0;

  virtual double get_current_length() = 0;
  virtual void set_debug_recording(bool m) = 0;
  virtual bool get_debug_recording() = 0;
  virtual void set_sigmf_recording(bool m) = 0;
  virtual bool get_sigmf_recording() = 0;
  virtual void set_state(CallState s) = 0;
  virtual CallState get_state() = 0;
  virtual void set_monitoring_state(MonitoringState s) = 0;
  virtual MonitoringState get_monitoring_state() = 0;
  virtual void set_phase2_tdma(bool m) = 0;
  virtual bool get_phase2_tdma() = 0;
  virtual void set_tdma_slot(int s) = 0;
  virtual int get_tdma_slot() = 0;
  virtual bool get_is_analog() = 0;
  virtual void set_is_analog(bool a) = 0;
  virtual const std::string& get_xor_mask() = 0;
  virtual time_t get_start_time() = 0;
  virtual bool is_conventional() = 0;
  virtual void set_encrypted(bool m) = 0;
  virtual bool get_encrypted() = 0;
  virtual void set_emergency(bool m) = 0;
  virtual bool get_emergency() = 0;
  virtual int get_priority() = 0;
  virtual bool get_mode() = 0;
  virtual bool get_duplex() = 0;
  virtual double get_signal() = 0;
  virtual double get_noise() = 0;
  virtual int get_freq_error() = 0;
  virtual void set_signal(double s) = 0;
  virtual void set_noise(double n) = 0;
  virtual SystemType get_system_type() = 0;
  virtual long get_current_source_id() = 0;
  virtual void set_current_source_id(long src) = 0;
  virtual void set_last_update() = 0;
  virtual bool get_conversation_mode() = 0;
  virtual std::shared_ptr<System> get_system() = 0;
  virtual std::vector<Transmission> get_transmissions() = 0;
};

#endif
