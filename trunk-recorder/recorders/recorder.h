#ifndef RECORDER_H
#define RECORDER_H

#include <chrono>
#include <functional>
#include <memory>
#include <string>
#include <vector>

#include "../global_structs.h"
#include "../recorder_config.h"
#include "../state.h"

class Source;
class System;

class Recorder {

public:
  struct DecimSettings {
    long decim;
    long decim2;
  };

  int rec_num;
  int rssi=0;
  static int rec_counter;
  std::string get_type_string();
  bool conventional;
  unsigned int selector_port;

  int get_selector_port() const { return selector_port;}
  void set_selector_port(unsigned int port) {selector_port = port;}
  Recorder(Recorder_Type  type);
  int get_num() const { return rec_num; };
  Recorder_Type get_type() const { return type; };

  bool is_conventional() const { return conventional; };

  virtual void tune_offset(double f) = 0;
  virtual void tune_freq(double f) = 0;
  virtual bool start(const RecorderConfig &config) = 0;
  virtual void stop() = 0;
  virtual void set_tdma_slot(int slot) = 0;
  virtual double get_freq() const = 0;
  virtual int get_freq_error() const = 0;
  virtual double get_pwr() const = 0;
  virtual std::vector<Transmission> get_transmission_list() = 0;
  virtual void set_source(long src) = 0;
  virtual long get_wav_hz() const = 0;
  virtual long get_talkgroup() const = 0;
  virtual RecorderState get_state() const = 0;
  virtual void set_enabled(bool enabled) = 0;
  virtual bool is_enabled() const = 0;
  virtual bool is_active() const = 0;
  virtual bool is_analog() const = 0;
  virtual bool is_idle() const = 0;
  virtual bool is_squelched() const = 0;
  virtual double get_current_length() const = 0;
  virtual std::chrono::duration<double> since_last_write() const = 0;
  virtual void clear() = 0;
  virtual void set_system(const std::shared_ptr<System> &) = 0;
  virtual void set_squelch_callback(std::function<void(bool, double)> cb) = 0;
  virtual void process_message_queues() = 0;

  uint64_t get_rust_call_id() const { return rust_call_id; }

protected:
  Recorder_Type  type;
  int autotune_offset = 0;
  uint64_t rust_call_id = 0;
};

typedef std::shared_ptr<Recorder> Recorder_sptr;

#endif
