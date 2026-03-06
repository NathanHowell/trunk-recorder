#ifndef CALL_CONVENTIONAL_H
#define CALL_CONVENTIONAL_H
#include "global_structs.h"
class System;
class Recorder;

#include "call.h"
#include <string>

class Call_conventional : public Call {
public:
  Call_conventional(long t, double f, const std::shared_ptr<System> &s, Config c, double squelch_db, bool signal_detection);
  time_t get_start_time() const override;
  bool is_conventional() const override { return true; }
  void restart_call() override;
  void set_recorder(const std::shared_ptr<Recorder> &r) override;
  double get_squelch_db() const;
  bool get_signal_detection() const;
private:
  double squelch_db;
  bool signal_detection;
};

#endif
