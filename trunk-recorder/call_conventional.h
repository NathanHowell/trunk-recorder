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
  void restart_call(const RecorderConfig &cfg) override;
  void set_recorder(const std::shared_ptr<Recorder> &r) override;
private:
  double squelch_db;
  bool signal_detection;
  long talkgroup;
  double freq;
};

#endif
