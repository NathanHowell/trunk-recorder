
#include "call_conventional.h"
#include "recorder_config.h"
#include "recorders/recorder.h"

Call_conventional::Call_conventional(const std::shared_ptr<System> &s) : Call(s) {}

void Call_conventional::restart_call(const RecorderConfig &cfg) {
  debug_recording = false;
  auto rec = recorder.lock();
  if (rec) {
    rec->start(cfg);
  }
}
