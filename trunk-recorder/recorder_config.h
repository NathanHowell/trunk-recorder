#ifndef RECORDER_CONFIG_H
#define RECORDER_CONFIG_H

#include <cstdint>
#include <string>

/// POD struct passed to recorder->start() with all fields the recorder
/// needs for initialization.  Replaces the shared_ptr<Call> dependency
/// so recorders never need to query back into Call.
struct RecorderConfig {
  long talkgroup = 0;
  long call_num = 0;
  double freq = 0.0;
  std::string short_name;
  std::string temp_dir;
  bool phase2_tdma = false;
  int tdma_slot = 0;
  std::string xor_mask;
  double squelch_db = 0.0;
  double digital_levels = 0.0;
  uint64_t rust_call_id = 0;
};

#endif
