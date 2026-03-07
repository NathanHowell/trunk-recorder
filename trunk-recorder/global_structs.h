#ifndef GLOBAL_STRUCTS_H
#define GLOBAL_STRUCTS_H
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>
const int DB_UNSET = 999;

class EventSink;

struct Transmission {
  long source;
  long talkgroup;
  unsigned int slot;
  unsigned int color_code;
  long start_time;
  long stop_time;
  long sample_count;
  long spike_count;
  long error_count;
  double freq;
  char filename[255];
};

struct Config {
  std::string temp_dir;
  std::string debug_recorder_address;
  bool debug_recorder;
  int debug_recorder_port;
  bool soft_vocoder;
  std::shared_ptr<EventSink> event_sink;
};

enum SystemType {
  SYS_CONVENTIONAL,
  SYS_CONVENTIONAL_P25,
  SYS_CONVENTIONAL_DMR,
  SYS_CONVENTIONAL_SIGMF,
  SYS_SMARTNET,
  SYS_P25,
};

inline bool is_conventional(SystemType t) {
  return t == SYS_CONVENTIONAL || t == SYS_CONVENTIONAL_P25 ||
         t == SYS_CONVENTIONAL_DMR || t == SYS_CONVENTIONAL_SIGMF;
}

inline SystemType system_type_from_string(const std::string &s) {
  if (s == "conventional") return SYS_CONVENTIONAL;
  if (s == "conventionalP25") return SYS_CONVENTIONAL_P25;
  if (s == "conventionalDMR") return SYS_CONVENTIONAL_DMR;
  if (s == "conventionalSIGMF") return SYS_CONVENTIONAL_SIGMF;
  if (s == "smartnet") return SYS_SMARTNET;
  if (s == "p25") return SYS_P25;
  throw std::invalid_argument("Unknown system type: " + s);
}

inline const char* system_type_to_string(SystemType t) {
  switch (t) {
    case SYS_CONVENTIONAL: return "conventional";
    case SYS_CONVENTIONAL_P25: return "conventionalP25";
    case SYS_CONVENTIONAL_DMR: return "conventionalDMR";
    case SYS_CONVENTIONAL_SIGMF: return "conventionalSIGMF";
    case SYS_SMARTNET: return "smartnet";
    case SYS_P25: return "p25";
  }
  return "unknown";
}

enum Recorder_Type { DEBUG,
                      SIGMF,
                      SIGMFC,
                      ANALOG,
                      ANALOGC,
                      P25,
                      P25C,
                      DMR,
                      SMARTNET };

#endif
