#ifndef GLOBAL_STRUCTS_H
#define GLOBAL_STRUCTS_H
#include <chrono>
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
  double length;
  char filename[255];
};

struct Config {
  std::string config_file;
  std::string temp_dir;
  std::string debug_recorder_address;
  std::string default_mode;
  bool new_call_from_update;
  bool debug_recorder;
  int debug_recorder_port;
  std::chrono::duration<double> call_timeout;
  bool console_log;
  std::string log_color;
  int control_message_warn_rate;
  int control_retune_limit;
  bool broadcast_signals;
  bool enable_audio_streaming;
  bool soft_vocoder;
  bool record_uu_v_calls;
  int frequency_format;
  std::shared_ptr<EventSink> event_sink;
};

struct Call_Source {
  long source;
  double position;
  bool emergency;
  std::string signal_system;
  std::string tag;
};

struct Call_Freq {
  double freq;
  long time;
  double position;
  double total_len;
  double error_count;
  double spike_count;
};

struct Call_Error {
  double position;
  double total_len;
  double error_count;
  double spike_count;
};

enum Call_Data_Status { INITIAL,
                        SUCCESS,
                        RETRY,
                        FAILED };
                  
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

struct Call_Data_t {
  long talkgroup;
  unsigned int color_code;
  std::vector<unsigned long> patched_talkgroups;
  long call_num;
  double freq;
  int freq_error;
  int source_num;
  int recorder_num;
  double signal;
  double noise;
  long start_time;
  long stop_time;
  long error_count;
  long spike_count;
  bool encrypted;
  bool emergency;
  int priority;
  bool mode;
  bool duplex;
  int min_transmissions_removed;

  int sys_num;
  std::string short_name;
  std::string audio_type;

  int tdma_slot;
  double length;
  bool phase2_tdma;

  std::vector<Call_Source> transmission_source_list;
  std::vector<Call_Error> transmission_error_list;
  std::vector<Transmission> transmission_list;

  Call_Data_Status status;
};

#endif
