#include "recorder.h"

Recorder::Recorder(Recorder_Type type) {
  this->type = type;
}


std::string Recorder::get_type_string() {
  switch(type) {
    case DEBUG:
      return "Debug";
    case SIGMF:
      return "SIGMF";
    case ANALOGC:
      return "AnalogC";
    case ANALOG:
      return "Analog";
    case P25:
      return "P25";
    case P25C:
      return "P25C";
    case DMR:
      return "DMR";
    default:
      return "Unknown";
  }
}