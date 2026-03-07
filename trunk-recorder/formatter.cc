#include "formatter.h"

boost::format format_freq(double f) {
  return boost::format("%e") % f;
}

boost::format FormatSamplingRate(float f) {
  return boost::format("%.0f") % f;
}

std::string format_state(RecorderState state) {
  std::stringstream ss;
  switch (state) {
    case REC_RECORDING: ss << Color::RED << "Recording"  << Color::RST; break;
    case REC_INACTIVE:  ss << Color::BLU << "Inactive"   << Color::RST; break;
    case REC_ACTIVE:    ss << Color::YEL << "Active"     << Color::RST; break;
    case REC_IDLE:      ss << "Idle"; break;
    case REC_STOPPED:   ss << Color::MAG << "Stopped"    << Color::RST; break;
    case REC_AVAILABLE: ss << Color::GRN << "Available"  << Color::RST; break;
    case REC_IGNORE:    ss << "Ignored"; break;
    default:            ss << "Unknown"; break;
  }
  return ss.str();
}
