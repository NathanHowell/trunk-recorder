#include "monitor_systems.h"

#include <boost/log/core.hpp>
#include <boost/log/trivial.hpp>
#include <boost/log/expressions.hpp>

void set_logging_level(const std::string &log_level) {
  boost::log::trivial::severity_level sev_level = boost::log::trivial::info;
  if (log_level == "trace") sev_level = boost::log::trivial::trace;
  else if (log_level == "debug") sev_level = boost::log::trivial::debug;
  else if (log_level == "info") sev_level = boost::log::trivial::info;
  else if (log_level == "warning") sev_level = boost::log::trivial::warning;
  else if (log_level == "error") sev_level = boost::log::trivial::error;
  else if (log_level == "fatal") sev_level = boost::log::trivial::fatal;
  boost::log::core::get()->set_filter(boost::log::trivial::severity >= sev_level);
}
