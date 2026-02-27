#ifndef CONFIG_H
#define CONFIG_H
#include <boost/program_options.hpp>
#include <boost/property_tree/json_parser.hpp>
#include <boost/property_tree/ptree.hpp>
#include <boost/property_tree/xml_parser.hpp>

#include <boost/log/attributes/named_scope.hpp>
#include <boost/log/core.hpp>
#include <boost/log/expressions.hpp>
#include <boost/log/sinks/sync_frontend.hpp>
#include <boost/log/sinks/text_ostream_backend.hpp>
#include <boost/log/sources/logger.hpp>
#include <boost/log/support/date_time.hpp>
#include <boost/log/trivial.hpp>
#include <boost/log/utility/setup/common_attributes.hpp>
#include <boost/log/utility/setup/console.hpp>
#include <boost/log/utility/setup/file.hpp>

#include <gnuradio/top_block.h>

#include <fstream>
#include <regex>

#include "cmake.h"
#include "git.h"

#include "./global_structs.h"
#include "source.h"
#include "systems/system.h"

#include <json.hpp>

bool load_config(std::string config_file, Config &config, gr::top_block_sptr &tb, std::vector<Source *> &sources, std::vector<System *> &systems);
bool load_config_from_json(nlohmann::json &data, Config &config, gr::top_block_sptr &tb, std::vector<Source *> &sources, std::vector<System *> &systems);
bool load_config_from_string(const std::string &json_body, Config &config, gr::top_block_sptr &tb, std::vector<Source *> &sources, std::vector<System *> &systems);

#endif