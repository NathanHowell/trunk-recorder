#ifndef SETUP_SYSTEMS_H
#define SETUP_SYSTEMS_H

#include <memory>
#include <stdlib.h>

#include <gnuradio/top_block.h>

#include "./global_structs.h"
#include "call.h"
#include "call_conventional.h"
#include "config.h"
#include "source.h"
#include "systems/system.h"

bool setup_conventional_channel(const std::shared_ptr<System> &system, double frequency, long channel_index, Config &config, gr::top_block_sptr &tb, std::vector<Source *> &sources, std::vector<Call *> &calls);
bool setup_conventional_system(const std::shared_ptr<System> &system, Config &config, gr::top_block_sptr &tb, std::vector<Source *> &sources, std::vector<Call *> &calls);
bool setup_systems(Config &config, gr::top_block_sptr &tb, std::vector<Source *> &sources, std::vector<std::shared_ptr<System>> &systems, std::vector<Call *> &calls);

#endif
