#ifndef MONITOR_SYSTEMS_H
#define MONITOR_SYSTEMS_H
#include <chrono>
#include <signal.h>
#include <stdlib.h>
#include <thread>

#include "./global_structs.h"
#include "call.h"
#include "config.h"
#include "event_sink.h"
#include "source.h"
#include "trunk_context.h"
#include "systems/p25_parser.h"
#include "systems/p25_trunking.h"
#include "systems/smartnet_parser.h"
#include "systems/system.h"
#include <gnuradio/top_block.h>

int monitor_messages(TrunkContext &ctx);
#endif