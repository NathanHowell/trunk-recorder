#ifndef TRUNK_CONTEXT_H
#define TRUNK_CONTEXT_H

#include <csignal>
#include <cstdlib>
#include <vector>

#include <gnuradio/top_block.h>

#include "global_structs.h"

class Source;
class System;
class Call;

struct TrunkContext {
  std::vector<Source *> sources;
  std::vector<System *> systems;
  std::vector<Call *> calls;
  gr::top_block_sptr tb;
  Config config;
  volatile sig_atomic_t exit_flag = 0;
  int exit_code = EXIT_SUCCESS;
};

#endif // TRUNK_CONTEXT_H
