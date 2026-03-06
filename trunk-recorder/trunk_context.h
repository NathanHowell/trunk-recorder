#ifndef TRUNK_CONTEXT_H
#define TRUNK_CONTEXT_H

#include <memory>
#include <vector>

#include <gnuradio/top_block.h>

#include "global_structs.h"

class Source;
class System;

struct TrunkContext {
  std::vector<std::shared_ptr<Source>> sources;
  std::vector<std::shared_ptr<System>> systems;
  gr::top_block_sptr tb;
  Config config;
};

#endif // TRUNK_CONTEXT_H
