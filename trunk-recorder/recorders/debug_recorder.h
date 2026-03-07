#ifndef DEBUG_RECORDER_H
#define DEBUG_RECORDER_H

#define _USE_MATH_DEFINES

#include <cstdio>
#include <iostream>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#if GNURADIO_VERSION < 0x030a00
#include <gnuradio/blocks/udp_sink.h>
#else
#include <gnuradio/network/udp_sink.h>
#endif

#include <gnuradio/hier_block2.h>
#include <gnuradio/io_signature.h>

#include "../gr_blocks/freq_xlating_fft_filter.h"
#include "recorder.h"

class Source;
class debug_recorder;

typedef std::shared_ptr<debug_recorder> debug_recorder_sptr;

debug_recorder_sptr make_debug_recorder(const std::shared_ptr<Source> &src, std::string address, int port);
#include "../source.h"

class debug_recorder : virtual public gr::hier_block2, virtual public Recorder {
  static debug_recorder_sptr make_debug_recorder(const std::shared_ptr<Source> &src, std::string address, int port);

public:
  debug_recorder(){};
  virtual ~debug_recorder(){};

  // debug-specific methods not in Recorder base
  virtual std::shared_ptr<Source> get_source() = 0;
  virtual void initialize_prefilter() = 0;
  virtual DecimSettings get_decim(long speed) = 0;
  virtual void generate_arb_taps() = 0;
};

#endif
