#ifndef SIGMF_RECORDER_H
#define SIGMF_RECORDER_H

#define _USE_MATH_DEFINES

#include <gnuradio/hier_block2.h>

#include "../gr_blocks/freq_xlating_fft_filter.h"
#include "recorder.h"

class Source;
class sigmf_recorder;

typedef std::shared_ptr<sigmf_recorder> sigmf_recorder_sptr;

sigmf_recorder_sptr make_sigmf_recorder(const std::shared_ptr<Source> &src, Recorder_Type type);
#include "../source.h"

class sigmf_recorder : virtual public gr::hier_block2, virtual public Recorder {

public:
  sigmf_recorder(){};
  virtual ~sigmf_recorder(){};
};

#endif
