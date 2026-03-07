#ifndef DMR_RECORDER_H
#define DMR_RECORDER_H

#define _USE_MATH_DEFINES

#include <gnuradio/hier_block2.h>

#include "../gr_blocks/plugin_wrapper_impl.h"
#include "../source.h"
#include "recorder.h"

class Source;
class dmr_recorder;

typedef std::shared_ptr<dmr_recorder> dmr_recorder_sptr;

dmr_recorder_sptr make_dmr_recorder(const std::shared_ptr<Source> &src, Recorder_Type type);

class dmr_recorder : virtual public gr::hier_block2, virtual public Recorder {

public:
  dmr_recorder(){};
  virtual ~dmr_recorder(){};

  // dmr-specific methods not in Recorder base
  virtual void set_tdma(bool phase2) = 0;
  virtual void switch_tdma(bool phase2) = 0;
  virtual std::vector<Transmission> get_transmission_list(int slot) = 0;
  virtual std::shared_ptr<Source> get_source() = 0;
};

#endif // ifndef dmr_recorder_H
