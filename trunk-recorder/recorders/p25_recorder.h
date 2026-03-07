#ifndef P25_RECORDER_H
#define P25_RECORDER_H

#define _USE_MATH_DEFINES

#include <gnuradio/hier_block2.h>

#include "recorder.h"

class Source;
class p25_recorder;

typedef std::shared_ptr<p25_recorder> p25_recorder_sptr;

p25_recorder_sptr make_p25_recorder(const std::shared_ptr<Source> &src, Recorder_Type type);
#include "../source.h"

class p25_recorder : virtual public gr::hier_block2, virtual public Recorder {
  static p25_recorder_sptr make_p25_recorder(const std::shared_ptr<Source> &src);

public:
  p25_recorder(){};
  virtual ~p25_recorder(){};

  // p25-specific methods not in Recorder base
  virtual void set_tdma(bool phase2) = 0;
  virtual void switch_tdma(bool phase2) = 0;
  virtual std::shared_ptr<Source> get_source() = 0;
  virtual void autotune() = 0;
};

#endif // ifndef P25_RECORDER_H
