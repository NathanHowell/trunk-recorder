#ifndef TRUNKING_DECODER_H
#define TRUNKING_DECODER_H

#include <functional>
#include <memory>

#include <gnuradio/hier_block2.h>
#include <gnuradio/message.h>

/// Common interface for trunking control channel decoders (P25 and Smartnet).
/// Both decoder types are gr::hier_block2 subclasses that also implement this interface.
class trunking_decoder {
public:
  virtual ~trunking_decoder() = default;

  virtual void tune_freq(double f) = 0;
  virtual double get_freq() = 0;
  virtual double get_pwr() = 0;
  virtual int get_freq_error() = 0;
  virtual void finetune_control_freq(double f) = 0;
  virtual void set_msg_callback(std::function<void(gr::message::sptr)> cb) = 0;

  virtual int get_autotune_offset() const = 0;
  virtual void set_autotune_offset(int offset) = 0;

  /// Return this object as a hier_block2 for GNU Radio graph connections.
  virtual std::shared_ptr<gr::hier_block2> as_hier_block() = 0;
};

#endif // TRUNKING_DECODER_H
