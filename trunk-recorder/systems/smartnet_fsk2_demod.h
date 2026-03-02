#ifndef SMARTNET_FSK2_DEMOD_H
#define SMARTNET_FSK2_DEMOD_H

#include <functional>
#include <gnuradio/analog/quadrature_demod_cf.h>
#include <gnuradio/block.h>
#include <gnuradio/hier_block2.h>
#include <gnuradio/io_signature.h>
#include <gnuradio/msg_queue.h>
#include <gnuradio/blocks/null_sink.h>

#include <gnuradio/filter/fir_filter_blk.h>

#include <op25_repeater/rmsagc_ff.h>
#include <op25_repeater/include/op25_repeater/fsk4_demod_ff.h>
#include <op25_repeater/include/op25_repeater/frame_assembler.h>
#include <gnuradio/digital/binary_slicer_fb.h>




class smartnet_fsk2_demod : public gr::hier_block2 {
    public:
  smartnet_fsk2_demod(gr::msg_queue::sptr queue);
  virtual ~smartnet_fsk2_demod();
  void reset();
  void set_msg_callback(std::function<void(gr::message::sptr)> cb);
    typedef std::shared_ptr<smartnet_fsk2_demod> sptr;

static sptr make(gr::msg_queue::sptr queue);


protected:
  virtual void initialize();



private:
  const int samples_per_symbol = 5;
  const double symbol_rate = 3600;
  gr::msg_queue::sptr rx_queue;
  gr::msg_queue::sptr tune_queue;
  gr::filter::fir_filter_fff::sptr sym_filter;
  gr::analog::quadrature_demod_cf::sptr fm_demod;
  gr::op25_repeater::rmsagc_ff::sptr baseband_amp;
  gr::op25_repeater::fsk4_demod_ff::sptr fsk4_demod;
  gr::digital::binary_slicer_fb::sptr slicer;
  gr::op25_repeater::frame_assembler::sptr framer;
  gr::blocks::null_sink::sptr null_sink1;
  gr::blocks::null_sink::sptr null_sink2; 
};
#endif