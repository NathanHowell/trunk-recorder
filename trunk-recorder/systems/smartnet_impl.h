#ifndef SMARTNET_IMPL_H
#define SMARTNET_IMPL_H

#define _USE_MATH_DEFINES

#include <cstdio>
#include <functional>
#include <iostream>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#include <boost/log/trivial.hpp>

#include <gnuradio/hier_block2.h>
#include <gnuradio/io_signature.h>

#include <gnuradio/block.h>

#include <gnuradio/message.h>
#include <gnuradio/msg_queue.h>
#include <gnuradio/blocks/null_sink.h>

#include "../gr_blocks/xlat_channelizer.h"
#include "smartnet_fsk2_demod.h"
#include "trunking_decoder.h"

class smartnet_impl;



class smartnet_impl : public gr::hier_block2, public trunking_decoder {
    public:
        typedef std::shared_ptr<smartnet_impl> sptr;
        
    static sptr make(double f,
                                        double c,
                                        long s,
                                        gr::msg_queue::sptr queue,
                                        int sys_num);
  smartnet_impl(double f,
               double c,
               long s,
               gr::msg_queue::sptr queue,
               int sys_num);


  ~smartnet_impl();

  void set_center(double c);
  void set_rate(long s);
  void tune_freq(double f) override;
  double get_pwr() override;
  double get_freq() override;
  void enable();
  int get_freq_error() override;
  void finetune_control_freq(double f) override;
  void set_msg_callback(std::function<void(gr::message::sptr)> cb) override;
  int autotune_offset;

  // TrunkingDecoder interface
  int get_autotune_offset() const override { return autotune_offset; }
  void set_autotune_offset(int offset) override { autotune_offset = offset; }
  std::shared_ptr<gr::hier_block2> as_hier_block() override { return std::dynamic_pointer_cast<gr::hier_block2>(shared_from_this()); }

  gr::msg_queue::sptr rx_queue;

private:
  void initialize(double freq, double center, long s, gr::msg_queue::sptr queue, int sys_num);

  double center_freq, chan_freq;
  long input_rate;
  int sys_num;


  //channelizer::sptr prefilter;
  xlat_channelizer::sptr prefilter;

  smartnet_fsk2_demod::sptr fsk2_demod;

};

#endif // ifndef P25_TRUNKING_H
