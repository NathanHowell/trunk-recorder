#ifndef DMR_RECORDER_IMPL_H
#define DMR_RECORDER_IMPL_H

#define _USE_MATH_DEFINES

#include <cstdio>
#include <iostream>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <chrono>
#include <time.h>


#include <gnuradio/filter/firdes.h>
#include <gnuradio/hier_block2.h>
#include <gnuradio/io_signature.h>

#include <gnuradio/analog/pll_freqdet_cf.h>
#include <gnuradio/blocks/short_to_float.h>
#include <gnuradio/filter/fft_filter_fff.h>
#include <gnuradio/filter/pfb_arb_resampler_ccf.h>

#include <gnuradio/block.h>
#include <gnuradio/blocks/copy.h>

#include <gnuradio/analog/sig_source.h>
#include <gnuradio/blocks/multiply.h>
#include <gnuradio/blocks/multiply_const.h>
#include <gnuradio/filter/fir_filter_blk.h>

#include <gnuradio/analog/pll_freqdet_cf.h>
#include <gnuradio/block.h>
#include <gnuradio/filter/fft_filter_fff.h>
#include <gnuradio/filter/firdes.h>
#include <gnuradio/hier_block2.h>
#include <gnuradio/io_signature.h>
#include <gnuradio/msg_queue.h>

#include <gnuradio/filter/fft_filter_ccf.h>

#include <gnuradio/blocks/multiply_const.h>
#include <gnuradio/filter/fir_filter_blk.h>

#include <op25_repeater/costas_loop_cc.h>
#include <op25_repeater/fsk4_slicer_fb.h>
#include <op25_repeater/gardner_cc.h>
#include <op25_repeater/include/op25_repeater/frame_assembler.h>
#include <op25_repeater/include/op25_repeater/fsk4_demod_ff.h>
#include <op25_repeater/include/op25_repeater/p25_frame_assembler.h>

#include <gnuradio/blocks/file_sink.h>
#include <gnuradio/blocks/head.h>
#include <gnuradio/message.h>
#include <gnuradio/msg_queue.h>

#include "../gr_blocks/channelizer.h"
#include "../gr_blocks/plugin_wrapper_impl.h"
#include "../gr_blocks/selector.h"
#include "../gr_blocks/headless_sink.h"
#include "../gr_blocks/xlat_channelizer.h"
#include "../source.h"
#include "../call_conventional.h"
#include "dmr_recorder.h"
#include "recorder.h"

class dmr_recorder_impl : public dmr_recorder {

protected:
  void initialize(const std::shared_ptr<Source> &src);

public:
  dmr_recorder_impl(const std::shared_ptr<Source> &src, Recorder_Type type);
  void tune_offset(double f) override;
  void tune_freq(double f) override;
  bool start(const RecorderConfig &config) override;
  void stop() override;
  void clear() override;
  double get_freq() const override;
  int get_freq_error() const override;
  int get_num() const;
  double get_pwr() const override;
  std::vector<Transmission> get_transmission_list() override;
  std::vector<Transmission> get_transmission_list(int slot);
  void set_tdma(bool phase2);
  void switch_tdma(bool phase2);
  void set_tdma_slot(int slot) override;
  void set_source(long src) override;
  void set_system(const std::shared_ptr<System> &) override;
  std::chrono::duration<double> since_last_write() const override;
  void process_message_queues() override;
  void set_enabled(bool enabled) override;
  bool is_enabled() const override;
  bool is_active() const override;
  bool is_analog() const override;
  bool is_idle() const override;
  bool is_squelched() const override;
  long get_wav_hz() const override;
  long get_talkgroup() const override;
  RecorderState get_state() const override;
  void set_squelch_callback(std::function<void(bool, double)> cb) override;
  std::shared_ptr<Source> get_source();

  void plugin_callback_handler(int16_t *samples, int sampleCount);

protected:
  RecorderState state;
  std::chrono::steady_clock::time_point starttime;
  long talkgroup;
  std::string short_name;
  const Config &config;
  std::shared_ptr<Source> source;
  double chan_freq;
  double center_freq;
  double squelch_db;

  // gr::blocks::multiply_const_ss::sptr levels;
  // channelizer::sptr prefilter;
  xlat_channelizer::sptr prefilter;
  gr::op25_repeater::gardner_cc::sptr clock;
  gr::op25_repeater::costas_loop_cc::sptr costas;

private:
  int silence_frames;
  int tdma_slot;
  bool d_phase2_tdma;
  bool d_soft_vocoder;
  long input_rate;
  const int phase1_samples_per_symbol = 5;
  const double phase1_symbol_rate = 4800;

  gr::blocks::multiply_const_ff::sptr rescale;

  /* FSK4 Stuff */

  std::vector<float> baseband_noise_filter_taps;
  std::vector<float> sym_taps;
  gr::msg_queue::sptr tune_queue;

  gr::filter::fft_filter_fff::sptr noise_filter;
  gr::filter::fir_filter_fff::sptr sym_filter;

  gr::blocks::multiply_const_ff::sptr pll_amp;
  gr::analog::pll_freqdet_cf::sptr pll_freq_lock;
  gr::op25_repeater::fsk4_demod_ff::sptr fsk4_demod;
  gr::op25_repeater::fsk4_slicer_fb::sptr slicer;

  /* P25 Decoder */
  gr::op25_repeater::frame_assembler::sptr framer;
  gr::op25_repeater::p25_frame_assembler::sptr op25_frame_assembler;
  gr::msg_queue::sptr traffic_queue;
  gr::msg_queue::sptr rx_queue;

  gr::blocks::short_to_float::sptr converter_slot0;
  gr::blocks::short_to_float::sptr converter_slot1;
  gr::blocks::multiply_const_ff::sptr levels;
  gr::blocks::headless_sink::sptr wav_sink_slot0;
  gr::blocks::headless_sink::sptr wav_sink_slot1;
  gr::blocks::plugin_wrapper::sptr plugin_sink_slot0;
  gr::blocks::plugin_wrapper::sptr plugin_sink_slot1;
};

#endif // ifndef dmr_recorder_H
