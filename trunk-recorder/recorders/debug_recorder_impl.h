#ifndef DEBUG_RECORDER_IMPL_H
#define DEBUG_RECORDER_IMPL_H

#define _USE_MATH_DEFINES

#include <cstdio>
#include <iostream>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <chrono>
#include <time.h>

#if GNURADIO_VERSION < 0x030a00
#include <gnuradio/blocks/udp_sink.h>
#else
#include <gnuradio/network/udp_sink.h>
#endif

#include <gnuradio/hier_block2.h>
#include <gnuradio/io_signature.h>

#include <gnuradio/analog/feedforward_agc_cc.h>
#include <gnuradio/analog/pll_freqdet_cf.h>
#include <gnuradio/digital/diff_phasor_cc.h>
#include <gnuradio/filter/firdes.h>
#include <gnuradio/filter/pfb_arb_resampler_ccf.h>

#include <gnuradio/analog/sig_source.h>
#include <gnuradio/blocks/multiply.h>
#include <gnuradio/blocks/multiply_const.h>
#include <gnuradio/filter/fir_filter_blk.h>

#include <gnuradio/block.h>
#include <gnuradio/blocks/complex_to_arg.h>
#include <gnuradio/blocks/copy.h>
#include <gnuradio/blocks/short_to_float.h>

#include <op25_repeater/fsk4_slicer_fb.h>
#include <op25_repeater/costas_loop_cc.h>
#include <op25_repeater/gardner_cc.h>
#include <op25_repeater/include/op25_repeater/fsk4_demod_ff.h>
#include <op25_repeater/include/op25_repeater/p25_frame_assembler.h>
#include <op25_repeater/include/op25_repeater/rx_status.h>
#include <op25_repeater/vocoder.h>

#include <gnuradio/blocks/file_sink.h>
#include <gnuradio/blocks/head.h>
#include <gnuradio/message.h>
#include <gnuradio/msg_queue.h>

#include "../gr_blocks/freq_xlating_fft_filter.h"
#include "../source.h"
#include "debug_recorder.h"
#include "recorder.h"

class Source;
class debug_recorder;

typedef std::shared_ptr<debug_recorder> debug_recorder_sptr;

class debug_recorder_impl : public debug_recorder {

public:
  debug_recorder_impl(const std::shared_ptr<Source> &src, std::string address, int port);

  // Recorder pure virtual overrides
  void tune_offset(double f) override;
  void tune_freq(double f) override;
  bool start(const RecorderConfig &config) override;
  void stop() override;
  void set_tdma_slot(int slot) override;
  double get_freq() const override;
  int get_freq_error() const override;
  double get_pwr() const override;
  std::vector<Transmission> get_transmission_list() override;
  void set_source(long src) override;

  long get_wav_hz() const override;
  long get_talkgroup() const override;
  RecorderState get_state() const override;
  void set_enabled(bool enabled) override;
  bool is_enabled() const override;
  bool is_active() const override;
  bool is_analog() const override;
  bool is_idle() const override;
  bool is_squelched() const override;
  std::chrono::duration<double> since_last_write() const override;
  void clear() override;
  void set_system(const std::shared_ptr<System> &) override;
  void set_squelch_callback(std::function<void(bool, double)> cb) override;
  void process_message_queues() override;

  // debug_recorder pure virtual overrides
  int get_num() const;
  std::shared_ptr<Source> get_source() override;
  void initialize_prefilter() override;
  DecimSettings get_decim(long speed) override;
  void generate_arb_taps() override;

private:
  double chan_freq;
  double center_freq;
  long talkgroup;
  std::chrono::steady_clock::time_point starttime;

  const Config &config;
  std::shared_ptr<Source> source;

  // int num;
  RecorderState state;

  double system_channel_rate;
  double arb_rate;
  double samples_per_symbol;
  double symbol_rate;

  long decim;
  double resampled_rate;
  bool double_decim;
  long if1;
  long if2;
  long input_rate;
  const int phase1_samples_per_symbol = 5;
  const double phase1_symbol_rate = 4800;

  std::vector<float> arb_taps;
  std::vector<float> sym_taps;
  std::vector<float> baseband_noise_filter_taps;
  std::vector<gr_complex> bandpass_filter_coeffs;
  std::vector<float> lowpass_filter_coeffs;
  std::vector<float> cutoff_filter_coeffs;

  gr::filter::fft_filter_ccc::sptr bandpass_filter;
  gr::filter::fft_filter_ccf::sptr lowpass_filter;
  gr::filter::fft_filter_ccf::sptr cutoff_filter;

  gr::blocks::copy::sptr valve;
  gr::analog::sig_source_c::sptr lo;
  gr::analog::sig_source_c::sptr bfo;
  gr::blocks::multiply_cc::sptr mixer;
#if GNURADIO_VERSION >= 0x030a00
  gr::network::udp_sink::sptr udp_sink;
#else
  gr::blocks::udp_sink::sptr udp_sink;
#endif
  gr::filter::pfb_arb_resampler_ccf::sptr arb_resampler;
};

#endif
