#ifndef ANALOG_RECORDER_H
#define ANALOG_RECORDER_H

#include <cstdio>
#include <fstream>
#include <iostream>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <chrono>
#include <time.h>
#include <unistd.h>


#include <gnuradio/hier_block2.h>
#include <gnuradio/io_signature.h>

#include <gnuradio/blocks/float_to_short.h>

#include <gnuradio/block.h>
#include <gnuradio/blocks/copy.h>
#include <gnuradio/blocks/multiply_const.h>
#include <gnuradio/filter/fir_filter_blk.h>
#include <gnuradio/filter/fft_filter_ccf.h>
#include <gnuradio/filter/firdes.h>
#include <gnuradio/filter/iir_filter_ffd.h>

#include <gnuradio/analog/ctcss_squelch_ff.h>
#include <gnuradio/analog/pwr_squelch_ff.h>
#include <gnuradio/analog/quadrature_demod_cf.h>

#include <gnuradio/blocks/float_to_short.h>

#include <gnuradio/filter/pfb_arb_resampler_ccf.h>

class Source;
class analog_recorder;

#include "../gr_blocks/channelizer.h"
#include "../gr_blocks/decoder_wrapper.h"
#include "../gr_blocks/freq_xlating_fft_filter.h"
#include "../gr_blocks/plugin_wrapper.h"
#include "../gr_blocks/headless_sink.h"
#include "../gr_blocks/xlat_channelizer.h"
#include "../systems/system.h"
#include "../call_conventional.h"
#include "recorder.h"

typedef std::shared_ptr<analog_recorder> analog_recorder_sptr;

#include "../source.h"

analog_recorder_sptr make_analog_recorder(const std::shared_ptr<Source> &src, Recorder_Type type);
analog_recorder_sptr make_analog_recorder(const std::shared_ptr<Source> &src, Recorder_Type type, float tone_freq);
class analog_recorder : public gr::hier_block2, public Recorder {
  friend analog_recorder_sptr make_analog_recorder(const std::shared_ptr<Source> &src, Recorder_Type type);
  friend analog_recorder_sptr make_analog_recorder(const std::shared_ptr<Source> &src, Recorder_Type type, float tone_freq);

protected:
  analog_recorder(const std::shared_ptr<Source> &src, const std::shared_ptr<System> &system, Recorder_Type type, float tone_freq);

public:
  ~analog_recorder();
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
  double get_current_length() const override;
  std::chrono::duration<double> since_last_write() const override;
  void clear() override;
  void set_system(const std::shared_ptr<System> &) override;
  void set_squelch_callback(std::function<void(bool, double)> cb) override;
  void process_message_queues() override;

  std::shared_ptr<Source> get_source();
  int get_num();
  static bool logging;
  void decoder_callback_handler(long unitId, const char *signaling_type, gr::blocks::SignalType signal);
  void plugin_callback_handler(int16_t *samples, int sampleCount);
  double get_output_sample_rate();
  void set_tau(float tau);
  float get_tau() const;

private:
  double center_freq, chan_freq;
  long talkgroup;
  long input_rate;
  float tone_freq;
  double system_channel_rate;
  double initial_rate;
  float quad_gain;
  double wav_sample_rate;
  double squelch_db;
  std::chrono::steady_clock::time_point starttime;
  bool use_tone_squelch;

  RecorderState state;
  std::vector<float> channel_lpf_taps;
  std::vector<float> lpf_taps;
  std::vector<float> audio_resampler_taps;
  std::vector<float> sym_taps;
  std::vector<float> high_f_taps;
  std::vector<float> low_f_taps;
  /* De-emph IIR filter taps */
  std::vector<double> d_fftaps; /*! Feed forward taps. */
  std::vector<double> d_fbtaps; /*! Feed back taps. */
  float d_tau;                 /*! De-emphasis time constant. */

  const Config &config;
  std::shared_ptr<Source> source;
  std::shared_ptr<System> system;
  void calculate_iir_taps(float tau);

  /* GR blocks */
  // channelizer::sptr prefilter;
  xlat_channelizer::sptr prefilter;
  gr::filter::iir_filter_ffd::sptr deemph;
  gr::filter::fir_filter_fff::sptr sym_filter;
  gr::filter::fft_filter_ccf::sptr channel_lpf;

  gr::blocks::multiply_const_ff::sptr levels;
  gr::filter::pfb_arb_resampler_ccf::sptr arb_resampler;
  gr::filter::fir_filter_fff::sptr decim_audio;
  gr::filter::fir_filter_fff::sptr high_f;
  gr::filter::fir_filter_fff::sptr low_f;
  gr::analog::pwr_squelch_ff::sptr squelch_two;
  gr::analog::ctcss_squelch_ff::sptr tone_squelch;

  gr::analog::quadrature_demod_cf::sptr demod;
  gr::blocks::float_to_short::sptr converter;

  gr::blocks::headless_sink::sptr wav_sink;
  gr::blocks::decoder_wrapper::sptr decoder_sink;
  gr::blocks::plugin_wrapper::sptr plugin_sink;

  void setup_decoders_for_system(const std::shared_ptr<System> &system);
};

#endif // ifndef ANALOG_RECORDER_H
