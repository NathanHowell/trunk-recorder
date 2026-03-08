#include "dmr_recorder_impl.h"

#include "../event_sink.h"

#include "../gr_blocks/plugin_wrapper_impl.h"
#include <boost/log/trivial.hpp>

dmr_recorder_sptr make_dmr_recorder(const std::shared_ptr<Source> &src, Recorder_Type type) {
  dmr_recorder *recorder = new dmr_recorder_impl(src, type);

  return gnuradio::get_initial_sptr(recorder);
}

dmr_recorder_impl::dmr_recorder_impl(const std::shared_ptr<Source> &src, Recorder_Type type)
    : gr::hier_block2("dmr_recorder",
                      gr::io_signature::make(1, 1, sizeof(gr_complex)),
                      gr::io_signature::make(0, 0, sizeof(float))),
      Recorder(type),
      config(src->get_config()) {
  conventional = true;
  initialize(src);
}

void dmr_recorder_impl::initialize(const std::shared_ptr<Source> &src) {
  source = src;
  chan_freq = source->get_center();
  center_freq = source->get_center();
  d_soft_vocoder = config.soft_vocoder;
  input_rate = source->get_rate();
  silence_frames = source->get_silence_frames();
  squelch_db = 0;

  talkgroup = 0;
  d_phase2_tdma = true;
  rec_num = rec_counter++;

  state = REC_INACTIVE;

  starttime = std::chrono::steady_clock::now();

  prefilter = xlat_channelizer::make(input_rate, channelizer::phase1_samples_per_symbol, channelizer::phase1_symbol_rate, xlat_channelizer::channel_bandwidth, center_freq, conventional);

  /* FSK4 Demod */
  const double phase1_channel_rate = phase1_symbol_rate * phase1_samples_per_symbol;
  const double pi = M_PI;

  // FSK4: Phase Loop Lock - can only be Phase 1, so locking at that rate.
  double freq_to_norm_radians = pi / (phase1_channel_rate / 2.0);
  double fc = 0.0;
  double fd = 600.0;
  double pll_demod_gain = 1.0 / (fd * freq_to_norm_radians);
  double samples_per_symbol = 5;
  pll_freq_lock = gr::analog::pll_freqdet_cf::make((phase1_symbol_rate / 2.0 * 1.2) * freq_to_norm_radians, (fc + (3 * fd * 1.9)) * freq_to_norm_radians, (fc + (-3 * fd * 1.9)) * freq_to_norm_radians);
  pll_amp = gr::blocks::multiply_const_ff::make(pll_demod_gain * 1.0);

  // FSK4: noise filter - can only be Phase 1, so locking at that rate.
  baseband_noise_filter_taps = gr::filter::firdes::low_pass_2(1.0, phase1_channel_rate, phase1_symbol_rate / 2.0 * 1.175, phase1_symbol_rate / 2.0 * 0.125, 20.0, gr::fft::window::WIN_KAISER, 6.76);

  noise_filter = gr::filter::fft_filter_fff::make(1.0, baseband_noise_filter_taps);

  // FSK4: Symbol Taps
  double symbol_decim = 1;

  for (int i = 0; i < samples_per_symbol; i++) {
    sym_taps.push_back(1.0 / samples_per_symbol);
  }
  sym_filter = gr::filter::fir_filter_fff::make(symbol_decim, sym_taps);

  // FSK4: FSK4 Demod - locked at Phase 1 rates, since it can only be Phase 1
  tune_queue = gr::msg_queue::make(20);
  fsk4_demod = gr::op25_repeater::fsk4_demod_ff::make(tune_queue, phase1_channel_rate, phase1_symbol_rate);

  /* P25 Decode */
  // OP25 Slicer
  const float l[] = {-2.0, 0.0, 2.0, 4.0};
  const int msgq_id = 0;
  const int debug = 0;
  std::vector<float> slices(l, l + sizeof(l) / sizeof(l[0]));
  slicer = gr::op25_repeater::fsk4_slicer_fb::make(msgq_id, debug, slices);
  wav_sink_slot0 = gr::blocks::headless_sink::make(1, 8000, 16);
  wav_sink_slot1 = gr::blocks::headless_sink::make(1, 8000, 16);

  // OP25 Frame Assembler
  traffic_queue = gr::msg_queue::make(2);
  rx_queue = gr::msg_queue::make(100);
  int verbosity = 0; // 10 = lots of debug messages

  framer = gr::op25_repeater::frame_assembler::make("file:///tmp/out1.raw", verbosity, 1, rx_queue, d_soft_vocoder);
  levels = gr::blocks::multiply_const_ff::make(1);
  plugin_sink_slot0 = gr::blocks::plugin_wrapper_impl::make(std::bind(&dmr_recorder_impl::plugin_callback_handler, this, std::placeholders::_1, std::placeholders::_2));
  plugin_sink_slot1 = gr::blocks::plugin_wrapper_impl::make(std::bind(&dmr_recorder_impl::plugin_callback_handler, this, std::placeholders::_1, std::placeholders::_2));

  connect(self(), 0, prefilter, 0);
  connect(prefilter, 0, pll_freq_lock, 0);
  connect(pll_freq_lock, 0, pll_amp, 0);
  connect(pll_amp, 0, noise_filter, 0);
  connect(noise_filter, 0, sym_filter, 0);
  connect(sym_filter, 0, fsk4_demod, 0);
  connect(fsk4_demod, 0, slicer, 0);
  connect(slicer, 0, framer, 0);
  connect(framer, 0, wav_sink_slot0, 0);
  connect(framer, 1, wav_sink_slot1, 0);

  connect(framer, 0, plugin_sink_slot0, 0);
  connect(framer, 1, plugin_sink_slot1, 0);
}

void dmr_recorder_impl::plugin_callback_handler(int16_t *samples, int sampleCount) {
  auto self = std::dynamic_pointer_cast<Recorder>(shared_from_this());
  config.event_sink->audio_callback(self, samples, sampleCount);
}

void dmr_recorder_impl::switch_tdma(bool phase2) {
}

void dmr_recorder_impl::set_tdma(bool phase2) {
  if (phase2 != d_phase2_tdma) {
    switch_tdma(phase2);
  }
}

void dmr_recorder_impl::tune_offset(double f) { prefilter->tune_offset(f); }
void dmr_recorder_impl::set_source(long) {}
void dmr_recorder_impl::set_system(const std::shared_ptr<System> &) {}

std::shared_ptr<Source> dmr_recorder_impl::get_source() {
  return source;
}

int dmr_recorder_impl::get_num() const {
  return rec_num;
}

std::chrono::duration<double> dmr_recorder_impl::since_last_write() const {
  return std::chrono::steady_clock::now() - wav_sink_slot0->get_stop_time();
}

RecorderState dmr_recorder_impl::get_state() const {
  return wav_sink_slot0->get_state();
}

void dmr_recorder_impl::set_enabled(bool enabled) {
  source->set_selector_port_enabled(selector_port, enabled);
}

double dmr_recorder_impl::get_pwr() const {
  return prefilter->get_pwr();
}

void dmr_recorder_impl::set_squelch_callback(std::function<void(bool, double)> cb) {
  prefilter->set_squelch_callback(std::move(cb));
}

int dmr_recorder_impl::get_freq_error() const { // get frequency error from FLL and convert to Hz
  return prefilter->get_freq_error();
}

void dmr_recorder_impl::tune_freq(double f) {
  chan_freq = f;
  float freq = (center_freq - f);
  prefilter->tune_offset(freq);
}

bool compareTransmissions(Transmission t1, Transmission t2) {
  return (t1.start_time < t2.start_time);
}

std::vector<Transmission> dmr_recorder_impl::get_transmission_list() {
  std::vector<Transmission> return_list = wav_sink_slot0->get_transmission_list();
  std::vector<Transmission> second_list = wav_sink_slot1->get_transmission_list();
  BOOST_LOG_TRIVIAL(info) << "Slot 0: " << return_list.size() << " Slot 1: " << second_list.size();
  return_list.insert(return_list.end(), second_list.begin(), second_list.end());
  BOOST_LOG_TRIVIAL(info) << "Combined: " << return_list.size();
  sort(return_list.begin(), return_list.end(), compareTransmissions);
  BOOST_LOG_TRIVIAL(info) << "Sorted: " << return_list.size();
  return return_list;
}

std::vector<Transmission> dmr_recorder_impl::get_transmission_list(int slot) {
  std::vector<Transmission> return_list;
  if (slot == 0) {
    return_list = wav_sink_slot0->get_transmission_list();
  } else {
    return_list = wav_sink_slot1->get_transmission_list();
  }
  BOOST_LOG_TRIVIAL(info) << "Slot " << slot << ": " << return_list.size();
  return return_list;
}

void dmr_recorder_impl::stop() {
  if (state == REC_ACTIVE) {
    state = REC_INACTIVE;
    set_enabled(false);
    wav_sink_slot0->stop_recording();
    wav_sink_slot1->stop_recording();
  } else {
    BOOST_LOG_TRIVIAL(error) << "dmr_recorder.cc: Trying to Stop an Inactive Logger!!!";
  }
}

void dmr_recorder_impl::flush_audio() {
  plugin_sink_slot0->flush();
  plugin_sink_slot1->flush();
}

bool dmr_recorder_impl::start(const RecorderConfig &config) {
  if (state == REC_INACTIVE) {
    tdma_slot = 0;

    starttime = std::chrono::steady_clock::now();

    talkgroup = config.talkgroup;
    short_name = config.short_name;
    chan_freq = config.freq;
    rust_call_id = config.rust_call_id;
    int offset_amount = (center_freq - chan_freq);

    prefilter->tune_offset(offset_amount);
    levels->set_k(config.digital_levels);
    wav_sink_slot0->start_recording(config, 0);
    wav_sink_slot1->start_recording(config, 1);
    state = REC_ACTIVE;

    squelch_db = config.squelch_db;
    if (!conventional) {
      set_enabled(true);
    }
    prefilter->set_squelch_db(squelch_db);

  } else {
    BOOST_LOG_TRIVIAL(error) << "dmr_recorder.cc: Trying to Start an already Active Logger!!!";
    return false;
  }
  return true;
}

std::vector<gr::block_sptr> dmr_recorder_impl::get_metric_blocks() const {
  std::vector<gr::block_sptr> blocks;
  if (prefilter) {
    auto inner = prefilter->get_metric_blocks();
    blocks.insert(blocks.end(), inner.begin(), inner.end());
  }
  if (clock) blocks.push_back(clock);
  if (costas) blocks.push_back(costas);
  if (fsk4_demod) blocks.push_back(fsk4_demod);
  return blocks;
}
