
#include "p25_recorder_impl.h"
#include "../formatter.h"
#include "p25_recorder.h"
#include <boost/log/trivial.hpp>

p25_recorder_sptr make_p25_recorder(const std::shared_ptr<Source> &src, Recorder_Type type) {
  auto sptr = gnuradio::get_initial_sptr(new p25_recorder_impl(src, type));
  // shared_from_this() is now available — build the decode blocks and wire the graph.
  static_cast<p25_recorder_impl *>(sptr.get())->build_graph();
  return sptr;
}

p25_recorder_impl::p25_recorder_impl(const std::shared_ptr<Source> &src, Recorder_Type type)
    : gr::hier_block2("p25_recorder",
                      gr::io_signature::make(1, 1, sizeof(gr_complex)),
                      gr::io_signature::make(0, 0, sizeof(float))),
      Recorder(type),
      config(src->get_config()) {
  if (type == P25C) {
    conventional = true;
  } else {
    conventional = false;
  }
  initialize(src);
}

void p25_recorder_impl::initialize(const std::shared_ptr<Source> &src) {
  source = src;
  chan_freq = source->get_center();
  center_freq = source->get_center();
  d_soft_vocoder = config.soft_vocoder;
  input_rate = source->get_rate();
  qpsk_mod = true;
  silence_frames = source->get_silence_frames();
  squelch_db = 0;
  talkgroup = 0;
  d_phase2_tdma = false;
  rec_num = rec_counter++;

  state = REC_INACTIVE;

  starttime = std::chrono::steady_clock::now();

  prefilter = xlat_channelizer::make(input_rate, channelizer::phase1_samples_per_symbol, channelizer::phase1_symbol_rate, xlat_channelizer::channel_bandwidth, center_freq, conventional);

  modulation_selector = gr::blocks::selector::make(sizeof(gr_complex), 0, 0);
  qpsk_demod = make_p25_recorder_qpsk_demod();
  fsk4_demod = make_p25_recorder_fsk4_demod();
}

void p25_recorder_impl::build_graph() {
  auto self_recorder = std::dynamic_pointer_cast<Recorder>(shared_from_this());
  qpsk_p25_decode = make_p25_recorder_decode(self_recorder, config, silence_frames, d_soft_vocoder);
  fsk4_p25_decode = make_p25_recorder_decode(self_recorder, config, silence_frames, d_soft_vocoder);

  connect(self(), 0, prefilter, 0);
  connect(prefilter, 0, modulation_selector, 0);
  connect(modulation_selector, 0, fsk4_demod, 0);
  connect(fsk4_demod, 0, fsk4_p25_decode, 0);
  connect(modulation_selector, 1, qpsk_demod, 0);
  connect(qpsk_demod, 0, qpsk_p25_decode, 0);
}

void p25_recorder_impl::switch_tdma(bool phase2) {
  if (phase2) {
    d_phase2_tdma = true;
    prefilter->set_samples_per_symbol(phase2_samples_per_symbol);
  } else {
    d_phase2_tdma = false;
    prefilter->set_samples_per_symbol(phase1_samples_per_symbol);
  }

  if (qpsk_mod) {
    qpsk_p25_decode->switch_tdma(phase2);
    qpsk_demod->switch_tdma(phase2);
  }
}

void p25_recorder_impl::set_tdma(bool phase2) {
  if (phase2 != d_phase2_tdma) {
    switch_tdma(phase2);
  }
}

void p25_recorder_impl::reset_block(gr::basic_block_sptr block) {
  gr::block_detail_sptr detail;
  gr::block_sptr grblock = cast_to_block_sptr(block);
  detail = grblock->detail();
  detail->reset_nitem_counters();
}
void p25_recorder_impl::clear() {
  // This lead to weird SegFaults, but the goal was to clear out buffers inbetween transmissions.
  /*
  if (double_decim) {
    //reset_block(bandpass_filter);
    //reset_block(bfo);
  } else {
  //reset_block(lo);
  }
  reset_block(lowpass_filter);
  reset_block(mixer);

  if (arb_rate != 1.0) {
  reset_block(arb_resampler);
  }

  reset_block(cutoff_filter);
  reset_block(squelch);
  //reset_block(rms_agc); // RMS AGC cant be made into a basic block
  reset_block(fll_band_edge);
  reset_block(modulation_selector);


  //reset_block(qpsk_demod); // bad - Seg Faults
  //reset_block(qpsk_p25_decode); // bad - Seg Faults
  //reset_block(fsk4_demod); // bad - Seg Faults
  //reset_block(fsk4_p25_decode);  // bad - Seg Faults

  */
  qpsk_demod->reset();
  qpsk_p25_decode->reset();
  fsk4_demod->reset();
  fsk4_p25_decode->reset();
}

void p25_recorder_impl::autotune() {
  /*if (!qpsk_mod) {
    gr::message::sptr msg;
    msg = tune_queue->delete_head_nowait();

    if (msg != 0) {
      BOOST_LOG_TRIVIAL(info) << "p25_recorder.cc: Freq:\t" << format_freq(chan_freq) << "\t Tune: " << msg->arg1();

      // tune_offset(freq + (msg->arg1()*100));
      tune_queue->flush();
    }
  }*/
}

void p25_recorder_impl::tune_offset(double f) { prefilter->tune_offset(f); }
bool p25_recorder_impl::is_analog() const { return false; }
long p25_recorder_impl::get_wav_hz() const { return 8000; }
long p25_recorder_impl::get_talkgroup() const { return 0; }

int p25_recorder_impl::get_freq_error() const { // get frequency error from FLL and convert to Hz
  return prefilter->get_freq_error();
}

std::shared_ptr<Source> p25_recorder_impl::get_source() {
  return source;
}

int p25_recorder_impl::get_num() const {
  return rec_num;
}

std::chrono::duration<double> p25_recorder_impl::since_last_write() const {
  if (qpsk_mod) {
    return qpsk_p25_decode->since_last_write();
  } else {
    return fsk4_p25_decode->since_last_write();
  }
}

void p25_recorder_impl::process_message_queues() {
  if (qpsk_mod) {
    qpsk_p25_decode->check_message_queue();
  } else {
    fsk4_p25_decode->check_message_queue();
  }
}

RecorderState p25_recorder_impl::get_state() const {
  if (qpsk_mod) {
    return qpsk_p25_decode->get_state();
  } else {
    return fsk4_p25_decode->get_state();
  }
}

bool p25_recorder_impl::is_enabled() const {
  return source->is_selector_port_enabled(selector_port);
}

void p25_recorder_impl::set_enabled(bool enabled) {
  source->set_selector_port_enabled(selector_port, enabled);
}

bool p25_recorder_impl::is_active() const {
  if (state == REC_ACTIVE) {
    return true;
  } else {
    return false;
  }
}

bool p25_recorder_impl::is_squelched() const {
  if (state == REC_ACTIVE) {
    return prefilter->is_squelched();
  }
  return true;
}

double p25_recorder_impl::get_pwr() const {
  return prefilter->get_pwr();
}

void p25_recorder_impl::set_squelch_callback(std::function<void(bool, double)> cb) {
  prefilter->set_squelch_callback(std::move(cb));
}

bool p25_recorder_impl::is_idle() const {
  if (qpsk_mod) {
    if ((qpsk_p25_decode->get_state() == REC_IDLE) || (qpsk_p25_decode->get_state() == REC_STOPPED)) {
      return true;
    }
  } else {
    if ((fsk4_p25_decode->get_state() == REC_IDLE) || (fsk4_p25_decode->get_state() == REC_STOPPED)) {
      return true;
    }
  }
  return false;
}

double p25_recorder_impl::get_freq() const {
  return chan_freq;
}

void p25_recorder_impl::tune_freq(double f) {
  chan_freq = f;
  float freq = (center_freq - f);
  prefilter->tune_offset(freq);
}

void p25_recorder_impl::set_source(long src) {
  if (qpsk_mod) {
    return qpsk_p25_decode->set_source(src);
  } else {
    return fsk4_p25_decode->set_source(src);
  }
}

void p25_recorder_impl::set_system(const std::shared_ptr<System> &sys) {
  qpsk_p25_decode->set_system(sys);
  fsk4_p25_decode->set_system(sys);
}

std::vector<Transmission> p25_recorder_impl::get_transmission_list() {
  if (qpsk_mod) {
    return qpsk_p25_decode->get_transmission_list();
  } else {
    return fsk4_p25_decode->get_transmission_list();
  }
}

void p25_recorder_impl::stop() {
  if (state == REC_ACTIVE) {
    if (source->get_autotune_source()) {
      // Send last tuning measurements to autotune manager
      source->add_autotune_error_measurement(this->get_freq_error(), autotune_offset);
    }
    BOOST_LOG_TRIVIAL(info) << "\u001b[33mStopping P25 Recorder Num [" << rec_num << "]\u001b[0m\tTG: " << talkgroup << "\tFreq: " << chan_freq << "\tTDMA: " << d_phase2_tdma << "\tSlot: " << tdma_slot << "\tTuningErr: " << std::showpos << this->get_freq_error() << std::noshowpos << " Hz";

    state = REC_INACTIVE;
    set_enabled(false);

    clear();
    if (qpsk_mod) {
      qpsk_p25_decode->stop();
    } else {
      fsk4_p25_decode->stop();
    }
  } else {
    BOOST_LOG_TRIVIAL(error) << "p25_recorder.cc: Trying to Stop an Inactive Logger!!!";
  }
}

void p25_recorder_impl::set_tdma_slot(int slot) {
  if (qpsk_mod) {
    qpsk_p25_decode->set_tdma_slot(slot);
  } else {
    fsk4_p25_decode->set_tdma_slot(slot);
  }
  tdma_slot = slot;
}

bool p25_recorder_impl::start(const RecorderConfig &config) {
  if (state == REC_INACTIVE) {
    set_tdma(config.phase2_tdma);
    if (config.phase2_tdma) {
      if (!qpsk_mod) {
        BOOST_LOG_TRIVIAL(error) << "Error - Modulation is FSK4 but receiving Phase 2 call, this will not work";
        return false;
      }
      set_tdma_slot(config.tdma_slot);

      if (!config.xor_mask.empty()) {
        qpsk_p25_decode->set_xor_mask(config.xor_mask);
      } else {
        BOOST_LOG_TRIVIAL(info) << "Error - can't set XOR Mask for TDMA";
        return false;
      }
    } else {
      set_tdma_slot(0);
    }

    starttime = std::chrono::steady_clock::now();

    talkgroup = config.talkgroup;
    short_name = config.short_name;
    chan_freq = config.freq;
    rust_call_id = config.rust_call_id;

    autotune_offset = 0;
    if (source->get_autotune_source()) {
      autotune_offset = source->get_source_error();
    }

    int offset_amount = (center_freq - chan_freq + autotune_offset);

    prefilter->tune_offset(offset_amount);

    if (qpsk_mod) {
      modulation_selector->set_output_index(1);
      qpsk_p25_decode->start(config);
    } else {
      modulation_selector->set_output_index(0);
      fsk4_p25_decode->start(config);
    }
    state = REC_ACTIVE;

    squelch_db = config.squelch_db;
    if (!conventional) {
      set_enabled(true);
    }
    prefilter->set_squelch_db(squelch_db);

  } else {
    BOOST_LOG_TRIVIAL(error) << "p25_recorder.cc: Trying to Start an already Active Logger!!!";
    return false;
  }
  return true;
}

int Recorder::rec_counter = 0;
