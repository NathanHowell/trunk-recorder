/* -*- c++ -*- */
/*
 * Headless audio sink for TR_HEADLESS builds.
 *
 * Replaces transmission_sink: tracks state, timing, and sample count
 * without writing WAV files.  Updates d_last_write_time in work() so
 * that the call-timeout logic in manage_calls() works correctly.
 * Builds a transmission list so call_concluder gets real duration.
 */

#include "headless_sink.h"

#include "../../trunk-recorder/recorder_config.h"

#include <cstring>
#include <gnuradio/io_signature.h>

namespace gr {
namespace blocks {

headless_sink::sptr
headless_sink::make(int n_channels, unsigned int sample_rate, int bits_per_sample) {
  return gnuradio::get_initial_sptr(new headless_sink(n_channels, sample_rate, bits_per_sample));
}

headless_sink::headless_sink(int n_channels, unsigned int sample_rate, int /*bits_per_sample*/)
    : sync_block("headless_sink",
                 io_signature::make(1, n_channels, sizeof(int16_t)),
                 io_signature::make(0, 0, 0)),
      d_sample_rate(sample_rate),
      d_state(REC_AVAILABLE),
      d_last_write_time(std::chrono::steady_clock::now()),
      d_start_time(),
      d_stop_time(std::chrono::steady_clock::now()),
      d_sample_count(0),
      d_talkgroup(0),
      d_freq(0.0) {}

bool headless_sink::start_recording(const RecorderConfig &config) {
  d_state = REC_IDLE;
  d_start_time = std::chrono::system_clock::now();
  d_stop_time = std::chrono::steady_clock::now();
  d_sample_count = 0;
  d_last_write_time = std::chrono::steady_clock::now();
  d_talkgroup = config.talkgroup;
  d_freq = config.freq;
  return true;
}

bool headless_sink::start_recording(const RecorderConfig &config, int /*slot*/) {
  return start_recording(config);
}

void headless_sink::stop_recording() {
  d_state = REC_AVAILABLE;
  d_stop_time = std::chrono::steady_clock::now();
}

void headless_sink::set_source(long /*src*/) {
  // No-op: no file to tag with source ID.
}

RecorderState headless_sink::get_state() {
  return d_state;
}

std::chrono::time_point<std::chrono::system_clock> headless_sink::get_start_time() {
  return d_start_time;
}

std::chrono::time_point<std::chrono::steady_clock> headless_sink::get_stop_time() {
  return d_stop_time;
}

std::chrono::time_point<std::chrono::steady_clock> headless_sink::get_last_write_time() {
  return d_last_write_time;
}

std::vector<Transmission> headless_sink::get_transmission_list() {
  if (d_sample_count == 0) {
    return {};
  }

  Transmission t;
  memset(&t, 0, sizeof(t));
  t.talkgroup = d_talkgroup;
  t.freq = d_freq;
  t.start_time = std::chrono::system_clock::to_time_t(d_start_time);
  t.stop_time = std::chrono::system_clock::to_time_t(std::chrono::system_clock::now());
  t.sample_count = d_sample_count.load();
  t.length = length_in_seconds();
  t.source = 0;
  t.slot = 0;
  t.color_code = 0;
  t.spike_count = 0;
  t.error_count = 0;
  t.filename[0] = '\0';

  return {t};
}

double headless_sink::length_in_seconds() {
  if (d_sample_rate == 0) {
    return 0.0;
  }
  return (double)d_sample_count / (double)d_sample_rate;
}

int headless_sink::work(int noutput_items,
                        gr_vector_const_void_star & /*input_items*/,
                        gr_vector_void_star & /*output_items*/) {
  if (d_state == REC_IDLE) {
    d_state = REC_RECORDING;
  }

  if (d_state == REC_RECORDING) {
    d_sample_count += noutput_items;
    auto now = std::chrono::steady_clock::now();
    d_last_write_time = now;
    d_stop_time = now;
  }

  // Consume all samples (discard audio data).
  return noutput_items;
}

} /* namespace blocks */
} /* namespace gr */
