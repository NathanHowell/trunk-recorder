/* -*- c++ -*- */
/*
 * Headless audio sink for TR_HEADLESS builds.
 *
 * Replaces transmission_sink: tracks state and timing without
 * writing WAV files.  Updates d_last_write_time in work() so that
 * the call-timeout logic in manage_calls() works correctly.
 */

#include "headless_sink.h"

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
      d_state(AVAILABLE),
      d_last_write_time(std::chrono::steady_clock::now()),
      d_start_time(0),
      d_stop_time(0) {}

bool headless_sink::start_recording(Call * /*call*/) {
  d_state = IDLE;
  d_start_time = time(NULL);
  d_last_write_time = std::chrono::steady_clock::now();
  return true;
}

bool headless_sink::start_recording(Call *call, int /*slot*/) {
  return start_recording(call);
}

void headless_sink::stop_recording() {
  d_state = AVAILABLE;
  d_stop_time = time(NULL);
}

void headless_sink::set_source(long /*src*/) {
  // No-op: no file to tag with source ID.
}

State headless_sink::get_state() {
  return d_state;
}

time_t headless_sink::get_start_time() {
  return d_start_time;
}

time_t headless_sink::get_stop_time() {
  return d_stop_time;
}

std::chrono::time_point<std::chrono::steady_clock> headless_sink::get_last_write_time() {
  return d_last_write_time;
}

std::vector<Transmission> headless_sink::get_transmission_list() {
  return {};
}

double headless_sink::total_length_in_seconds() {
  return 0.0;
}

double headless_sink::length_in_seconds() {
  return 0.0;
}

int headless_sink::work(int noutput_items,
                        gr_vector_const_void_star & /*input_items*/,
                        gr_vector_void_star & /*output_items*/) {
  if (d_state == IDLE) {
    d_state = RECORDING;
  }

  if (d_state == RECORDING) {
    d_last_write_time = std::chrono::steady_clock::now();
    d_stop_time = time(NULL);
  }

  // Consume all samples (discard audio data).
  return noutput_items;
}

} /* namespace blocks */
} /* namespace gr */
