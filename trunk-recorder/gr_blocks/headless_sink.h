/* -*- c++ -*- */
/*
 * Headless audio sink for TR_HEADLESS builds.
 *
 * Drop-in replacement for transmission_sink that provides the same
 * public API (state machine, timing, transmission list) without any
 * WAV file I/O.  Keeps the call-timeout logic working by tracking
 * d_last_write_time on every work() invocation.
 */

#ifndef INCLUDED_HEADLESS_SINK_H
#define INCLUDED_HEADLESS_SINK_H

#include <atomic>
#include <chrono>
#include <vector>

#include "../../trunk-recorder/global_structs.h"
#include "../../trunk-recorder/state.h"

#include <gnuradio/blocks/api.h>
#include <gnuradio/sync_block.h>

class Call;

namespace gr {
namespace blocks {

class BLOCKS_API headless_sink : virtual public sync_block {
private:
  unsigned d_sample_rate;
  std::atomic<State> d_state;
  std::atomic<std::chrono::time_point<std::chrono::steady_clock>> d_last_write_time;
  time_t d_start_time;
  std::atomic<time_t> d_stop_time;
  std::atomic<long> d_sample_count;
  long d_talkgroup;
  double d_freq;

public:
  typedef std::shared_ptr<headless_sink> sptr;

  static sptr make(int n_channels,
                   unsigned int sample_rate,
                   int bits_per_sample = 16);

  headless_sink(int n_channels,
                unsigned int sample_rate,
                int bits_per_sample);

  bool start_recording(const std::shared_ptr<Call> &call);
  bool start_recording(const std::shared_ptr<Call> &call, int slot);
  void stop_recording();

  void set_source(long src);

  State get_state();
  time_t get_start_time();
  time_t get_stop_time();
  std::chrono::time_point<std::chrono::steady_clock> get_last_write_time();

  std::vector<Transmission> get_transmission_list();
  double total_length_in_seconds();
  double length_in_seconds();

  int work(int noutput_items,
           gr_vector_const_void_star &input_items,
           gr_vector_void_star &output_items) override;
};

} /* namespace blocks */
} /* namespace gr */

#endif /* INCLUDED_HEADLESS_SINK_H */
