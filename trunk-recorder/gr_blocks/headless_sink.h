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

struct RecorderConfig;

namespace gr {
namespace blocks {

class BLOCKS_API headless_sink : virtual public sync_block {
private:
  unsigned d_sample_rate;
  std::atomic<RecorderState> d_state;
  std::atomic<std::chrono::time_point<std::chrono::steady_clock>> d_last_write_time;
  std::chrono::time_point<std::chrono::system_clock> d_start_time;
  std::atomic<std::chrono::time_point<std::chrono::steady_clock>> d_stop_time;
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

  bool start_recording(const RecorderConfig &config);
  bool start_recording(const RecorderConfig &config, int slot);
  void stop_recording();

  void set_source(long src);

  RecorderState get_state();
  std::chrono::time_point<std::chrono::system_clock> get_start_time();
  std::chrono::time_point<std::chrono::steady_clock> get_stop_time();
  std::chrono::time_point<std::chrono::steady_clock> get_last_write_time();

  std::vector<Transmission> get_transmission_list();

  int work(int noutput_items,
           gr_vector_const_void_star &input_items,
           gr_vector_void_star &output_items) override;
};

} /* namespace blocks */
} /* namespace gr */

#endif /* INCLUDED_HEADLESS_SINK_H */
