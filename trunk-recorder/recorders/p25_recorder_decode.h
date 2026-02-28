#ifndef P25_RECORDER_DECODE_H
#define P25_RECORDER_DECODE_H

#include <json.hpp>
#include <gnuradio/block.h>
#include <gnuradio/block_detail.h>
#include <gnuradio/blocks/short_to_float.h>
#include <gnuradio/hier_block2.h>
#include <gnuradio/io_signature.h>
#include <gnuradio/msg_queue.h>

#include <op25_repeater/fsk4_slicer_fb.h>
#include <op25_repeater/costas_loop_cc.h>
#include <op25_repeater/gardner_cc.h>
#include <op25_repeater/include/op25_repeater/fsk4_demod_ff.h>
#include <op25_repeater/include/op25_repeater/p25_frame_assembler.h>
#include <op25_repeater/include/op25_repeater/rx_status.h>
#include <op25_repeater/vocoder.h>

#include <gnuradio/blocks/multiply_const.h>

#include "../gr_blocks/plugin_wrapper.h"
#include "../gr_blocks/headless_sink.h"
#include "recorder.h"

class p25_recorder_decode;

typedef std::shared_ptr<p25_recorder_decode> p25_recorder_decode_sptr;

p25_recorder_decode_sptr make_p25_recorder_decode(const std::shared_ptr<Recorder> &recorder, const Config &config, int silence_frames, bool d_soft_vocoder);

class p25_recorder_decode : public gr::hier_block2 {
  friend p25_recorder_decode_sptr make_p25_recorder_decode(const std::shared_ptr<Recorder> &recorder, const Config &config, int silence_frames, bool d_soft_vocoder);

protected:
  virtual void initialize(int silence_frames, bool d_soft_vocoder);
  std::shared_ptr<Recorder> d_recorder;
  const Config &d_config;
  std::shared_ptr<Call> d_call;
  gr::op25_repeater::p25_frame_assembler::sptr op25_frame_assembler;
  gr::msg_queue::sptr traffic_queue;
  gr::msg_queue::sptr rx_queue;
  gr::op25_repeater::fsk4_slicer_fb::sptr slicer;
  gr::blocks::short_to_float::sptr converter;
  gr::blocks::multiply_const_ss::sptr levels;
  gr::blocks::headless_sink::sptr wav_sink;
  gr::blocks::plugin_wrapper::sptr plugin_sink;

public:
  p25_recorder_decode(const std::shared_ptr<Recorder> &recorder, const Config &config);
  void set_tdma_slot(int slot);
  std::vector<Transmission> get_transmission_list();
  void set_source(long src);
  void set_xor_mask(const std::string &mask);
  void switch_tdma(bool phase2_tdma);
  void start(const std::shared_ptr<Call> &call);
  std::chrono::duration<double> since_last_write();
  void stop();
  void reset();
  void reset_block(gr::basic_block_sptr block); 
  int tdma_slot;
  bool delay_open;
  virtual ~p25_recorder_decode();
  double get_current_length();
  void plugin_callback_handler(int16_t *samples, int sampleCount);
  double get_output_sample_rate();
  RecorderState get_state();
  gr::op25_repeater::p25_frame_assembler::sptr get_transmission_sink();
  void check_message_queue();

private:
  void handle_alias_message(const nlohmann::json& j);
};
#endif