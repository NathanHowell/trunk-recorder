#ifndef EVENT_SINK_H
#define EVENT_SINK_H

#include <cstdint>
#include <memory>
#include <vector>

#include "global_structs.h"
#include "gr_blocks/decoder_wrapper.h"
#include "systems/parser.h"

class Call;
class System;
class Source;
class Recorder;

class EventSink {
public:
  virtual ~EventSink() = default;

  virtual void audio_callback(Call *call, const std::shared_ptr<Recorder> &recorder,
                              int16_t *samples, int sampleCount) = 0;
  virtual void poll_one() = 0;
  virtual int signal(long unitId, const char *signaling_type,
                     gr::blocks::SignalType sig_type, Call *call,
                     const std::shared_ptr<System> &system, const std::shared_ptr<Recorder> &recorder) = 0;
  virtual void trunk_message(std::vector<TrunkMessage> messages,
                             const std::shared_ptr<System> &system) = 0;
  virtual void call_start(Call *call) = 0;
  virtual void conclude_call(Call *call, const std::shared_ptr<System> &sys, Config config) = 0;
  virtual void calls_active(std::vector<Call *> calls) = 0;
  virtual void setup_recorder(const std::shared_ptr<Recorder> &recorder) = 0;
  virtual void setup_system(const std::shared_ptr<System> &system) = 0;
  virtual void setup_config(std::vector<Source *> sources,
                            std::vector<std::shared_ptr<System>> systems) = 0;
  virtual void system_rates(std::vector<std::shared_ptr<System>> systems, float timeDiff) = 0;
  virtual void unit_registration(const std::shared_ptr<System> &system, long source_id) = 0;
  virtual void unit_deregistration(const std::shared_ptr<System> &system, long source_id) = 0;
  virtual void unit_acknowledge_response(const std::shared_ptr<System> &system, long source_id) = 0;
  virtual void unit_group_affiliation(const std::shared_ptr<System> &system, long source_id,
                                      long talkgroup_num) = 0;
  virtual void unit_data_grant(const std::shared_ptr<System> &system, long source_id) = 0;
  virtual void unit_answer_request(const std::shared_ptr<System> &system, long source_id,
                                   long talkgroup) = 0;
  virtual void unit_location(const std::shared_ptr<System> &system, long source_id,
                             long talkgroup_num) = 0;
};

#endif // EVENT_SINK_H
