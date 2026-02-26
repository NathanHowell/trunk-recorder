#ifndef PLUGIN_EVENT_SINK_H
#define PLUGIN_EVENT_SINK_H

#include "../event_sink.h"

class PluginEventSink : public EventSink {
public:
  void audio_callback(Call *call, Recorder *recorder,
                      int16_t *samples, int sampleCount) override;
  void poll_one() override;
  int signal(long unitId, const char *signaling_type,
             gr::blocks::SignalType sig_type, Call *call, System *system,
             Recorder *recorder) override;
  void trunk_message(std::vector<TrunkMessage> messages,
                     System *system) override;
  void call_start(Call *call) override;
  void conclude_call(Call *call, System *sys, Config config) override;
  void calls_active(std::vector<Call *> calls) override;
  void setup_recorder(Recorder *recorder) override;
  void setup_system(System *system) override;
  void setup_config(std::vector<Source *> sources,
                    std::vector<System *> systems) override;
  void system_rates(std::vector<System *> systems, float timeDiff) override;
  void unit_registration(System *system, long source_id) override;
  void unit_deregistration(System *system, long source_id) override;
  void unit_acknowledge_response(System *system, long source_id) override;
  void unit_group_affiliation(System *system, long source_id,
                              long talkgroup_num) override;
  void unit_data_grant(System *system, long source_id) override;
  void unit_answer_request(System *system, long source_id,
                           long talkgroup) override;
  void unit_location(System *system, long source_id,
                     long talkgroup_num) override;
};

#endif // PLUGIN_EVENT_SINK_H
