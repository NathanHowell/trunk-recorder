#include "plugin_event_sink.h"
#include "plugin_manager.h"
#include "../call_concluder/call_concluder.h"

void PluginEventSink::poll_one() {
  plugman_poll_one();
}

int PluginEventSink::signal(long unitId, const char *signaling_type,
                            gr::blocks::SignalType sig_type, Call *call,
                            System *system, Recorder *recorder) {
  return plugman_signal(unitId, signaling_type, sig_type, call, system,
                        recorder);
}

void PluginEventSink::trunk_message(std::vector<TrunkMessage> messages,
                                    System *system) {
  plugman_trunk_message(messages, system);
}

void PluginEventSink::call_start(Call *call) {
  plugman_call_start(call);
}

void PluginEventSink::conclude_call(Call *call, System *sys, Config config) {
  Call_Concluder::conclude_call(call, sys, config);
}

void PluginEventSink::calls_active(std::vector<Call *> calls) {
  plugman_calls_active(calls);
}

void PluginEventSink::setup_recorder(Recorder *recorder) {
  plugman_setup_recorder(recorder);
}

void PluginEventSink::setup_system(System *system) {
  plugman_setup_system(system);
}

void PluginEventSink::setup_config(std::vector<Source *> sources,
                                   std::vector<System *> systems) {
  plugman_setup_config(sources, systems);
}

void PluginEventSink::system_rates(std::vector<System *> systems,
                                   float timeDiff) {
  plugman_system_rates(systems, timeDiff);
}

void PluginEventSink::unit_registration(System *system, long source_id) {
  plugman_unit_registration(system, source_id);
}

void PluginEventSink::unit_deregistration(System *system, long source_id) {
  plugman_unit_deregistration(system, source_id);
}

void PluginEventSink::unit_acknowledge_response(System *system,
                                                long source_id) {
  plugman_unit_acknowledge_response(system, source_id);
}

void PluginEventSink::unit_group_affiliation(System *system, long source_id,
                                             long talkgroup_num) {
  plugman_unit_group_affiliation(system, source_id, talkgroup_num);
}

void PluginEventSink::unit_data_grant(System *system, long source_id) {
  plugman_unit_data_grant(system, source_id);
}

void PluginEventSink::unit_answer_request(System *system, long source_id,
                                          long talkgroup) {
  plugman_unit_answer_request(system, source_id, talkgroup);
}

void PluginEventSink::unit_location(System *system, long source_id,
                                    long talkgroup_num) {
  plugman_unit_location(system, source_id, talkgroup_num);
}
