#include "call_concluder.h"
#include "../plugin_manager/plugin_manager.h"
#include <cmath>

Call_Data_t Call_Concluder::create_call_data(Call *call, System *sys, Config config) {
  Call_Data_t call_info;
  double total_length = 0;

  call_info.status = INITIAL;
  call_info.error_count = 0;
  call_info.spike_count = 0;
  call_info.start_time = call->get_start_time();
  call_info.stop_time = call->get_stop_time();
  call_info.length = 0;
  call_info.freq = call->get_freq();
  call_info.freq_error = call->get_freq_error();
  call_info.signal = call->get_signal();
  call_info.noise = call->get_noise();
  if (call->get_recorder()) {
    call_info.recorder_num = call->get_recorder()->get_num();
    call_info.source_num = call->get_recorder()->get_source()->get_num();
  } else {
    call_info.recorder_num = -1;
    call_info.source_num = -1;
  }
  call_info.encrypted = call->get_encrypted();
  call_info.emergency = call->get_emergency();
  call_info.priority = call->get_priority();
  call_info.mode = call->get_mode();
  call_info.duplex = call->get_duplex();
  call_info.tdma_slot = call->get_tdma_slot();
  call_info.phase2_tdma = call->get_phase2_tdma();
  call_info.transmission_list = call->get_transmissions();
  call_info.sys_num = sys->get_sys_num();
  call_info.short_name = sys->get_short_name();
  call_info.call_num = call->get_call_num();
  call_info.talkgroup = call->get_talkgroup();
  call_info.talkgroup_display = call->get_talkgroup_display();
  call_info.patched_talkgroups = sys->get_talkgroup_patch(call_info.talkgroup);
  call_info.min_transmissions_removed = 0;
  call_info.color_code = 0;

  std::string loghdr = log_header( call_info.short_name, call_info.call_num, call_info.talkgroup_display , call_info.freq);

  if (call->get_is_analog()) {
    call_info.audio_type = "analog";
  } else if (call->get_phase2_tdma()) {
    call_info.audio_type = "digital tdma";
  } else {
    call_info.audio_type = "digital";
  }

  if (call_info.encrypted) {
    BOOST_LOG_TRIVIAL(info) << loghdr << Color::RED << "Encrypted call" << Color::RST << " - No audio generated";
  }

  // loop through the transmission list, pull in things to fill in totals for call_info
  for (std::vector<Transmission>::iterator it = call_info.transmission_list.begin(); it != call_info.transmission_list.end();) {
    Transmission t = *it;

    if (t.length < sys->get_min_tx_duration() && !call_info.encrypted) {
      BOOST_LOG_TRIVIAL(info) << loghdr << "Removing transmission less than " << sys->get_min_tx_duration() << " seconds. Actual length: " << t.length << ".";
      call_info.min_transmissions_removed++;
      it = call_info.transmission_list.erase(it);
      continue;
    }

    std::string tag = sys->find_unit_tag(t.source);
    std::string display_tag = "";
    if (tag != "") {
      display_tag = " (\033[0;34m" + tag + "\033[0m)";
    }

    std::stringstream transmission_info;
    transmission_info << loghdr << "- Transmission src: " << t.source << display_tag << " pos: " << format_time(total_length) << " length: " << format_time(t.length);

    if (t.error_count < 1) {
      BOOST_LOG_TRIVIAL(info) << transmission_info.str();
    } else {
      BOOST_LOG_TRIVIAL(info) << transmission_info.str() << "\033[0;31m errors: " << t.error_count << " spikes: " << t.spike_count << "\033[0m";
    }

    if (it == call_info.transmission_list.begin()) {
      call_info.start_time = t.start_time;
    }

    if (std::next(it) == call_info.transmission_list.end()) {
      call_info.stop_time = t.stop_time;
    }

    if (call_info.color_code == -1 && t.color_code != -1) {
      call_info.color_code = t.color_code;
      if (call_info.color_code != t.color_code) {
        BOOST_LOG_TRIVIAL(warning) << loghdr << "Call has multiple Color Codes - previous Transmission Color Code: " << call_info.color_code << " current Transmission Color Code: " << t.color_code;
      }
    }

    if (call_info.talkgroup != t.talkgroup) {
      BOOST_LOG_TRIVIAL(warning) << loghdr << "Transmission has a different Talkgroup than Call - Call Talkgroup: " << call_info.talkgroup << " Transmission Talkgroup: " << t.talkgroup;
      call_info.talkgroup = t.talkgroup;
    }


    Call_Source call_source = {t.source, t.start_time, total_length, false, "", tag};
    Call_Error call_error = {t.start_time, total_length, t.length, t.error_count, t.spike_count};
    call_info.error_count = call_info.error_count + t.error_count;
    call_info.spike_count = call_info.spike_count + t.spike_count;
    call_info.transmission_source_list.push_back(call_source);
    call_info.transmission_error_list.push_back(call_error);

    total_length = total_length + t.length;
    it++;
  }

  Talkgroup *tg = sys->find_talkgroup(call_info.talkgroup);
  if (tg != NULL) {
    call_info.talkgroup_tag = tg->tag;
    call_info.talkgroup_alpha_tag = tg->alpha_tag;
    call_info.talkgroup_description = tg->description;
    call_info.talkgroup_group = tg->group;
  } else {
    call_info.talkgroup_tag = "";
    call_info.talkgroup_alpha_tag = "";
    call_info.talkgroup_description = "";
    call_info.talkgroup_group = "";
  }

  call_info.length = total_length;

  return call_info;
}

void Call_Concluder::conclude_call(Call *call, System *sys, Config config) {
  Call_Data_t call_info = create_call_data(call, sys, config);

  std::string loghdr = log_header( call_info.short_name, call_info.call_num, call_info.talkgroup_display , call_info.freq);

  if(call->get_state() == MONITORING && call->get_monitoring_state() == SUPERSEDED){
    BOOST_LOG_TRIVIAL(info) << loghdr << "Call has been superseded.";
    return;
  }

  if (call_info.encrypted) {
    // Notify plugins so they see the call ended (with duration/metadata).
    plugman_call_end(call_info);
    return;
  }

  if (call_info.transmission_list.size() == 0 && call_info.min_transmissions_removed == 0) {
    BOOST_LOG_TRIVIAL(error) << loghdr << "No Transmissions were recorded!";
    return;
  }
  else if (call_info.transmission_list.size() == 0 && call_info.min_transmissions_removed > 0) {
    BOOST_LOG_TRIVIAL(info) << loghdr << "No Transmissions were recorded! " << call_info.min_transmissions_removed << " transmissions less than " << sys->get_min_tx_duration() << " seconds were removed.";
    return;
  }

  if (call_info.length <= sys->get_min_duration()) {
    BOOST_LOG_TRIVIAL(info) << loghdr << "Call length: " << call_info.length << " is less than min duration: " << sys->get_min_duration();
    return;
  }

  plugman_call_end(call_info);
}
