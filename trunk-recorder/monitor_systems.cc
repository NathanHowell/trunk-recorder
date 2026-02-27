#include "monitor_systems.h"
#include "recorders/p25_recorder.h"

using namespace std;

// File-local pointer for signal handler access to TrunkContext
static TrunkContext *g_ctx = nullptr;

void exit_interupt(int sig) { // can be called asynchronously
  if (g_ctx) g_ctx->exit_flag = 1;
}

using SteadyClock = std::chrono::steady_clock;
using TimePoint = SteadyClock::time_point;

bool start_recorder(const std::shared_ptr<Call> &call, TrunkMessage message, Config &config, const std::shared_ptr<System> &sys, std::vector<std::shared_ptr<Source>> &sources) {
  auto talkgroup = sys->find_talkgroup(call->get_talkgroup());

  bool source_found = false;
  bool recorder_found = false;
  bool override_record_unknown = false;

  std::shared_ptr<Recorder> recorder;
  std::shared_ptr<Recorder> debug_recorder;
  std::shared_ptr<Recorder> sigmf_recorder;

  if (!talkgroup){
    for (auto &TGID : sys->get_talkgroup_patch(call->get_talkgroup())) {  //for each talkgroup in the patch
      if (sys->find_talkgroup(TGID) != nullptr){  //if the patched talkgroup is known
        override_record_unknown = true;
        std::string loghdr = log_header( call->get_short_name(), call->get_call_num(), call->get_talkgroup_display(), call->get_freq());
        BOOST_LOG_TRIVIAL(info) << loghdr << "\u001b[33mEnabling recording of TG not in Talkgroup File due to active supergroup patch\u001b[0m ";
      }
    }
  }

  if (!talkgroup && (sys->get_record_unknown() == false) && override_record_unknown == false) {
    call->set_state(MONITORING);
    call->set_monitoring_state(UNKNOWN_TG);
    if (sys->get_hideUnknown() == false) {
      std::string loghdr = log_header( call->get_short_name(), call->get_call_num(), call->get_talkgroup_display(), call->get_freq());
      BOOST_LOG_TRIVIAL(info) << loghdr << "\u001b[33mNot Recording: TG not in Talkgroup File\u001b[0m ";
    }
    return false;
  }

  if (talkgroup) {
    call->set_talkgroup_tag(talkgroup->alpha_tag);
  } else {
    call->set_talkgroup_tag("-");
  }

  if (call->get_encrypted() == true || (talkgroup && (talkgroup->mode.compare("E") == 0 || talkgroup->mode.compare("TE") == 0 || talkgroup->mode.compare("DE") == 0))) {
    if (talkgroup && (talkgroup->mode.compare("E") == 0 || talkgroup->mode.compare("TE") == 0 || talkgroup->mode.compare("DE") == 0)) {
      call->set_encrypted(true);
    }
    
    if (!sys->get_monitorEncrypted()) {
      call->set_state(MONITORING);
      call->set_monitoring_state(ENCRYPTED);
      if (sys->get_hideEncrypted() == false) {
        long unit_id = call->get_current_source_id();
        std::string tag = sys->find_unit_tag(unit_id);
        if (tag != "") {
          tag = " (\033[0;34m" + tag + "\033[0m)";
        }
        std::string loghdr = log_header( sys->get_short_name(), call->get_call_num(), call->get_talkgroup_display(), call->get_freq());
        BOOST_LOG_TRIVIAL(info) << loghdr << "\u001b[31mNot Recording: ENCRYPTED\u001b[0m - src: " << unit_id << tag;
      }
      return false;
    }
  }

  for (auto &source : sources) {

    if ((source->get_min_hz() <= call->get_freq()) &&
        (source->get_max_hz() >= call->get_freq())) {
      source_found = true;

      if (talkgroup) {
        int priority = talkgroup->get_priority();
        for (auto &TGID : sys->get_talkgroup_patch(call->get_talkgroup())) {
          if (sys->find_talkgroup(TGID) != nullptr) {
            if (sys->find_talkgroup(TGID)->get_priority() < priority) {
              priority = sys->find_talkgroup(TGID)->get_priority();
              BOOST_LOG_TRIVIAL(info) << "Temporarily increased priority of talkgroup " << call->get_talkgroup() << " to " << sys->find_talkgroup(TGID)->get_priority() << " due to active patch with talkgroup " << TGID;
            }
          }
        }
        if (talkgroup->mode.compare("A") == 0) {
          recorder = source->get_analog_recorder(talkgroup, priority, call);
          call->set_is_analog(true);
        } else {
          recorder = source->get_digital_recorder(talkgroup, priority, call);
        }
      } else {
        std::string loghdr = log_header( call->get_short_name(), call->get_call_num(), call->get_talkgroup_display(), call->get_freq());
        BOOST_LOG_TRIVIAL(info) << loghdr << "TG not in Talkgroup File ";

        // A talkgroup was not found from the talkgroup file.
        // Use an analog recorder if this is a Type II trunk and defaultMode is analog.
        // All other cases use a digital recorder.
        if ((config.default_mode == "analog") && (sys->get_system_type() == "smartnet")) {
          recorder = source->get_analog_recorder(call);
          call->set_is_analog(true);
        } else {
          recorder = source->get_digital_recorder(call);
        }
      }

      if (recorder) {
        if (message.meta.length()) {
          BOOST_LOG_TRIVIAL(trace) << message.meta;
        }

        if (recorder->start(call)) {
          call->set_recorder(recorder);
          call->set_state(RECORDING);
          config.event_sink->setup_recorder(recorder);
          recorder_found = true;
        } else {
          call->set_state(MONITORING);
          // call->set_monitoring_state(NO_SOURCE);
          recorder_found = false;
          return false;
        }
      } else {
        // not recording call either because the priority was too low or no
        // recorders were available
        return false;
      }

      debug_recorder = source->get_debug_recorder();

      if (debug_recorder) {
        debug_recorder->start(call);
        call->set_debug_recorder(debug_recorder);
        call->set_debug_recording(true);
        config.event_sink->setup_recorder(debug_recorder);
        recorder_found = true;
      } else {
        // BOOST_LOG_TRIVIAL(info) << "\tNot debug recording call";
      }

      sigmf_recorder = source->get_sigmf_recorder();

      if (sigmf_recorder) {
        sigmf_recorder->start(call);
        call->set_sigmf_recorder(sigmf_recorder);
        call->set_sigmf_recording(true);
        config.event_sink->setup_recorder(sigmf_recorder);
        recorder_found = true;
      } else {
        // BOOST_LOG_TRIVIAL(info) << "\tNot SIGMF recording call";
      }

      if (recorder_found) {
        // recording successfully started.
        return true;
      }
    }
  }

  if (!source_found) {
    call->set_state(MONITORING);
    call->set_monitoring_state(NO_SOURCE);
    std::string loghdr = log_header( call->get_short_name(), call->get_call_num(), call->get_talkgroup_display(), call->get_freq());
    BOOST_LOG_TRIVIAL(error) << loghdr << "\u001b[36mNot Recording: no source covering Freq\u001b[0m";
    return false;
  }
  return false;
}

void print_status(std::vector<std::shared_ptr<Source>> &sources, std::vector<std::shared_ptr<System>> &systems, std::vector<std::shared_ptr<Call>> &calls) {
  BOOST_LOG_TRIVIAL(info) << "Active Calls: " << calls.size();

  for (auto &call : calls) {
    auto recorder = call->get_recorder();
    std::string loghdr = log_header( call->get_short_name(), call->get_call_num(), call->get_talkgroup_display(), call->get_freq());
    if (call->get_state() == MONITORING) {
      BOOST_LOG_TRIVIAL(info) << loghdr << "Elapsed: " << std::setw(4) << call->elapsed().count() << " State: " << format_state(call->get_state(), call->get_monitoring_state());
    } else {
      if (call->is_conventional() ) {
        bool is_enabled = call->get_recorder()->is_enabled();
         BOOST_LOG_TRIVIAL(info) << loghdr << "Elapsed: " << std::setw(4) << call->elapsed().count() << " State: " << format_state(call->get_state()) << " Enabled: " << is_enabled;
      } else {
        BOOST_LOG_TRIVIAL(info) << loghdr << "Elapsed: " << std::setw(4) << call->elapsed().count() << " State: " << format_state(call->get_state());
      }
    }

    if (recorder) {
        BOOST_LOG_TRIVIAL(info) << "\t[ " << std::setw(2) << recorder->get_num() << " ] State: " << format_state(recorder->get_state());
    }
  }

  BOOST_LOG_TRIVIAL(info) << "Active Patches: ";
  for (auto &sys : systems) {
    sys->print_active_talkgroup_patches();
  }

  BOOST_LOG_TRIVIAL(info) << "Control Channel Decode Rates: ";
  for (auto &sys : systems) {
    if ((sys->get_system_type() != "conventional") && (sys->get_system_type() != "conventionalP25") && (sys->get_system_type() != "conventionalDMR") && (sys->get_system_type() != "conventionalSIGMF")) {
      BOOST_LOG_TRIVIAL(info) << "[" << sys->get_short_name() << "]\t" << format_freq(sys->get_current_control_channel()) << "\t" << sys->get_decode_rate() << " msg/sec";
      
      if ((sys->get_source()->get_autotune_source()) && (sys->get_system_type() == "p25")) {
        // If control channel source has autotune enabled, perform autotune adjustments and log to console
        autotune_control_channel(sys);
      }
    }
  }

  BOOST_LOG_TRIVIAL(info) << "Recorders: ";

  for (auto &source : sources) {
    source->print_recorders();
  }
}

void manage_conventional_call(const std::shared_ptr<Call> &call, Config &config) {

  if (call->get_recorder()) {
    // if any recording has happened

    if (call->get_current_length() > 0) {

      BOOST_LOG_TRIVIAL(trace) << "[" << call->get_short_name() << "]\t\033[0;34m" << call->get_call_num() << "C\033[0m Call Length: " << call->get_current_length() << "s\t Idle: " << call->get_recorder()->is_idle() << "\t Squelched: " << call->get_recorder()->is_squelched() << " Idle Count: " << call->get_idle_count();

      // means that the squelch is on and it has stopped recording
      if (call->get_recorder()->is_idle()) {
        // increase the number of periods it has not been recording for
        call->set_noise(call->get_recorder()->get_pwr());
        call->increase_idle_count();
      } else {
        call->set_signal(call->get_recorder()->get_pwr());
        if (call->get_idle_count() > 0) {
          // if it starts recording again, then reset the idle count
          call->reset_idle_count();
        }
      }

      // if no additional recording has happened in the past X periods, stop and open new file
      if (call->get_idle_count() > config.call_timeout.count()) {
        auto recorder = call->get_recorder();
        call->conclude_call();
        call->restart_call();
        if (recorder) {
          config.event_sink->setup_recorder(recorder);
          config.event_sink->call_start(call);
        }
      } else if ((call->get_current_length() > call->get_system()->get_max_duration()) && (call->get_system()->get_max_duration() > 0)) {
        auto recorder = call->get_recorder();
        call->conclude_call();
        call->restart_call();
        if (recorder) {
          config.event_sink->setup_recorder(recorder);
          config.event_sink->call_start(call);
        }
      }
    } else if (!call->get_recorder()->is_active()) {
      // P25 Conventional and DMR Recorders need a have the graph unlocked before they can start recording.
      auto recorder = call->get_recorder();
      recorder->start(call);
      call->set_state(RECORDING);
      config.event_sink->call_start(call);
      BOOST_LOG_TRIVIAL(trace) << "[" << call->get_short_name() << "]\t\033[0;34m" << call->get_call_num() << "C\033[0m Starting P25 Convetional Recorder ";
    }
  }
}

void manage_calls(Config &config, std::vector<std::shared_ptr<Call>> &calls) {
  bool ended_call = false;
  for (auto it = calls.begin(); it != calls.end();) {
    auto &call = *it;
    State state = call->get_state();
    // Handle Conventional Calls
    if (call->is_conventional()) {
      manage_conventional_call(call, config);
      ++it;
      continue;
    }

    // Handle Trunked Calls

    if ((state == MONITORING) && (call->since_last_update() > config.call_timeout)) {
      call->conclude_call();
      ended_call = true;
      it = calls.erase(it);
      continue;
    }

    if (state == RECORDING) {
      auto recorder = call->get_recorder();

      // Stop the call if:
      // - there hasn't been an UPDATE for it on the Control Channel in X seconds AND the recorder hasn't written anything in X seconds

      if (recorder && (recorder->since_last_write() > config.call_timeout) && (call->since_last_update() > config.call_timeout)) {
        std::string loghdr = log_header( call->get_short_name(), call->get_call_num(), call->get_talkgroup_display(), call->get_freq());
        BOOST_LOG_TRIVIAL(trace) << loghdr << "\u001b[36m Stopping Call because of Recorder \u001b[0m Rec last write: " << recorder->since_last_write().count() << "s State: " << format_state(recorder->get_state());
        call->conclude_call();
        // The State of the Recorders has changed, so lets send an update
        ended_call = true;
        if (recorder) {
          config.event_sink->setup_recorder(recorder);
        }
        it = calls.erase(it);
        continue;
      }
    } else if (call->since_last_update() > config.call_timeout) {
      auto recorder = call->get_recorder();
      std::string loghdr = log_header( call->get_short_name(), call->get_call_num(), call->get_talkgroup_display(), call->get_freq());
      if (recorder) {
        BOOST_LOG_TRIVIAL(trace) << loghdr << "\u001b[36m  Call UPDATEs has been inactive for more than " << config.call_timeout.count() << "s \u001b[0m Rec last write: " << recorder->since_last_write().count() << "s State: " << format_state(recorder->get_state());
      } else {
        BOOST_LOG_TRIVIAL(trace) << loghdr << "\u001b[36m  Call UPDATEs has been inactive for more than " << config.call_timeout.count() << "s \u001b[0m (no recorder)";
      }
    }
    ++it;
  } // foreach loggers

  if (ended_call) {
    config.event_sink->calls_active(calls);
  }
}

void current_system_status(TrunkMessage message, const std::shared_ptr<System> &sys, const std::shared_ptr<EventSink> &event_sink) {
  if (sys->update_status(message)) {
    event_sink->setup_system(sys);
  }
}

void current_system_sysid(TrunkMessage message, const std::shared_ptr<System> &sys, const std::shared_ptr<EventSink> &event_sink) {
  if ((sys->get_system_type() == "p25") || (sys->get_system_type() == "conventionalP25")) {
    if (sys->update_sysid(message)) {
      event_sink->setup_system(sys);
    }
  }
}

void unit_registration(const std::shared_ptr<System> &sys, long source_id, const std::shared_ptr<EventSink> &event_sink) {
  event_sink->unit_registration(sys, source_id);
}

void unit_deregistration(const std::shared_ptr<System> &sys, long source_id, const std::shared_ptr<EventSink> &event_sink) {
  event_sink->unit_deregistration(sys, source_id);
}

void unit_acknowledge_response(const std::shared_ptr<System> &sys, long source_id, const std::shared_ptr<EventSink> &event_sink) {
  event_sink->unit_acknowledge_response(sys, source_id);
}

void unit_group_affiliation(const std::shared_ptr<System> &sys, long source_id, long talkgroup_num, const std::shared_ptr<EventSink> &event_sink) {
  event_sink->unit_group_affiliation(sys, source_id, talkgroup_num);
}

void unit_data_grant(const std::shared_ptr<System> &sys, long source_id, const std::shared_ptr<EventSink> &event_sink) {
  event_sink->unit_data_grant(sys, source_id);
}

void unit_answer_request(const std::shared_ptr<System> &sys, long source_id, long talkgroup, const std::shared_ptr<EventSink> &event_sink) {
  event_sink->unit_answer_request(sys, source_id, talkgroup);
}

void unit_location(const std::shared_ptr<System> &sys, long source_id, long talkgroup_num, const std::shared_ptr<EventSink> &event_sink) {
  event_sink->unit_location(sys, source_id, talkgroup_num);
}




void handle_call_grant(TrunkMessage message, const std::shared_ptr<System> &sys, bool grant_message, Config &config, std::vector<std::shared_ptr<Source>> &sources, std::vector<std::shared_ptr<Call>> &calls) {
  bool call_found = false;
  bool duplicate_grant = false;
  bool superseding_grant = false;
  bool recording_started [[maybe_unused]] = false;

  std::shared_ptr<Call> original_call;

  /* Notes: it is possible for 2 Calls to exist for the same talkgroup on different freq. This happens when a Talkgroup starts on a freq
  that current recorder can't retune to. In this case, the current orig Talkgroup reocrder will keep going on the old freq, while a new
  recorder is start on a source that can cover that freq. This makes sure any of the remaining transmission that it is in the buffer
  of the original recorder gets flushed.
  UPDATED: however if we have 2 different talkgroups on the same freq we should do a stop_call on the original call since it is being used by another TG now. This will let the recorder keep
  going until it gets a termination flag.
  */

  // BOOST_LOG_TRIVIAL(info) << "TG: " << message.talkgroup << " sys num: " << message.sys_num << " freq: " << message.freq << " TDMA Slot" << message.tdma_slot << " TDMA: " << message.phase2_tdma;

  unsigned long message_preferredNAC = 0;
  unsigned long call_rfss_site = 0;
  unsigned long sys_rfss_site = 0;

  auto message_talkgroup = sys->find_talkgroup(message.talkgroup);
  if (message_talkgroup) {
    message_preferredNAC = message_talkgroup->get_preferredNAC();
  }

  for (auto &call : calls) {

    /* This is for Multi-Site support */
    // Find candidate duplicate calls with the same talkgroup and different multisite-enabled systems
    if (call->get_talkgroup() == message.talkgroup) {
      if (call->get_sys_num() != message.sys_num) {
        if (call->get_system()->get_multiSite() && sys->get_multiSite()) {
          if (call->get_system()->get_wacn() == sys->get_wacn()) {
            // Default mode to match WACN and use RFSS/Site to identify duplicate calls
            sys_rfss_site = sys->get_sys_rfss() * 10000 + sys->get_sys_site_id();
            call_rfss_site = call->get_system()->get_sys_rfss() * 10000 + call->get_system()->get_sys_site_id();
            if ((sys_rfss_site != call_rfss_site) && (call->get_system()->get_multiSiteSystemName() == "")) {
              if (call->get_state() == RECORDING) {

                duplicate_grant = true;
                original_call = call;

                unsigned long call_preferredNAC = 0;
                auto call_talkgroup = call->get_system()->find_talkgroup(message.talkgroup);
                if (call_talkgroup) {
                  call_preferredNAC = call_talkgroup->get_preferredNAC();
                }

                // Evaluate superseding grants by comparing call NAC or RFSS-Site against preferred NAC/site in talkgroup .csv
                if ((call_preferredNAC != call->get_system()->get_nac()) && (message_preferredNAC == sys->get_nac())) {
                  superseding_grant = true;
                } else if ((call_preferredNAC != call_rfss_site) && (message_preferredNAC == sys_rfss_site)) {
                  superseding_grant = true;
                }
              }
            }

            // Secondary mode to match multiSiteSystemName and use multiSiteSystemNumber.
            // If a multiSiteSystemName has been manually entered;
            // We already know that Call's system number does not match the message system number.
            // In this case, we check that the multiSiteSystemName is present, and that the Call and System multiSiteSystemNames are the same.
            else if ((call->get_system()->get_multiSiteSystemName() != "") && (call->get_system()->get_multiSiteSystemName() == sys->get_multiSiteSystemName())) {
              if (call->get_state() == RECORDING) {

                duplicate_grant = true;
                original_call = call;

                unsigned long call_preferredNAC = 0;
                auto call_talkgroup = call->get_system()->find_talkgroup(message.talkgroup);
                if (call_talkgroup) {
                  call_preferredNAC = call_talkgroup->get_preferredNAC();
                }

                if ((call->get_system()->get_multiSiteSystemNumber() != 0) && (sys->get_multiSiteSystemNumber() != 0)) {
                  if ((call_preferredNAC != call->get_system()->get_multiSiteSystemNumber()) && (message_preferredNAC == sys->get_multiSiteSystemNumber())) {
                    superseding_grant = true;
                  }
                }
              }
            }
          }
        }
      }
    }

    if ((call->get_talkgroup() == message.talkgroup) && (call->get_sys_num() == message.sys_num) && (call->get_freq() == message.freq) && (call->get_tdma_slot() == message.tdma_slot) && (call->get_phase2_tdma() == message.phase2_tdma)) {
      call_found = true;
      bool source_updated = call->update(message);
      if (source_updated) {
        config.event_sink->call_start(call);
      }
    }

    // There is an existing call on freq and slot that the new call will be started on. We should stop the older call. The older recorder will
    // keep writing to the file until it hits a termination flag, so no packets should be dropped.
    if ((call->get_state() == RECORDING) && (call->get_talkgroup() != message.talkgroup) && (call->get_sys_num() == message.sys_num) && (call->get_freq() == message.freq) && (call->get_tdma_slot() == message.tdma_slot) && (call->get_phase2_tdma() == message.phase2_tdma)) {
      auto recorder = call->get_recorder();
      string recorder_state = "UNKNOWN";
      if (recorder) {
        recorder_state = format_state(recorder->get_state());
      }
      std::string loghdr = log_header( call->get_short_name(), call->get_call_num(), call->get_talkgroup_display(), call->get_freq());
      BOOST_LOG_TRIVIAL(trace) << loghdr << "\u001b[36mShould be Stopping RECORDING call, Recorder State: " << recorder_state << " RX overlapping TG message Freq, TG:" << message.talkgroup << "\u001b[0m";
    }

  }

  if (!call_found) {
    auto call = Call::make(message, sys, config);

    auto talkgroup = sys->find_talkgroup(call->get_talkgroup());

    if (talkgroup) {
      call->set_talkgroup_tag(talkgroup->alpha_tag);
    } else {
      call->set_talkgroup_tag("-");
    }

    boost::format original_call_data;
    boost::format grant_call_data;

    if ((superseding_grant) || (duplicate_grant)) {
      if (original_call->get_system()->get_multiSiteSystemName() == "") {
        original_call_data = boost::format("\u001b[34m%sC\u001b[0m %X/%s-%s ") % original_call->get_call_num() % original_call->get_system()->get_wacn() % original_call->get_system()->get_sys_rfss() % original_call->get_system()->get_sys_site_id();
        grant_call_data = boost::format("\u001b[34m%sC\u001b[0m %X/%s-%s ") % call->get_call_num() % sys->get_wacn() % sys->get_sys_rfss() % +sys->get_sys_site_id();
      } else {
        original_call_data = boost::format("\u001b[34m%sC\u001b[0m %s/%s ") % original_call->get_call_num() % original_call->get_system()->get_multiSiteSystemName() % original_call->get_system()->get_multiSiteSystemNumber();
        grant_call_data = boost::format("\u001b[34m%sC\u001b[0m %s/%s ") % call->get_call_num() % sys->get_multiSiteSystemName() % sys->get_multiSiteSystemNumber();
      }
    }
    if (superseding_grant) {
      std::string loghdr = log_header( call->get_short_name(), call->get_call_num(), call->get_talkgroup_display(), call->get_freq());

      BOOST_LOG_TRIVIAL(info) << loghdr << "\u001b[36mSuperseding Grant\u001b[0m - Stopping original call: " << original_call_data << "- Superseding call: " << grant_call_data;
      // Attempt to start a new call on the preferred NAC.
      recording_started = start_recorder(call, message, config, sys, sources);

      if (recording_started) {
        // Clean up the original call.
        original_call->set_state(MONITORING);
        original_call->set_monitoring_state(SUPERSEDED);
        original_call->conclude_call();
      } else {

        BOOST_LOG_TRIVIAL(info) << loghdr << "\u001b[36mCould not start Superseding recorder.\u001b[0m Continuing original call: " << original_call->get_call_num() << "C";
      }
    } else if (duplicate_grant) {
      std::string loghdr = log_header( call->get_short_name(), call->get_call_num(), call->get_talkgroup_display(), call->get_freq());
      call->set_state(MONITORING);
      call->set_monitoring_state(DUPLICATE);
      BOOST_LOG_TRIVIAL(info) << loghdr << "\u001b[36mDuplicate Grant\u001b[0m - Not recording: " << grant_call_data << "- Original call: " << original_call_data;
    } else {
      recording_started = start_recorder(call, message, config, sys, sources);
      if (recording_started && !grant_message) {
        std::string loghdr = log_header( call->get_short_name(), call->get_call_num(), call->get_talkgroup_display(), call->get_freq());
        BOOST_LOG_TRIVIAL(info) << loghdr << "\u001b[36mThis was an UPDATE\u001b[0m";
      }
    }
    calls.push_back(call);
    config.event_sink->call_start(call);
    config.event_sink->calls_active(calls);
  }
}

void handle_call_update(TrunkMessage message, const std::shared_ptr<System> &sys, std::vector<std::shared_ptr<Call>> &calls, Config &config) {
  bool call_found = false;

  /* Notes: it is possible for 2 Calls to exist for the same talkgroup on different freq. This happens when a Talkgroup starts on a freq
  that current recorder can't retune to. In this case, the current orig Talkgroup reocrder will keep going on the old freq, while a new
  recorder is start on a source that can cover that freq. This makes sure any of the remaining transmission that it is in the buffer
  of the original recorder gets flushed.
  UPDATED: however if we have 2 different talkgroups on the same freq we should do a stop_call on the original call since it is being used by another TG now. This will let the recorder keep
  going until it gets a termination flag.
  */

  for (auto &call : calls) {

    // BOOST_LOG_TRIVIAL(info) << "TG: " << call->get_talkgroup() << " | " << message.talkgroup << " sys num: " << call->get_sys_num() << " | " << message.sys_num << " freq: " << call->get_freq() << " | " << message.freq << " TDMA Slot" << call->get_tdma_slot() << " | " << message.tdma_slot << " TDMA: " << call->get_phase2_tdma() << " | " << message.phase2_tdma;
    if ((call->get_talkgroup() == message.talkgroup) && (call->get_sys_num() == message.sys_num) && (call->get_freq() == message.freq) && (call->get_tdma_slot() == message.tdma_slot) && (call->get_phase2_tdma() == message.phase2_tdma)) {
      call_found = true;

      if (message.encrypted) {
        call->set_encrypted(true);
      } else {
        auto talkgroup = sys->find_talkgroup(message.talkgroup);
        if (talkgroup && (talkgroup->mode.compare("E") == 0 || talkgroup->mode.compare("TE") == 0 || talkgroup->mode.compare("DE") == 0)) {
          call->set_encrypted(true);
        }
      }

      bool source_updated = call->update(message);
      if (source_updated) {
        config.event_sink->call_start(call);
      }
    }
  }

  if (!call_found) {
    // Note: some calls maybe removed before the UPDATEs stop on the trunking channel if there is some GAP in the updates.
    // BOOST_LOG_TRIVIAL(info) << "Call not found for UPDATE mesg - either we missed GRANT or removed Call too soon\tFreq: " << format_freq(message.freq) << "\tTG:" << message.talkgroup << "\tSource: " << message.source << "\tSys Num: " << message.sys_num << "\tTDMA Slot: " << message.tdma_slot << "\tTDMA: " << message.phase2_tdma;
  }
}

void handle_message(std::vector<TrunkMessage> messages, const std::shared_ptr<System> &sys, Config &config, std::vector<std::shared_ptr<Source>> &sources, std::vector<std::shared_ptr<Call>> &calls, gr::top_block_sptr &tb) {
  for (std::vector<TrunkMessage>::iterator it = messages.begin(); it != messages.end(); it++) {
    TrunkMessage message = *it;

    switch (message.message_type) {
    case GRANT:
      handle_call_grant(message, sys, true, config, sources, calls);
      break;

    case UPDATE:
      if (config.new_call_from_update) {
        // Treat UPDATE as a GRANT and start a new call if we don't have one for this TG
        handle_call_grant(message, sys, false, config, sources, calls);
      } else {
        // Treat UPDATE as an UPDATE and only update existing calls
        handle_call_update(message, sys, calls, config);
      }
      break;

    case UU_V_GRANT:
      if (config.record_uu_v_calls) {
        handle_call_grant(message, sys, true, config, sources, calls);
      }
      break;

    case UU_V_UPDATE:
      if (config.record_uu_v_calls) {
        handle_call_update(message, sys, calls, config);
      }
      break;

    case CONTROL_CHANNEL:
      sys->add_control_channel(message.freq);
      break;

    case REGISTRATION:
      unit_registration(sys, message.source, config.event_sink);
      break;

    case DEREGISTRATION:
      unit_deregistration(sys, message.source, config.event_sink);
      break;

    case AFFILIATION:
      unit_group_affiliation(sys, message.source, message.talkgroup, config.event_sink);
      break;

    case SYSID:
      current_system_sysid(message, sys, config.event_sink);
      break;

    case STATUS:
      current_system_status(message, sys, config.event_sink);
      break;

    case LOCATION:
      unit_location(sys, message.source, message.talkgroup, config.event_sink);
      break;

    case ACKNOWLEDGE:
      unit_acknowledge_response(sys, message.source, config.event_sink);
      break;

    case PATCH_ADD:
      sys->update_active_talkgroup_patches(message.patch_data);
      break;
    case PATCH_DELETE:
      sys->delete_talkgroup_patch(message.patch_data);
      break;

    case DATA_GRANT:
      unit_data_grant(sys, message.source, config.event_sink);
      break;

    case UU_ANS_REQ:
      unit_answer_request(sys, message.source, message.talkgroup, config.event_sink);
      break;

    case INVALID_CC_MESSAGE:
    {
      //Do not count messages that aren't valid TSBK or MBTs.
      int msg_count = sys->get_message_count();
      if(msg_count > 1){
        sys->set_message_count(msg_count - 1);
      }
      break;
    }

    case TDULC:
      sys->retune_trunking(tb, sources);
      if (sys->get_source() && sys->get_source()->get_autotune_source() && sys->get_system_type() == "p25") {
        autotune_control_channel(sys, false);
      }
      break;

    case UNKNOWN:
      break;
    }
  }
}


void check_message_count(float timeDiff, Config &config, gr::top_block_sptr &tb, std::vector<std::shared_ptr<Source>> &sources, std::vector<std::shared_ptr<System>> &systems) {
  config.event_sink->setup_config(sources, systems);
  config.event_sink->system_rates(systems, timeDiff);

  for (auto &sys : systems) {
    if ((sys->get_system_type() != "conventional") && (sys->get_system_type() != "conventionalP25") && (sys->get_system_type() != "conventionalDMR") && (sys->get_system_type() != "conventionalSIGMF")) {
      int msgs_decoded_per_second = std::floor(sys->get_message_count() / timeDiff);
      sys->set_decode_rate(msgs_decoded_per_second);

      if (msgs_decoded_per_second < 2) {

        // if it loses track of the control channel, quit after a while
        if (config.control_retune_limit > 0) {
          sys->set_retune_attempts(sys->get_retune_attempts() + 1);
          if (sys->get_retune_attempts() > config.control_retune_limit) {
            BOOST_LOG_TRIVIAL(error) << "[" << sys->get_short_name() << "]\t"
                                     << "Control channel retune limit exceeded after " << sys->get_retune_attempts() << " tries - Terminating trunk recorder";
            g_ctx->exit_flag = 1;
            g_ctx->exit_code = EXIT_FAILURE;
            return;
          }
        }
        if (sys->control_channel_count() > 1) {
          sys->retune_trunking(tb, sources);
          if (sys->get_source() && sys->get_source()->get_autotune_source() && sys->get_system_type() == "p25") {
            autotune_control_channel(sys, false);
          }
        } else {
          BOOST_LOG_TRIVIAL(error) << "[" << sys->get_short_name() << "]\tThere is only one control channel defined";
        }

      } else {
        sys->set_retune_attempts(0);
      }

      if (msgs_decoded_per_second < config.control_message_warn_rate) {
        BOOST_LOG_TRIVIAL(error) << "[" << sys->get_short_name() << "]\tfreq: " << format_freq(sys->get_current_control_channel()) << "\tControl Channel Message Decode Rate: " << msgs_decoded_per_second << "/sec, count:  " << sys->get_message_count();
      } else if (config.control_message_warn_rate == -1) {
        BOOST_LOG_TRIVIAL(info) << "[" << sys->get_short_name() << "]\tfreq: " << format_freq(sys->get_current_control_channel()) << "\tControl Channel Message Decode Rate: " << msgs_decoded_per_second << "/sec, count:  " << sys->get_message_count();
      }
    }
    sys->set_message_count(0);
  }
}

void check_conventional_channel_detection(std::vector<std::shared_ptr<Source>> &sources) {
  for (auto &source : sources) {
    source->enable_detected_recorders();
  }
}

// This is to handle the messages that come off the Analog recorder.
void process_message_queues(std::vector<std::shared_ptr<System>> &systems) {
  for (auto &sys : systems) {
    for (auto &ar : sys->get_conventional_recorders()) {
      ar->process_message_queues();
    }
  }
}

// Process message queues for recorders associated with Calls
void process_recorder_message_queues(std::vector<std::shared_ptr<Call>> &calls) {
  for (auto &call : calls) {
    if (call->get_state() == RECORDING) {
      auto recorder = call->get_recorder();
      if (recorder && (recorder->get_type() == P25 || recorder->get_type() == P25C)) {
        auto p25_rec = std::dynamic_pointer_cast<p25_recorder>(recorder);
        // Verify recorder status as conventionals calls may be in a RECORDING:IDLE state
        if (p25_rec && (p25_rec->is_active())) {
          p25_rec->process_message_queues();
        }
      }
    }
  }
}

int monitor_messages(TrunkContext &ctx) {
  g_ctx = &ctx;

  Config &config = ctx.config;
  gr::top_block_sptr &tb = ctx.tb;
  std::vector<std::shared_ptr<Source>> &sources = ctx.sources;
  std::vector<std::shared_ptr<System>> &systems = ctx.systems;
  std::vector<std::shared_ptr<Call>> &calls = ctx.calls;

  gr::message::sptr msg;

  auto now = SteadyClock::now();
  TimePoint last_status_time = now;
  TimePoint last_decode_rate_check = now;
  TimePoint management_timestamp = now;
  TimePoint last_conventional_channel_detection_check = now;
  std::vector<TrunkMessage> trunk_messages;
  std::unique_ptr<SmartnetParser> smartnet_parser;
  std::unique_ptr<P25Parser> p25_parser;

  signal(SIGINT, exit_interupt);

  if (systems.empty()) {
    BOOST_LOG_TRIVIAL(error) << "No systems configured, cannot start monitoring.";
    return 1;
  }
  // TODO: SmartnetParser blindly takes the first system regardless of type — should find a smartnet system
  smartnet_parser = std::make_unique<SmartnetParser>(systems.front());
  p25_parser = std::make_unique<P25Parser>();

  while (1) {

    if (ctx.exit_flag) { // my action when signal set it 1
      BOOST_LOG_TRIVIAL(info) << "Caught an Exit Signal...";
      for (auto &call : calls) {
        if (call->get_state() != MONITORING) {
          call->conclude_call();
        }
      }
      calls.clear();

      BOOST_LOG_TRIVIAL(info) << "Cleaning up & Exiting...";

      // Sleep for 5 seconds to allow for all of the Call Concluder threads to finish.
      std::this_thread::sleep_for(std::chrono::milliseconds(5000));
      return ctx.exit_code;
    }

    process_message_queues(systems);
    process_recorder_message_queues(calls);

    config.event_sink->poll_one();

    for (auto &system : systems) {
      if ((system->get_system_type() == "p25") || (system->get_system_type() == "smartnet")) {
        msg.reset();
        msg = system->get_msg_queue()->delete_head_nowait();
        while (msg != 0) {
          system->set_message_count(system->get_message_count() + 1);

          if (system->get_system_type() == "smartnet") {
            trunk_messages = smartnet_parser->parse_message(msg, system);
            handle_message(trunk_messages, system, config, sources, calls, tb);
            config.event_sink->trunk_message(trunk_messages, system);
          }

          if (system->get_system_type() == "p25") {
            trunk_messages = p25_parser->parse_message(msg, system);
            handle_message(trunk_messages, system, config, sources, calls, tb);
            config.event_sink->trunk_message(trunk_messages, system);
          }

          if (msg->type() == -1) {
            BOOST_LOG_TRIVIAL(error) << "[" << system->get_short_name() << "]\t process_data_unit timeout";
          }

          msg.reset();
          msg = system->get_msg_queue()->delete_head_nowait();
        }
      }
    }
    now = SteadyClock::now();

    if ((now - last_conventional_channel_detection_check) >= std::chrono::milliseconds(100)) {
      check_conventional_channel_detection(sources);
      last_conventional_channel_detection_check = now;
    }

    if ((now - management_timestamp) >= std::chrono::seconds(1)) {
      manage_calls(config, calls);
      management_timestamp = now;
    }

    std::this_thread::sleep_for(std::chrono::milliseconds(10));

    auto decode_rate_elapsed = now - last_decode_rate_check;

    if (decode_rate_elapsed >= std::chrono::seconds(3)) {
      float timeDiffSeconds = std::chrono::duration<float>(decode_rate_elapsed).count();
      check_message_count(timeDiffSeconds, config, tb, sources, systems);
      for (auto &source : sources) {
        if (!source->got_samples()) {
          BOOST_LOG_TRIVIAL(error) << "Source " << source->get_num() << " has stopped receiving samples - Terminating trunk recorder";
          ctx.exit_flag = 1;
          ctx.exit_code = 1;
          break;
        }
      }
      last_decode_rate_check = now;
      for (auto &system : systems) {
        if (system->get_system_type() == "p25") {
          system->clear_stale_talkgroup_patches();
        }
      }
    }

    if ((now - last_status_time) > std::chrono::seconds(200)) {
      last_status_time = now;
      print_status(sources, systems, calls);
    }
  }
}
