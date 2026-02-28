#include "call_state_manager.h"
#include "event_sink.h"
#include "formatter.h"
#include "recorders/p25_recorder.h"

using namespace std;

CallStateManager::CallStateManager(Config &config, std::vector<std::shared_ptr<Source>> &sources)
    : config_(config), sources_(sources) {}

// ---------------------------------------------------------------------------
// try_start_recording — attempt to assign a recorder to a call
// ---------------------------------------------------------------------------

bool CallStateManager::try_start_recording(const std::shared_ptr<Call> &call,
                                           TrunkMessage message,
                                           const std::shared_ptr<System> &sys) {
  auto talkgroup = sys->find_talkgroup(call->get_talkgroup());

  bool source_found = false;
  bool recorder_found = false;
  bool override_record_unknown = false;

  std::shared_ptr<Recorder> recorder;
  std::shared_ptr<Recorder> debug_recorder;
  std::shared_ptr<Recorder> sigmf_recorder;

  if (!talkgroup) {
    for (auto &TGID : sys->get_talkgroup_patch(call->get_talkgroup())) {
      if (sys->find_talkgroup(TGID) != nullptr) {
        override_record_unknown = true;
        std::string loghdr = log_header(call->get_short_name(), call->get_call_num(), call->get_talkgroup(), call->get_freq());
        BOOST_LOG_TRIVIAL(info) << loghdr << "\u001b[33mEnabling recording of TG not in Talkgroup File due to active supergroup patch\u001b[0m ";
      }
    }
  }

  if (!talkgroup && (sys->get_record_unknown() == false) && override_record_unknown == false) {
    call->set_state(MONITORING);
    call->set_monitoring_state(UNKNOWN_TG);
    if (sys->get_hideUnknown() == false) {
      std::string loghdr = log_header(call->get_short_name(), call->get_call_num(), call->get_talkgroup(), call->get_freq());
      BOOST_LOG_TRIVIAL(info) << loghdr << "\u001b[33mNot Recording: TG not in Talkgroup File\u001b[0m ";
    }
    return false;
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
        std::string loghdr = log_header(sys->get_short_name(), call->get_call_num(), call->get_talkgroup(), call->get_freq());
        BOOST_LOG_TRIVIAL(info) << loghdr << "\u001b[31mNot Recording: ENCRYPTED\u001b[0m - src: " << unit_id << tag;
      }
      return false;
    }
  }

  for (auto &source : sources_) {
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
        std::string loghdr = log_header(call->get_short_name(), call->get_call_num(), call->get_talkgroup(), call->get_freq());
        BOOST_LOG_TRIVIAL(info) << loghdr << "TG not in Talkgroup File ";

        if ((config_.default_mode == "analog") && (sys->get_system_type() == SYS_SMARTNET)) {
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
          config_.event_sink->setup_recorder(recorder);
          recorder_found = true;
        } else {
          call->set_state(MONITORING);
          recorder_found = false;
          return false;
        }
      } else {
        return false;
      }

      debug_recorder = source->get_debug_recorder();
      if (debug_recorder) {
        debug_recorder->start(call);
        call->set_debug_recorder(debug_recorder);
        call->set_debug_recording(true);
        config_.event_sink->setup_recorder(debug_recorder);
        recorder_found = true;
      }

      sigmf_recorder = source->get_sigmf_recorder();
      if (sigmf_recorder) {
        sigmf_recorder->start(call);
        call->set_sigmf_recorder(sigmf_recorder);
        call->set_sigmf_recording(true);
        config_.event_sink->setup_recorder(sigmf_recorder);
        recorder_found = true;
      }

      if (recorder_found) {
        return true;
      }
    }
  }

  if (!source_found) {
    call->set_state(MONITORING);
    call->set_monitoring_state(NO_SOURCE);
    std::string loghdr = log_header(call->get_short_name(), call->get_call_num(), call->get_talkgroup(), call->get_freq());
    BOOST_LOG_TRIVIAL(error) << loghdr << "\u001b[36mNot Recording: no source covering Freq\u001b[0m";
    return false;
  }
  return false;
}

// ---------------------------------------------------------------------------
// check_multisite — detect duplicate/superseding grants across multi-site systems
// ---------------------------------------------------------------------------

CallStateManager::MultiSiteResult
CallStateManager::check_multisite(long talkgroup, int sys_num,
                                  const std::shared_ptr<System> &sys) {
  MultiSiteResult result;

  unsigned long message_preferredNAC = 0;
  auto message_talkgroup = sys->find_talkgroup(talkgroup);
  if (message_talkgroup) {
    message_preferredNAC = message_talkgroup->get_preferredNAC();
  }

  for (auto &call : calls_) {
    if (call->get_talkgroup() != talkgroup)
      continue;
    if (call->get_sys_num() == sys_num)
      continue;
    if (!call->get_system()->get_multiSite() || !sys->get_multiSite())
      continue;
    if (call->get_system()->get_wacn() != sys->get_wacn())
      continue;

    unsigned long sys_rfss_site = sys->get_sys_rfss() * 10000 + sys->get_sys_site_id();
    unsigned long call_rfss_site = call->get_system()->get_sys_rfss() * 10000 + call->get_system()->get_sys_site_id();

    // Default mode: match WACN, use RFSS/Site to identify duplicates
    if ((sys_rfss_site != call_rfss_site) && (call->get_system()->get_multiSiteSystemName() == "")) {
      if (call->get_state() == RECORDING) {
        result.is_duplicate = true;
        result.original_call = call;

        unsigned long call_preferredNAC = 0;
        auto call_talkgroup = call->get_system()->find_talkgroup(talkgroup);
        if (call_talkgroup) {
          call_preferredNAC = call_talkgroup->get_preferredNAC();
        }

        if ((call_preferredNAC != call->get_system()->get_nac()) && (message_preferredNAC == sys->get_nac())) {
          result.is_superseding = true;
        } else if ((call_preferredNAC != call_rfss_site) && (message_preferredNAC == sys_rfss_site)) {
          result.is_superseding = true;
        }
      }
    }
    // Secondary mode: match multiSiteSystemName
    else if ((call->get_system()->get_multiSiteSystemName() != "") && (call->get_system()->get_multiSiteSystemName() == sys->get_multiSiteSystemName())) {
      if (call->get_state() == RECORDING) {
        result.is_duplicate = true;
        result.original_call = call;

        unsigned long call_preferredNAC = 0;
        auto call_talkgroup = call->get_system()->find_talkgroup(talkgroup);
        if (call_talkgroup) {
          call_preferredNAC = call_talkgroup->get_preferredNAC();
        }

        if ((call->get_system()->get_multiSiteSystemNumber() != 0) && (sys->get_multiSiteSystemNumber() != 0)) {
          if ((call_preferredNAC != call->get_system()->get_multiSiteSystemNumber()) && (message_preferredNAC == sys->get_multiSiteSystemNumber())) {
            result.is_superseding = true;
          }
        }
      }
    }
  }

  return result;
}

// ---------------------------------------------------------------------------
// handle_grant — process a GRANT (or UPDATE-as-grant) from the control channel
// ---------------------------------------------------------------------------

void CallStateManager::handle_grant(TrunkMessage message,
                                    const std::shared_ptr<System> &sys,
                                    bool is_grant_message) {
  bool call_found = false;
  bool recording_started [[maybe_unused]] = false;

  auto multisite = check_multisite(message.talkgroup, message.sys_num, sys);

  for (auto &call : calls_) {
    // Exact match — update existing call
    if ((call->get_talkgroup() == message.talkgroup) && (call->get_sys_num() == message.sys_num) && (call->get_freq() == message.freq) && (call->get_tdma_slot() == message.tdma_slot) && (call->get_phase2_tdma() == message.phase2_tdma)) {
      call_found = true;
      bool source_updated = call->update(message);
      if (source_updated) {
        config_.event_sink->call_start(call);
      }
    }

    // Overlapping frequency with different talkgroup — log warning
    if ((call->get_state() == RECORDING) && (call->get_talkgroup() != message.talkgroup) && (call->get_sys_num() == message.sys_num) && (call->get_freq() == message.freq) && (call->get_tdma_slot() == message.tdma_slot) && (call->get_phase2_tdma() == message.phase2_tdma)) {
      auto recorder = call->get_recorder();
      string recorder_state = "UNKNOWN";
      if (recorder) {
        recorder_state = format_state(recorder->get_state());
      }
      std::string loghdr = log_header(call->get_short_name(), call->get_call_num(), call->get_talkgroup(), call->get_freq());
      BOOST_LOG_TRIVIAL(trace) << loghdr << "\u001b[36mShould be Stopping RECORDING call, Recorder State: " << recorder_state << " RX overlapping TG message Freq, TG:" << message.talkgroup << "\u001b[0m";
    }
  }

  if (call_found) {
    return;
  }

  // --- New call ---

  auto call = Call::make(message, sys, config_);
  auto talkgroup = sys->find_talkgroup(call->get_talkgroup());

  boost::format original_call_data;
  boost::format grant_call_data;

  if (multisite.is_superseding || multisite.is_duplicate) {
    if (multisite.original_call->get_system()->get_multiSiteSystemName() == "") {
      original_call_data = boost::format("\u001b[34m%sC\u001b[0m %X/%s-%s ") % multisite.original_call->get_call_num() % multisite.original_call->get_system()->get_wacn() % multisite.original_call->get_system()->get_sys_rfss() % multisite.original_call->get_system()->get_sys_site_id();
      grant_call_data = boost::format("\u001b[34m%sC\u001b[0m %X/%s-%s ") % call->get_call_num() % sys->get_wacn() % sys->get_sys_rfss() % +sys->get_sys_site_id();
    } else {
      original_call_data = boost::format("\u001b[34m%sC\u001b[0m %s/%s ") % multisite.original_call->get_call_num() % multisite.original_call->get_system()->get_multiSiteSystemName() % multisite.original_call->get_system()->get_multiSiteSystemNumber();
      grant_call_data = boost::format("\u001b[34m%sC\u001b[0m %s/%s ") % call->get_call_num() % sys->get_multiSiteSystemName() % sys->get_multiSiteSystemNumber();
    }
  }

  if (multisite.is_superseding) {
    std::string loghdr = log_header(call->get_short_name(), call->get_call_num(), call->get_talkgroup(), call->get_freq());
    BOOST_LOG_TRIVIAL(info) << loghdr << "\u001b[36mSuperseding Grant\u001b[0m - Stopping original call: " << original_call_data << "- Superseding call: " << grant_call_data;
    recording_started = try_start_recording(call, message, sys);

    if (recording_started) {
      multisite.original_call->set_state(MONITORING);
      multisite.original_call->set_monitoring_state(SUPERSEDED);
      multisite.original_call->conclude_call();
    } else {
      BOOST_LOG_TRIVIAL(info) << loghdr << "\u001b[36mCould not start Superseding recorder.\u001b[0m Continuing original call: " << multisite.original_call->get_call_num() << "C";
    }
  } else if (multisite.is_duplicate) {
    std::string loghdr = log_header(call->get_short_name(), call->get_call_num(), call->get_talkgroup(), call->get_freq());
    call->set_state(MONITORING);
    call->set_monitoring_state(DUPLICATE);
    BOOST_LOG_TRIVIAL(info) << loghdr << "\u001b[36mDuplicate Grant\u001b[0m - Not recording: " << grant_call_data << "- Original call: " << original_call_data;
  } else {
    recording_started = try_start_recording(call, message, sys);
    if (recording_started && !is_grant_message) {
      std::string loghdr = log_header(call->get_short_name(), call->get_call_num(), call->get_talkgroup(), call->get_freq());
      BOOST_LOG_TRIVIAL(info) << loghdr << "\u001b[36mThis was an UPDATE\u001b[0m";
    }
  }

  calls_.push_back(call);
  config_.event_sink->call_start(call);
  config_.event_sink->calls_active(calls_);
}

// ---------------------------------------------------------------------------
// handle_update — process an UPDATE message for an existing call
// ---------------------------------------------------------------------------

void CallStateManager::handle_update(TrunkMessage message,
                                     const std::shared_ptr<System> &sys) {
  bool call_found = false;

  for (auto &call : calls_) {
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
        config_.event_sink->call_start(call);
      }
    }
  }

  if (!call_found) {
    // Note: some calls may be removed before the UPDATEs stop on the trunking
    // channel if there is some gap in the updates.
  }
}

// ---------------------------------------------------------------------------
// conclude_and_erase — conclude a call, erase from vector, advance iterator
// ---------------------------------------------------------------------------

void CallStateManager::conclude_and_erase(
    std::vector<std::shared_ptr<Call>>::iterator &it, bool &ended_call) {
  auto &call = *it;
  auto recorder = call->get_recorder();
  call->conclude_call();
  ended_call = true;
  if (recorder) {
    config_.event_sink->setup_recorder(recorder);
  }
  it = calls_.erase(it);
}

// ---------------------------------------------------------------------------
// manage_trunked_call — timeout logic for a single trunked call
// ---------------------------------------------------------------------------

void CallStateManager::manage_trunked_call(
    std::vector<std::shared_ptr<Call>>::iterator &it, bool &ended_call) {
  auto &call = *it;
  State state = call->get_state();

  // MONITORING calls: end when the control channel stops mentioning them.
  if ((state == MONITORING) && (call->since_last_update() > config_.call_timeout)) {
    call->conclude_call();
    ended_call = true;
    it = calls_.erase(it);
    return;
  }

  // RECORDING calls: end when either the recorder goes idle OR the control
  // channel stops mentioning them.
  if (state == RECORDING) {
    auto recorder = call->get_recorder();
    if (recorder && (recorder->since_last_write() > config_.call_timeout || call->since_last_update() > config_.call_timeout)) {
      std::string loghdr = log_header(call->get_short_name(), call->get_call_num(), call->get_talkgroup(), call->get_freq());
      BOOST_LOG_TRIVIAL(trace) << loghdr << "\u001b[36m Stopping Call because of Recorder \u001b[0m Rec last write: " << recorder->since_last_write().count() << "s State: " << format_state(recorder->get_state());
      conclude_and_erase(it, ended_call);
      return;
    }
  }
  // Any other state that has timed out: conclude and remove.
  else if (call->since_last_update() > config_.call_timeout) {
    auto recorder = call->get_recorder();
    std::string loghdr = log_header(call->get_short_name(), call->get_call_num(), call->get_talkgroup(), call->get_freq());
    if (recorder) {
      BOOST_LOG_TRIVIAL(trace) << loghdr << "\u001b[36m  Concluding stale call \u001b[0m Rec last write: " << recorder->since_last_write().count() << "s State: " << format_state(recorder->get_state());
    } else {
      BOOST_LOG_TRIVIAL(trace) << loghdr << "\u001b[36m  Concluding stale call \u001b[0m (no recorder)";
    }
    call->conclude_call();
    ended_call = true;
    it = calls_.erase(it);
    return;
  }

  ++it;
}

// ---------------------------------------------------------------------------
// manage_conventional_call — idle detection and restart for conventional calls
// ---------------------------------------------------------------------------

void CallStateManager::manage_conventional_call(const std::shared_ptr<Call> &call) {
  if (!call->get_recorder()) {
    return;
  }

  if (call->get_current_length() > 0) {
    BOOST_LOG_TRIVIAL(trace) << "[" << call->get_short_name() << "]\t\033[0;34m" << call->get_call_num() << "C\033[0m Call Length: " << call->get_current_length() << "s\t Idle: " << call->get_recorder()->is_idle() << "\t Squelched: " << call->get_recorder()->is_squelched() << " Idle Count: " << call->get_idle_count();

    if (call->get_recorder()->is_idle()) {
      call->set_noise(call->get_recorder()->get_pwr());
      call->increase_idle_count();
    } else {
      call->set_signal(call->get_recorder()->get_pwr());
      if (call->get_idle_count() > 0) {
        call->reset_idle_count();
      }
    }

    if (call->get_idle_count() > config_.call_timeout.count()) {
      auto recorder = call->get_recorder();
      call->conclude_call();
      call->restart_call();
      if (recorder) {
        config_.event_sink->setup_recorder(recorder);
        config_.event_sink->call_start(call);
      }
    } else if ((call->get_current_length() > call->get_system()->get_max_duration()) && (call->get_system()->get_max_duration() > 0)) {
      auto recorder = call->get_recorder();
      call->conclude_call();
      call->restart_call();
      if (recorder) {
        config_.event_sink->setup_recorder(recorder);
        config_.event_sink->call_start(call);
      }
    }
  } else if (!call->get_recorder()->is_active()) {
    auto recorder = call->get_recorder();
    recorder->start(call);
    call->set_state(RECORDING);
    config_.event_sink->call_start(call);
    BOOST_LOG_TRIVIAL(trace) << "[" << call->get_short_name() << "]\t\033[0;34m" << call->get_call_num() << "C\033[0m Starting P25 Convetional Recorder ";
  }
}

// ---------------------------------------------------------------------------
// tick — periodic call management, called every ~1 second
// ---------------------------------------------------------------------------

void CallStateManager::tick() {
  bool ended_call = false;

  for (auto it = calls_.begin(); it != calls_.end();) {
    auto &call = *it;

    if (call->is_conventional()) {
      manage_conventional_call(call);
      ++it;
      continue;
    }

    manage_trunked_call(it, ended_call);
  }

  if (ended_call) {
    config_.event_sink->calls_active(calls_);
  }
}

// ---------------------------------------------------------------------------
// conclude_all — shut down all active calls
// ---------------------------------------------------------------------------

void CallStateManager::conclude_all() {
  for (auto &call : calls_) {
    if (call->get_state() != MONITORING) {
      call->conclude_call();
    }
  }
  calls_.clear();
}

// ---------------------------------------------------------------------------
// process_recorder_queues — process message queues for recording calls
// ---------------------------------------------------------------------------

void CallStateManager::process_recorder_queues() {
  for (auto &call : calls_) {
    if (call->get_state() == RECORDING) {
      auto recorder = call->get_recorder();
      if (recorder && (recorder->get_type() == P25 || recorder->get_type() == P25C)) {
        auto p25_rec = std::dynamic_pointer_cast<p25_recorder>(recorder);
        if (p25_rec && (p25_rec->is_active())) {
          p25_rec->process_message_queues();
        }
      }
    }
  }
}
