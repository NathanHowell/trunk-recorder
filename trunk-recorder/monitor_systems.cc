#include "monitor_systems.h"
#include "call_state_manager.h"

using namespace std;

// File-local pointer for signal handler access to TrunkContext
static TrunkContext *g_ctx = nullptr;

void exit_interupt(int sig) { // can be called asynchronously
  if (g_ctx) g_ctx->exit_flag = 1;
}

using SteadyClock = std::chrono::steady_clock;
using TimePoint = SteadyClock::time_point;

void print_status(std::vector<std::shared_ptr<Source>> &sources, std::vector<std::shared_ptr<System>> &systems, std::vector<std::shared_ptr<Call>> &calls) {
  BOOST_LOG_TRIVIAL(info) << "Active Calls: " << calls.size();

  for (auto &call : calls) {
    auto recorder = call->get_recorder();
    std::string loghdr = log_header( call->get_short_name(), call->get_call_num(), call->get_talkgroup(), call->get_freq());
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
    if (!is_conventional(sys->get_system_type())) {
      BOOST_LOG_TRIVIAL(info) << "[" << sys->get_short_name() << "]\t" << format_freq(sys->get_current_control_channel()) << "\t" << sys->get_decode_rate() << " msg/sec";

      if ((sys->get_source()->get_autotune_source()) && (sys->get_system_type() == SYS_P25)) {
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

static void current_system_status(TrunkMessage message, const std::shared_ptr<System> &sys, const std::shared_ptr<EventSink> &event_sink) {
  if (sys->update_status(message)) {
    event_sink->setup_system(sys);
  }
}

static void current_system_sysid(TrunkMessage message, const std::shared_ptr<System> &sys, const std::shared_ptr<EventSink> &event_sink) {
  if ((sys->get_system_type() == SYS_P25) || (sys->get_system_type() == SYS_CONVENTIONAL_P25)) {
    if (sys->update_sysid(message)) {
      event_sink->setup_system(sys);
    }
  }
}

static void unit_registration(const std::shared_ptr<System> &sys, long source_id, const std::shared_ptr<EventSink> &event_sink) {
  event_sink->unit_registration(sys, source_id);
}

static void unit_deregistration(const std::shared_ptr<System> &sys, long source_id, const std::shared_ptr<EventSink> &event_sink) {
  event_sink->unit_deregistration(sys, source_id);
}

static void unit_acknowledge_response(const std::shared_ptr<System> &sys, long source_id, const std::shared_ptr<EventSink> &event_sink) {
  event_sink->unit_acknowledge_response(sys, source_id);
}

static void unit_group_affiliation(const std::shared_ptr<System> &sys, long source_id, long talkgroup_num, const std::shared_ptr<EventSink> &event_sink) {
  event_sink->unit_group_affiliation(sys, source_id, talkgroup_num);
}

static void unit_data_grant(const std::shared_ptr<System> &sys, long source_id, const std::shared_ptr<EventSink> &event_sink) {
  event_sink->unit_data_grant(sys, source_id);
}

static void unit_answer_request(const std::shared_ptr<System> &sys, long source_id, long talkgroup, const std::shared_ptr<EventSink> &event_sink) {
  event_sink->unit_answer_request(sys, source_id, talkgroup);
}

static void unit_location(const std::shared_ptr<System> &sys, long source_id, long talkgroup_num, const std::shared_ptr<EventSink> &event_sink) {
  event_sink->unit_location(sys, source_id, talkgroup_num);
}

static void handle_message(std::vector<TrunkMessage> messages, const std::shared_ptr<System> &sys, Config &config, CallStateManager &call_mgr, std::vector<std::shared_ptr<Source>> &sources, gr::top_block_sptr &tb) {
  for (std::vector<TrunkMessage>::iterator it = messages.begin(); it != messages.end(); it++) {
    TrunkMessage message = *it;

    switch (message.message_type) {
    case GRANT:
      call_mgr.handle_grant(message, sys, true);
      break;

    case UPDATE:
      if (config.new_call_from_update) {
        call_mgr.handle_grant(message, sys, false);
      } else {
        call_mgr.handle_update(message, sys);
      }
      break;

    case UU_V_GRANT:
      if (config.record_uu_v_calls) {
        call_mgr.handle_grant(message, sys, true);
      }
      break;

    case UU_V_UPDATE:
      if (config.record_uu_v_calls) {
        call_mgr.handle_update(message, sys);
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
      if (sys->get_source() && sys->get_source()->get_autotune_source() && sys->get_system_type() == SYS_P25) {
        autotune_control_channel(sys, false);
      }
      break;

    case UNKNOWN:
      break;
    }
  }
}


static void check_message_count(float timeDiff, Config &config, gr::top_block_sptr &tb, std::vector<std::shared_ptr<Source>> &sources, std::vector<std::shared_ptr<System>> &systems) {
  config.event_sink->setup_config(sources, systems);
  config.event_sink->system_rates(systems, timeDiff);

  for (auto &sys : systems) {
    if (!is_conventional(sys->get_system_type())) {
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
          if (sys->get_source() && sys->get_source()->get_autotune_source() && sys->get_system_type() == SYS_P25) {
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

static void check_conventional_channel_detection(std::vector<std::shared_ptr<Source>> &sources) {
  for (auto &source : sources) {
    source->enable_detected_recorders();
  }
}

// This is to handle the messages that come off the Analog recorder.
static void process_message_queues(std::vector<std::shared_ptr<System>> &systems) {
  for (auto &sys : systems) {
    for (auto &ar : sys->get_conventional_recorders()) {
      ar->process_message_queues();
    }
  }
}

int monitor_messages(TrunkContext &ctx) {
  g_ctx = &ctx;

  Config &config = ctx.config;
  gr::top_block_sptr &tb = ctx.tb;
  std::vector<std::shared_ptr<Source>> &sources = ctx.sources;
  std::vector<std::shared_ptr<System>> &systems = ctx.systems;

  // Move pre-existing conventional calls into the manager, then use it exclusively.
  CallStateManager call_mgr(config, sources);
  for (auto &call : ctx.calls) {
    call_mgr.active_calls_mut().push_back(std::move(call));
  }
  ctx.calls.clear();

  gr::message::sptr msg;

  auto now = SteadyClock::now();
  TimePoint last_status_time = now;
  TimePoint last_decode_rate_check = now;
  TimePoint management_timestamp = now;
  TimePoint last_conventional_channel_detection_check = now;
  std::vector<TrunkMessage> trunk_messages;
  std::map<int, std::unique_ptr<SmartnetParser>> smartnet_parsers;
  std::unique_ptr<P25Parser> p25_parser;

  signal(SIGINT, exit_interupt);

  if (systems.empty()) {
    BOOST_LOG_TRIVIAL(error) << "No systems configured, cannot start monitoring.";
    return 1;
  }
  for (auto &system : systems) {
    if (system->get_system_type() == SYS_SMARTNET) {
      smartnet_parsers[system->get_sys_num()] = std::make_unique<SmartnetParser>(system);
    }
  }
  p25_parser = std::make_unique<P25Parser>();

  while (1) {

    if (ctx.exit_flag) { // my action when signal set it 1
      BOOST_LOG_TRIVIAL(info) << "Caught an Exit Signal...";
      call_mgr.conclude_all();

      BOOST_LOG_TRIVIAL(info) << "Cleaning up & Exiting...";

      // Sleep for 5 seconds to allow for all of the Call Concluder threads to finish.
      std::this_thread::sleep_for(std::chrono::milliseconds(5000));
      return ctx.exit_code;
    }

    process_message_queues(systems);
    call_mgr.process_recorder_queues();

    config.event_sink->poll_one();

    for (auto &system : systems) {
      if ((system->get_system_type() == SYS_P25) || (system->get_system_type() == SYS_SMARTNET)) {
        msg.reset();
        msg = system->get_msg_queue()->delete_head_nowait();
        while (msg != 0) {
          system->set_message_count(system->get_message_count() + 1);

          if (system->get_system_type() == SYS_SMARTNET) {
            auto &smartnet_parser = smartnet_parsers[system->get_sys_num()];
            trunk_messages = smartnet_parser->parse_message(msg, system);
            handle_message(trunk_messages, system, config, call_mgr, sources, tb);
            config.event_sink->trunk_message(trunk_messages, system);
          }

          if (system->get_system_type() == SYS_P25) {
            trunk_messages = p25_parser->parse_message(msg, system);
            handle_message(trunk_messages, system, config, call_mgr, sources, tb);
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
      call_mgr.tick();
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
        if (system->get_system_type() == SYS_P25) {
          system->clear_stale_talkgroup_patches();
        }
      }
    }

    if ((now - last_status_time) > std::chrono::seconds(200)) {
      last_status_time = now;
      print_status(sources, systems, call_mgr.active_calls_mut());
    }
  }
}
