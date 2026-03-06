#include "./setup_systems.h"
#include "event_sink.h"
#include "recorder_config.h"
using namespace std;
bool setup_conventional_channel(const std::shared_ptr<System> &system, double frequency, long channel_index, Config &config, gr::top_block_sptr &tb, std::vector<std::shared_ptr<Source>> &sources, std::vector<std::shared_ptr<Call>> &calls) {
  bool channel_added = false;
  std::shared_ptr<Source> source;
  float tone_freq = 0.0;
  for (auto src_it = sources.begin(); src_it != sources.end(); src_it++) {
    source = *src_it;

    if ((source->get_min_hz() <= frequency) && (source->get_max_hz() >= frequency)) {
      channel_added = true;
      if (system->get_squelch_db() == -160) {
        BOOST_LOG_TRIVIAL(error) << "[" << system->get_short_name() << "]\tSquelch needs to be specified for the Source for Conventional Systems";
        return false;
      } else {
        channel_added = true;
      }

      std::shared_ptr<Call_conventional> call;
      auto tg = system->find_talkgroup_by_freq(frequency);
      if (tg) {
        tone_freq = tg->tone;

        // If there is a per channel squelch setting, use it, otherwise use the system squelch setting
        if (tg->squelch_db != DB_UNSET) {
          call = std::make_shared<Call_conventional>(tg->number, tg->freq, system, config, tg->squelch_db, tg->signal_detection);
        } else {
          call = std::make_shared<Call_conventional>(tg->number, tg->freq, system, config, system->get_squelch_db(), tg->signal_detection);
        }

      } else {
        call = std::make_shared<Call_conventional>(channel_index, frequency, system, config, system->get_squelch_db(), true);  // signal detection is always true when a channel file is not used
      }

      BOOST_LOG_TRIVIAL(info) << "[" << system->get_short_name() << "]\tMonitoring " << system_type_to_string(system->get_system_type()) << " channel: " << format_freq(frequency) << " Talkgroup: " << channel_index;
      if (system->get_system_type() == SYS_CONVENTIONAL) {
        analog_recorder_sptr rec;
        if (tone_freq > 0.0) {
          rec = source->create_conventional_recorder(tb, tone_freq);
        } else {
          rec = source->create_conventional_recorder(tb);
        }
        rec->start(RecorderConfig{
            .talkgroup = call->get_talkgroup(),
            .call_num = call->get_call_num(),
            .freq = call->get_freq(),
            .short_name = call->get_short_name(),
            .temp_dir = config.temp_dir,
            .squelch_db = call->get_squelch_db(),
            .digital_levels = system->get_digital_levels(),
        });
        rec->set_tau(system->get_tau()); //set the tau value for the recorder from the system config
        call->set_recorder(rec);
        system->add_conventional_recorder(rec);
        calls.push_back(call);
        config.event_sink->setup_recorder(rec);
      } else if (system->get_system_type() == SYS_CONVENTIONAL_DMR) {
        // Because of dynamic mod assignment we can not start the recorder until the graph has been unlocked.
        // This has something to do with the way the Selector block works.
        // the manage_conventional_calls() function handles adding and starting the P25 Recorder
        dmr_recorder_sptr rec;
        rec = source->create_dmr_conventional_recorder(tb);
        call->set_recorder(rec);
        system->add_conventionalDMR_recorder(rec);
        calls.push_back(call);
      } else if (system->get_system_type() == SYS_CONVENTIONAL_P25) {
        // Because of dynamic mod assignment we can not start the recorder until the graph has been unlocked.
        // This has something to do with the way the Selector block works.
        // the manage_conventional_calls() function handles adding and starting the P25 Recorder
        p25_recorder_sptr rec;
        rec = source->create_digital_conventional_recorder(tb);
        call->set_recorder(rec);
        system->add_conventionalP25_recorder(rec);
        calls.push_back(call);
      } else if (system->get_system_type() == SYS_CONVENTIONAL_SIGMF) {
        sigmf_recorder_sptr rec;
        rec = source->create_sigmf_conventional_recorder(tb);
        call->set_recorder(rec);
        system->add_conventionalSIGMF_recorder(rec);
        calls.push_back(call);
      } else {
        BOOST_LOG_TRIVIAL(error) << "Error - Unknown system type: " << system_type_to_string(system->get_system_type());
      }

      // break out of the for loop
      break;
    }
  }
  return channel_added;
}

bool setup_conventional_system(const std::shared_ptr<System> &system, Config &config, gr::top_block_sptr &tb, std::vector<std::shared_ptr<Source>> &sources, std::vector<std::shared_ptr<Call>> &calls) {
  bool system_added = false;

  auto talkgroups = system->get_talkgroups();
  if (!talkgroups.empty()) {
    for (auto tg_it = talkgroups.begin(); tg_it != talkgroups.end(); tg_it++) {
      auto &tg = *tg_it;

      bool channel_added = setup_conventional_channel(system, tg->freq, tg->number, config, tb, sources, calls);

      if (!channel_added) {
        BOOST_LOG_TRIVIAL(error) << "[" << system->get_short_name() << "]\t Unable to find a source for this conventional channel! Channel not added: " << format_freq(tg->freq) << " Talkgroup: " << tg->number;
        // return false;
      } else {
        system_added = true;
      }
    }
  } else {
    std::vector<double> channels = system->get_channels();
    int channel_index = 0;
    for (vector<double>::iterator chan_it = channels.begin(); chan_it != channels.end(); chan_it++) {
      double channel = *chan_it;
      ++channel_index;
      bool channel_added = setup_conventional_channel(system, channel, channel_index, config, tb, sources, calls);

      if (!channel_added) {
        BOOST_LOG_TRIVIAL(error) << "[" << system->get_short_name() << "]\t Unable to find a source for this conventional channel! Channel not added: " << format_freq(channel) << " Talkgroup: " << channel_index;
        // return false;
      } else {
        system_added = true;
      }
    }
  }
  return system_added;
}

bool setup_systems(Config &config, gr::top_block_sptr &tb, std::vector<std::shared_ptr<Source>> &sources, std::vector<std::shared_ptr<System>> &systems, std::vector<std::shared_ptr<Call>> &calls) {

  for (auto &system : systems) {
    bool system_added = false;
    if (is_conventional(system->get_system_type())) {
      system_added = setup_conventional_system(system, config, tb, sources, calls);
    } else {
      // Trunking system — create one decoder per control channel
      system->setup_decoders(tb, sources);
      system_added = (system->get_decoders().size() > 0);
      if (!system_added) {
        BOOST_LOG_TRIVIAL(error) << "[" << system->get_short_name() << "]\t No sources cover any control channel";
        return false;
      }
    }
  }
  return true;
}
