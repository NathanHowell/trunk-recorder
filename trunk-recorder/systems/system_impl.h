#ifndef SYSTEM_IMPL_H
#define SYSTEM_IMPL_H
#include "../talkgroups.h"
#include "../unit_tags.h"
#include <boost/log/trivial.hpp>
#include <memory>
#include <stdio.h>
//#include "../source.h"
#include "parser.h"
#include "system.h"
#include "trunking_decoder.h"

#ifdef __GNUC__
#pragma GCC diagnostic push
//#pragma GCC diagnostic ignored "-Wint-in-bool-context"
//#pragma GCC diagnostic ignored "-Wunused-local-typedefs"
#endif

#include <lfsr/lfsr.h>

#ifdef __GNUC__
#pragma GCC diagnostic pop
#endif


class Source;
class analog_recorder;
class p25_recorder;
class dmr_recorder;
class sigmf_recorder;

typedef std::shared_ptr<analog_recorder> analog_recorder_sptr;
typedef std::shared_ptr<p25_recorder> p25_recorder_sptr;
typedef std::shared_ptr<dmr_recorder> dmr_recorder_sptr;
typedef std::shared_ptr<sigmf_recorder> sigmf_recorder_sptr;

class System_impl : public System {
  int sys_num;
  unsigned long sys_id;
  unsigned long wacn;
  unsigned long nac;
  int sys_rfss;
  int sys_site_id;

public:
  std::unique_ptr<Talkgroups> talkgroups;
  std::unique_ptr<UnitTags> unit_tags;
  std::unique_ptr<p25p2_lfsr> lfsr;
  std::shared_ptr<Source> source;
  std::string channel_file;
  std::string unit_tags_file;
  std::string unit_tags_ota_file;
  std::string unit_tags_mode;
  std::string custom_freq_table_file;
  std::string short_name;
  std::string default_mode;
  SystemType system_type;
  std::string bandplan;
  int bandfreq;
  double bandplan_base;
  double bandplan_high;
  double bandplan_spacing;
  int bandplan_offset;
  int max_dev;
  double filter_width;
  bool qpsk_mod;
  double squelch_db;
  float tau;
  double analog_levels;
  double digital_levels;

  std::string xor_mask;
  std::vector<double> control_channels;
  unsigned int current_control_channel;
  std::vector<double> channels;
  std::vector<analog_recorder_sptr> conventional_recorders;
  std::vector<p25_recorder_sptr> conventionalP25_recorders;
  std::vector<dmr_recorder_sptr> conventionalDMR_recorders;
  std::vector<sigmf_recorder_sptr> conventionalSIGMF_recorders;

  struct decoder_entry {
    std::shared_ptr<trunking_decoder> decoder;
    std::shared_ptr<Source> source;
    double freq;
  };
  std::vector<decoder_entry> decoders;

  std::string get_short_name() override;
  void set_short_name(std::string short_name) override;
  void set_mdc_enabled(bool b) override;
  void set_fsync_enabled(bool b) override;
  void set_star_enabled(bool b) override;
  void set_tps_enabled(bool b) override;

  bool get_mdc_enabled() override;
  bool get_fsync_enabled() override;
  bool get_star_enabled() override;
  bool get_tps_enabled() override;

  void set_analog_levels(double r) override;
  double get_analog_levels() override;
  void set_digital_levels(double r) override;
  double get_digital_levels() override;
  void set_qpsk_mod(bool m) override;
  bool get_qpsk_mod() override;
  void set_squelch_db(double s) override;
  double get_squelch_db() override;
  void set_tau(float tau) override;
  float get_tau() const override;
  void set_max_dev(int max_dev) override;
  int get_max_dev() override;
  void set_filter_width(double f) override;
  double get_filter_width() override;
  gr::msg_queue::sptr get_msg_queue() override;
  SystemType get_system_type() override;
  unsigned long get_sys_id() override;
  unsigned long get_wacn() override;
  unsigned long get_nac() override;
  int get_sys_rfss() override;
  int get_sys_site_id() override;
  void set_xor_mask(unsigned long sys_id, unsigned long wacn, unsigned long nac) override;
  const std::string& get_xor_mask() override;
  bool update_status(TrunkMessage message) override;
  bool update_sysid(TrunkMessage message) override;
  int get_sys_num() override;
  void set_system_type(SystemType) override;
  std::shared_ptr<Source> get_source() override;
  void set_source(const std::shared_ptr<Source> &) override;
  std::string find_unit_tag(long unitID) override;
  void add_unit_tag(std::string pattern, std::string tag) override;
  void set_channel_file(std::string channel_file) override;
  bool has_channel_file() override;
  void set_unit_tags_file(std::string) override;
  void set_unit_tags_ota_file(std::string) override;
  std::string get_unit_tags_ota_file() override;
  void set_unit_tags_mode(std::string mode) override;
  std::string get_unit_tags_mode() override;
  void set_custom_freq_table_file(std::string custom_freq_table_file) override;
  std::string get_custom_freq_table_file() override;
  bool has_custom_freq_table_file() override;
  int control_channel_count() override;
  void add_control_channel(double channel) override;
  double get_next_control_channel() override;
  double get_current_control_channel() override;
  int channel_count() override;
  void add_channel(double channel) override;
  void add_conventional_recorder(analog_recorder_sptr rec) override;
  void add_conventionalP25_recorder(p25_recorder_sptr rec) override;
  void add_conventionalSIGMF_recorder(sigmf_recorder_sptr rec) override;
  void add_conventionalDMR_recorder(dmr_recorder_sptr rec) override;
  std::vector<p25_recorder_sptr> get_conventionalP25_recorders() override;
  std::vector<analog_recorder_sptr> get_conventional_recorders() override;
  std::vector<sigmf_recorder_sptr> get_conventionalSIGMF_recorders() override;
  std::vector<dmr_recorder_sptr> get_conventionalDMR_recorders() override;
  std::vector<double> get_channels() override;
  std::vector<double> get_control_channels() override;
  void add_talkgroup(std::shared_ptr<Talkgroup> tg) override;
  std::vector<std::shared_ptr<Talkgroup>> get_talkgroups() override;
  gr::msg_queue::sptr msg_queue;
  System_impl(int sys_id);
  void set_bandplan(std::string) override;
  std::string get_bandplan() override;
  void set_bandfreq(int) override;
  int get_bandfreq() override;
  void set_bandplan_base(double) override;
  double get_bandplan_base() override;
  void set_bandplan_high(double high) override;
  double get_bandplan_high() override;
  void set_bandplan_spacing(double) override;
  double get_bandplan_spacing() override;
  void set_bandplan_offset(int) override;
  int get_bandplan_offset() override;

  double get_control_channel_pwr() override;
  int get_freq_error() override;
  void finetune_control_freq(double f) override;
  int get_autotune_offset() override;
  void set_autotune_offset(int offset) override;

  bool add_ota_unit_tag(const OTAAlias &ota_alias) override;
  void setup_decoders(gr::top_block_sptr &tb, std::vector<std::shared_ptr<Source>> &sources) override;
  void set_msg_callback(std::function<void(gr::message::sptr)> cb) override;
  std::vector<std::shared_ptr<trunking_decoder>> get_decoders() override;

private:
  bool d_mdc_enabled;
  bool d_fsync_enabled;
  bool d_star_enabled;
  bool d_tps_enabled;
  std::function<void(gr::message::sptr)> d_msg_cb;
};
#endif
