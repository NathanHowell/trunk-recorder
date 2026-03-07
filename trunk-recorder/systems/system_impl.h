#ifndef SYSTEM_IMPL_H
#define SYSTEM_IMPL_H
#include "../unit_tags.h"
#include <boost/log/trivial.hpp>
#include <memory>
#include <stdio.h>
//#include "../source.h"
#include "parser.h"
#include "system.h"
#include "trunking_decoder.h"

class Source;

class System_impl : public System {
  int sys_num;
  unsigned long sys_id;
  unsigned long wacn;
  bool sysid_received;
  bool status_received;

public:
  std::unique_ptr<UnitTags> unit_tags;
  std::shared_ptr<Source> source;
  std::string short_name;
  SystemType system_type;
  std::string bandplan;
  int bandfreq;
  double bandplan_base;
  double bandplan_high;
  double bandplan_spacing;
  int bandplan_offset;
  int max_dev;
  bool qpsk_mod;
  float tau;
  double analog_levels;

  std::vector<double> control_channels;
  unsigned int current_control_channel;

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
  void set_qpsk_mod(bool m) override;
  bool get_qpsk_mod() override;
  void set_tau(float tau) override;
  float get_tau() const override;
  void set_max_dev(int max_dev) override;
  int get_max_dev() override;
  gr::msg_queue::sptr get_msg_queue() override;
  SystemType get_system_type() override;
  unsigned long get_sys_id() override;
  unsigned long get_wacn() override;
  void set_xor_mask(unsigned long sys_id, unsigned long wacn, unsigned long nac) override;
  bool update_status(TrunkMessage message) override;
  bool update_sysid(TrunkMessage message) override;
  int get_sys_num() override;
  void set_system_type(SystemType) override;
  std::shared_ptr<Source> get_source() override;
  void set_source(const std::shared_ptr<Source> &) override;
  int control_channel_count() override;
  void add_control_channel(double channel) override;
  double get_next_control_channel() override;
  double get_current_control_channel() override;
  std::vector<double> get_control_channels() override;
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
