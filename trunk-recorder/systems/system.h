#ifndef SYSTEM_H
#define SYSTEM_H
#include <functional>
#include <memory>
#include "../global_structs.h"
#include "../unit_tags_ota.h"
#include <boost/log/trivial.hpp>
#include <gnuradio/msg_queue.h>
#include <gnuradio/top_block.h>
#include <stdio.h>
//#include "../source.h"
#include "parser.h"
#include "trunking_decoder.h"
#include <iomanip>

#ifdef __GNUC__
#pragma GCC diagnostic push
//#pragma GCC diagnostic ignored "-Wint-in-bool-context"
//#pragma GCC diagnostic ignored "-Wunused-local-typedefs"
#endif

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

class System {

public:
  static std::shared_ptr<System> make(int sys_id);
  virtual std::string get_short_name() = 0;
  virtual void set_short_name(std::string short_name) = 0;
  virtual void set_mdc_enabled(bool b) = 0;
  virtual void set_fsync_enabled(bool b) = 0;
  virtual void set_star_enabled(bool b) = 0;
  virtual void set_tps_enabled(bool b) = 0;

  virtual bool get_mdc_enabled() = 0;
  virtual bool get_fsync_enabled() = 0;
  virtual bool get_star_enabled() = 0;
  virtual bool get_tps_enabled() = 0;

  virtual void set_analog_levels(double r) = 0;
  virtual double get_analog_levels() = 0;
  virtual void set_qpsk_mod(bool m) = 0;
  virtual bool get_qpsk_mod() = 0;
  virtual void set_tau(float tau) = 0;
  virtual float get_tau() const = 0;
  virtual void set_max_dev(int max_dev) = 0;
  virtual int get_max_dev() = 0;
  virtual gr::msg_queue::sptr get_msg_queue() = 0;
  virtual SystemType get_system_type() = 0;
  virtual unsigned long get_sys_id() = 0;
  virtual unsigned long get_wacn() = 0;
  virtual void set_xor_mask(unsigned long sys_id, unsigned long wacn, unsigned long nac) = 0;
  virtual bool update_status(TrunkMessage message) = 0;
  virtual bool update_sysid(TrunkMessage message) = 0;
  virtual int get_sys_num() = 0;
  virtual void set_system_type(SystemType) = 0;
  virtual std::shared_ptr<Source> get_source() = 0;
  virtual void set_source(const std::shared_ptr<Source> &) = 0;
  virtual int control_channel_count() = 0;
  virtual void add_control_channel(double channel) = 0;
  virtual double get_next_control_channel() = 0;
  virtual double get_current_control_channel() = 0;
  virtual std::vector<double> get_control_channels() = 0;
  virtual void set_bandplan(std::string) = 0;
  virtual std::string get_bandplan() = 0;
  virtual void set_bandfreq(int) = 0;
  virtual int get_bandfreq() = 0;
  virtual void set_bandplan_base(double) = 0;
  virtual double get_bandplan_base() = 0;
  virtual void set_bandplan_high(double high) = 0;
  virtual double get_bandplan_high() = 0;
  virtual void set_bandplan_spacing(double) = 0;
  virtual double get_bandplan_spacing() = 0;
  virtual void set_bandplan_offset(int) = 0;
  virtual int get_bandplan_offset() = 0;

  virtual double get_control_channel_pwr() = 0;
  virtual int get_freq_error() = 0;
  virtual void finetune_control_freq(double f) = 0;
  virtual int get_autotune_offset() = 0;
  virtual void set_autotune_offset(int offset) = 0;

  virtual bool add_ota_unit_tag(const OTAAlias &ota_alias) = 0;

  virtual void setup_decoders(gr::top_block_sptr &tb, std::vector<std::shared_ptr<Source>> &sources) = 0;
  virtual void set_msg_callback(std::function<void(gr::message::sptr)> cb) {}
  virtual std::vector<std::shared_ptr<trunking_decoder>> get_decoders() = 0;
};
#endif
