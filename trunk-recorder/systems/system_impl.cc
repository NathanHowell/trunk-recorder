#include "system_impl.h"
#include "system.h"
#include "p25_trunking.h"
#include "smartnet_impl.h"
#include "../source.h"
#include "../formatter.h"

#include <limits>

std::shared_ptr<System> System::make(int sys_num) {
  return std::make_shared<System_impl>(sys_num);
}

std::string System_impl::get_short_name() {
  return this->short_name;
}

void System_impl::set_short_name(std::string short_name) {
  this->short_name = short_name;
}

System_impl::System_impl(int sys_num) {
  this->sys_num = sys_num;
  sys_id = 0;
  wacn = 0;
  nac = 0;
  sys_rfss = 0;
  sys_site_id = 0;
  current_control_channel = 0;
  // Setup the talkgroups from the CSV file
  talkgroups = std::make_unique<Talkgroups>();
  // Setup the unit tags from the CSV file
  unit_tags = std::make_unique<UnitTags>();
  d_mdc_enabled = false;
  d_fsync_enabled = false;
  d_star_enabled = false;
  d_tps_enabled = false;
  msg_queue = gr::msg_queue::make(100);
}

void System_impl::set_xor_mask(unsigned long sys_id, unsigned long wacn, unsigned long nac) {
  if (sys_id && wacn && nac) {
    this->sys_id = sys_id;
    this->wacn = wacn;
    this->nac = nac;
    BOOST_LOG_TRIVIAL(info) << "Setting XOR Mask: System_impl ID " << std::dec << sys_id << " WACN: " << wacn << " NAC: " << nac << std::dec;
    if (sys_id && wacn && nac) {
      lfsr = std::make_unique<p25p2_lfsr>(nac, sys_id, wacn);
      xor_mask = lfsr->getXorChars();

      BOOST_LOG_TRIVIAL(info) << "XOR Mask len: " << xor_mask.size();
      for (unsigned i = 0; i < xor_mask.size(); i++) {
        std::cout << (short)xor_mask[i] << ", ";
      }
    }
  }
}
bool System_impl::update_status(TrunkMessage message) {
  if (!sys_id || !wacn || !nac) {
    sys_id = message.sys_id;
    wacn = message.wacn;
    nac = message.nac;
    BOOST_LOG_TRIVIAL(info) << "[" << short_name << "]\tDecoding System ID "
                            << std::hex << std::uppercase << message.sys_id << " WACN: "
                            << std::hex << std::uppercase << message.wacn << " NAC: " << std::hex << std::uppercase << message.nac;
    if (sys_id && wacn && nac) {
      lfsr = std::make_unique<p25p2_lfsr>(nac, sys_id, wacn);
      xor_mask = lfsr->getXorChars();
    }
    return true;
  }
  return false;
}

bool System_impl::update_sysid(TrunkMessage message) {
  if (!sys_rfss || !sys_site_id) {
    sys_rfss = message.sys_rfss;
    sys_site_id = message.sys_site_id;
    BOOST_LOG_TRIVIAL(info) << "[" << short_name << "]\tDecoding System Site"
                            << " RFSS: " << std::setw(3) << std::setfill('0') << message.sys_rfss
                            << " SITE ID: " << std::setw(3) << std::setfill('0') << message.sys_site_id
                            << " (" << std::setw(3) << std::setfill('0') << message.sys_rfss << "-" << std::setw(3) << std::setfill('0') << message.sys_site_id << ")";
    return true;
  }
  return false;
}

 gr::msg_queue::sptr System_impl::get_msg_queue() {
  return msg_queue;
 }

const std::string& System_impl::get_xor_mask() {
  return xor_mask;
}

int System_impl::get_sys_num() {
  return this->sys_num;
}

unsigned long System_impl::get_sys_id() {
  return this->sys_id;
}

unsigned long System_impl::get_nac() {
  return this->nac;
}

unsigned long System_impl::get_wacn() {
  return this->wacn;
}

int System_impl::get_sys_rfss(){
  return this->sys_rfss;
}

int System_impl::get_sys_site_id(){
  return this->sys_site_id;
}


void System_impl::set_tau(float t){
  tau = t;
}

float System_impl::get_tau() const{
  return tau;
}


void System_impl::set_max_dev(int max_dev) {
  this->max_dev = max_dev;
}

int System_impl::get_max_dev() {
  return max_dev;
}

void System_impl::set_analog_levels(double r) {
  analog_levels = r;
}

double System_impl::get_analog_levels() {
  return analog_levels;
}


void System_impl::set_qpsk_mod(bool m) {
  qpsk_mod = m;
}

bool System_impl::get_qpsk_mod() {
  return qpsk_mod;
}

void System_impl::set_mdc_enabled(bool b) { d_mdc_enabled = b; };
void System_impl::set_fsync_enabled(bool b) { d_fsync_enabled = b; };
void System_impl::set_star_enabled(bool b) { d_star_enabled = b; };
void System_impl::set_tps_enabled(bool b) { d_tps_enabled = b; }

bool System_impl::get_mdc_enabled() { return d_mdc_enabled; };
bool System_impl::get_fsync_enabled() { return d_fsync_enabled; };
bool System_impl::get_star_enabled() { return d_star_enabled; };
bool System_impl::get_tps_enabled() { return d_tps_enabled; };

SystemType System_impl::get_system_type() {
  return this->system_type;
}

void System_impl::set_system_type(SystemType sys_type) {
  this->system_type = sys_type;
}


void System_impl::set_unit_tags_ota_file(std::string unit_tags_ota_file) {
  this->unit_tags_ota_file = unit_tags_ota_file;
  this->unit_tags->load_unit_tags_ota(unit_tags_ota_file);
}

std::string System_impl::get_unit_tags_ota_file() {
  return this->unit_tags_ota_file;
}

void System_impl::set_unit_tags_mode(std::string mode) {
  this->unit_tags_mode = mode;
  if (mode == "ota" || mode == "OTA") {
    this->unit_tags->set_mode(TAG_OTA_FIRST);
  } else if (mode == "user_only") {
    this->unit_tags->set_mode(TAG_USER_ONLY);
  } else if (mode == "none") {
    this->unit_tags->set_mode(TAG_NONE);
  } else {
    this->unit_tags->set_mode(TAG_USER_FIRST);
  }
}

std::string System_impl::get_unit_tags_mode() {
  return this->unit_tags_mode;
}

void System_impl::set_custom_freq_table_file(std::string custom_freq_table_file) {
  this->custom_freq_table_file = custom_freq_table_file;
}

std::string System_impl::get_custom_freq_table_file(){
  return this->custom_freq_table_file;
}

bool System_impl::has_custom_freq_table_file() {
    if (this->custom_freq_table_file.length() > 0) {
    return true;
  } else {
    return false;
  }
}

std::shared_ptr<Source> System_impl::get_source() {
  return this->source;
}

void System_impl::set_source(const std::shared_ptr<Source> &s) {
  this->source = s;
}

std::string System_impl::find_unit_tag(long unitID) {
  return unit_tags->find_unit_tag(unitID);
}

void System_impl::add_unit_tag(std::string pattern, std::string tag) {
  unit_tags->add(std::move(pattern), std::move(tag));
}


void System_impl::add_talkgroup(std::shared_ptr<Talkgroup> tg) {
  talkgroups->add_talkgroup(std::move(tg));
}

std::vector<std::shared_ptr<Talkgroup>> System_impl::get_talkgroups() {
  return talkgroups->get_talkgroups();
}



int System_impl::control_channel_count() {
  return control_channels.size();
}

std::vector<double> System_impl::get_control_channels() {
  return control_channels;
}

void System_impl::add_control_channel(double control_channel) {
  if (control_channels.size() == 0) {
    control_channels.push_back(control_channel);
  } else {
    if (std::find(control_channels.begin(), control_channels.end(),
                  control_channel) == control_channels.end()) {
      control_channels.push_back(control_channel);
    }
  }
}

double System_impl::get_current_control_channel() {
  return this->control_channels[current_control_channel];
}

double System_impl::get_next_control_channel() {
  current_control_channel++;
  if (current_control_channel >= control_channels.size()) {
    current_control_channel = 0;
  }
  return this->control_channels[current_control_channel];
}

void System_impl::set_bandplan(std::string bandplan) {
  this->bandplan = bandplan;
}

std::string System_impl::get_bandplan() {
  return this->bandplan;
}

void System_impl::set_bandfreq(int freq) {
  this->bandfreq = freq;
}

int System_impl::get_bandfreq() {
  return this->bandfreq;
}

void System_impl::set_bandplan_high(double high) {
  this->bandplan_high = high;
}

double System_impl::get_bandplan_high() {
  return this->bandplan_high / 1000000;
}

void System_impl::set_bandplan_base(double base) {
  this->bandplan_base = base;
}

double System_impl::get_bandplan_base() {
  return this->bandplan_base / 1000000;
}

void System_impl::set_bandplan_spacing(double space) {
  this->bandplan_spacing = space / 1000000;
}

double System_impl::get_bandplan_spacing() {
  return this->bandplan_spacing;
}

void System_impl::set_bandplan_offset(int offset) {
  this->bandplan_offset = offset;
}

int System_impl::get_bandplan_offset() {
  return this->bandplan_offset;
}

double System_impl::get_control_channel_pwr() {
  double best = std::numeric_limits<double>::quiet_NaN();
  for (auto &entry : decoders) {
    double pwr = entry.decoder->get_pwr();
    if (std::isnan(best) || pwr > best) {
      best = pwr;
    }
  }
  return best;
}

int System_impl::get_freq_error() {
  if (decoders.size() > 1) {
    BOOST_LOG_TRIVIAL(warning) << "[" << short_name << "] get_freq_error() called with " << decoders.size() << " decoders, using first";
  }
  if (!decoders.empty()) {
    return decoders[0].decoder->get_freq_error();
  }
  return 0;
}

void System_impl::finetune_control_freq(double f) {
  if (decoders.size() > 1) {
    BOOST_LOG_TRIVIAL(warning) << "[" << short_name << "] finetune_control_freq() called with " << decoders.size() << " decoders, using first";
  }
  if (!decoders.empty()) {
    decoders[0].decoder->finetune_control_freq(f);
  }
}

int System_impl::get_autotune_offset() {
  if (decoders.size() > 1) {
    BOOST_LOG_TRIVIAL(warning) << "[" << short_name << "] get_autotune_offset() called with " << decoders.size() << " decoders, using first";
  }
  if (!decoders.empty()) {
    return decoders[0].decoder->get_autotune_offset();
  }
  return 0;
}

void System_impl::set_autotune_offset(int offset) {
  if (decoders.size() > 1) {
    BOOST_LOG_TRIVIAL(warning) << "[" << short_name << "] set_autotune_offset() called with " << decoders.size() << " decoders, using first";
  }
  if (!decoders.empty()) {
    decoders[0].decoder->set_autotune_offset(offset);
  }
}

bool System_impl::add_ota_unit_tag(const OTAAlias &ota_alias) {
  if (unit_tags) {
    return unit_tags->add_ota(ota_alias);
  }
  return false;
}

void System_impl::set_msg_callback(std::function<void(gr::message::sptr)> cb) {
  d_msg_cb = std::move(cb);
  if (d_msg_cb) {
    for (auto &entry : decoders) {
      entry.decoder->set_msg_callback(d_msg_cb);
    }
  }
}

std::vector<std::shared_ptr<trunking_decoder>> System_impl::get_decoders() {
  std::vector<std::shared_ptr<trunking_decoder>> result;
  for (auto &entry : decoders) {
    result.push_back(entry.decoder);
  }
  return result;
}

void System_impl::setup_decoders(gr::top_block_sptr &tb, std::vector<std::shared_ptr<Source>> &sources) {
  for (auto &freq : control_channels) {
    std::shared_ptr<Source> src;
    for (auto &s : sources) {
      if (s->get_min_hz() <= freq && s->get_max_hz() >= freq) {
        src = s;
        break;
      }
    }
    if (!src) {
      BOOST_LOG_TRIVIAL(warning) << "[" << short_name << "] No source covers control channel " << format_freq(freq) << ", skipping";
      continue;
    }

    std::shared_ptr<trunking_decoder> decoder;
    if (system_type == SYS_SMARTNET) {
      auto sn = smartnet_impl::make(freq, src->get_center(), src->get_rate(), get_msg_queue(), get_sys_num());
      if (d_msg_cb) sn->set_msg_callback(d_msg_cb);
      tb->connect(src->get_src_block(), 0, sn, 0);
      decoder = sn;
    } else if (system_type == SYS_P25) {
      auto p25 = make_p25_trunking(freq, src->get_center(), src->get_rate(), get_msg_queue(), qpsk_mod, get_sys_num());
      if (d_msg_cb) p25->set_msg_callback(d_msg_cb);
      tb->connect(src->get_src_block(), 0, p25, 0);
      decoder = p25;
    } else {
      continue;
    }

    BOOST_LOG_TRIVIAL(info) << "[" << short_name << "] Decoder started on control channel " << format_freq(freq);
    decoders.push_back({decoder, src, freq});
  }

  if (!decoders.empty()) {
    set_source(decoders[0].source);
    if (decoders.size() > 1) {
      BOOST_LOG_TRIVIAL(warning) << "[" << short_name << "] " << decoders.size()
        << " decoders active, but system source set to first decoder's source only (autotune will only apply to first)";
    }
  }
}
