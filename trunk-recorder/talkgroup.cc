#include "talkgroup.h"

Talkgroup::Talkgroup(int sys_num, long num, std::string mode, int priority, unsigned long preferredNAC) {
  this->sys_num = sys_num;
  this->number = num;
  this->mode = mode;
  this->priority = priority;
  this->active = false;
  this->preferredNAC = preferredNAC;

  // This talkgroup is for a Trunked system and freq and tone are not used
  this->freq = 0;
  this->tone = 0;
  this->squelch_db = DB_UNSET;
  this->signal_detection = false;

}

Talkgroup::Talkgroup(int sys_num, long num, double freq, double tone, double squelch_db, bool signal_detection) {
  this->sys_num = sys_num;
  this->number = num;
  this->mode = "Z";
  this->active = false;
  this->freq = freq;
  this->tone = tone;
  this->squelch_db = squelch_db;
  this->signal_detection = signal_detection;

  // This talkgroup is for a Conventional system and priority and preferredNAC are not used
  this->priority = 0;
  this->preferredNAC = 0;
}

std::string Talkgroup::menu_string() {
  char buff[150];

  // std::ostringstream oss;

  snprintf(buff, 150, "%5lu - %s", number, mode.c_str());

  std::string buffAsStdStr = buff;

  return buffAsStdStr;
}

int Talkgroup::get_priority() {
  return priority;
}

unsigned long Talkgroup::get_preferredNAC() {
  return preferredNAC;
}

void Talkgroup::set_priority(int new_priority) {
  priority = new_priority;
  return;
}

bool Talkgroup::is_active() {
  return active;
}

void Talkgroup::set_active(bool a) {
  active = a;
}
