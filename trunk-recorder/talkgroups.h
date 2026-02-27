#ifndef TALKGROUPS_H
#define TALKGROUPS_H

#include "talkgroup.h"
#include <boost/algorithm/string.hpp>
#include <memory>
#include <string>
#include <vector>

class Talkgroups {
  std::vector<std::shared_ptr<Talkgroup>> talkgroups;

public:
  Talkgroups();
  void load_talkgroups(int sys_num, std::string filename);
  void load_channels(int sys_num, std::string filename);
  std::shared_ptr<Talkgroup> find_talkgroup(int sys_num, long tg);
  std::shared_ptr<Talkgroup> find_talkgroup_by_freq(int sys_num, double freq);
  std::vector<std::shared_ptr<Talkgroup>> get_talkgroups();
};
#endif // TALKGROUPS_H
