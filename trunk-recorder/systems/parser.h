#ifndef PARSE_H
#define PARSE_H
#include <iostream>
#include <vector>

enum MessageType {
  GRANT = 0,
  STATUS = 1,
  UPDATE = 2,
  CONTROL_CHANNEL = 3,
  REGISTRATION = 4,
  DEREGISTRATION = 5,
  AFFILIATION = 6,
  SYSID = 7,
  ACKNOWLEDGE = 8,
  LOCATION = 9,
  PATCH_ADD = 10,
  PATCH_DELETE = 11,
  DATA_GRANT = 12,
  UU_ANS_REQ = 13,
  UU_V_GRANT = 14,
  UU_V_UPDATE = 15,
  INVALID_CC_MESSAGE = 16,
  TDULC = 17,
  UNKNOWN = 99
};

struct PatchData {
  unsigned long sg = 0;
  unsigned long ga1 = 0;
  unsigned long ga2 = 0;
  unsigned long ga3 = 0;
};

struct TrunkMessage {
  MessageType message_type = UNKNOWN;
  std::string meta;
  double freq = 0.0;
  long talkgroup = 0;
  bool encrypted = false;
  bool emergency = false;
  bool duplex = false;
  bool mode = false;
  int priority = 0;
  int tdma_slot = 0;
  bool phase2_tdma = false;
  long source = -1;
  int sys_num = 0;
  unsigned long sys_id = 0;
  int sys_rfss = 0;
  int sys_site_id = 0;
  unsigned long nac = 0;
  unsigned long wacn = 0;
  PatchData patch_data;
  unsigned long opcode = 0;

};

class TrunkParser {
  std::vector<TrunkMessage> parse_message(std::string s);
};
#endif
