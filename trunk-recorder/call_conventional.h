#ifndef CALL_CONVENTIONAL_H
#define CALL_CONVENTIONAL_H

#include "call.h"

class Call_conventional : public Call {
public:
  Call_conventional(const std::shared_ptr<System> &s);
  void restart_call(const RecorderConfig &cfg) override;
};

#endif
