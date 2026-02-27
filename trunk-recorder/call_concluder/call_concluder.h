#ifndef CALL_CONCLUDER_H
#define CALL_CONCLUDER_H
#include <ctime>
#include <vector>

#include "../call.h"
#include "../formatter.h"
#include "../global_structs.h"
#include "../systems/system.h"
#include "../systems/system_impl.h"

class Call_Concluder {

public:
  static Call_Data_t create_call_data(Call *call, System *sys, Config config);
  static void conclude_call(Call *call, System *sys, Config config);
};

#endif
