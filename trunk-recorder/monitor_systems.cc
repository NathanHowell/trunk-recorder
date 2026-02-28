// monitor_systems.cc — formerly the C++ monitor loop.
//
// All logic has moved to Rust (trunk-oxide crate):
//   - Message draining & dispatch → CallManager::handle_message
//   - Call lifecycle (grant/update/timeout) → CallManager
//   - Periodic checks → TrunkRecorder::run_monitor
//   - Signal handling → Rust main (tokio ctrl_c)
//
// The monitor_messages() entry point and all helper functions have been removed.
// This file is kept to avoid breaking the shared library's compilation unit list.

#include "monitor_systems.h"
