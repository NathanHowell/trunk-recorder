#ifndef CALL_STATE_MANAGER_H
#define CALL_STATE_MANAGER_H

#include <memory>
#include <vector>

#include "call.h"
#include "global_structs.h"
#include "source.h"
#include "systems/parser.h"
#include "systems/system.h"

/// Owns the active calls vector and centralizes all call lifecycle transitions.
///
/// Every state change (MONITORING, RECORDING, concluded) goes through this
/// class so that timeout and cleanup logic lives in one place.
class CallStateManager {
public:
  CallStateManager(Config &config, std::vector<std::shared_ptr<Source>> &sources);

  /// Handle a GRANT or UPDATE-as-grant message from the control channel.
  void handle_grant(TrunkMessage message, const std::shared_ptr<System> &sys,
                    bool is_grant_message);

  /// Handle an UPDATE message for an existing call.
  void handle_update(TrunkMessage message, const std::shared_ptr<System> &sys);

  /// Run periodic call management (timeouts, conventional idle detection).
  /// Called every ~1 second from the main loop.
  void tick();

  /// Conclude all active calls (called on shutdown).
  void conclude_all();

  /// Process message queues for recorders associated with active calls.
  void process_recorder_queues();

  /// Read-only access to the active calls vector.
  const std::vector<std::shared_ptr<Call>> &active_calls() const { return calls_; }

  /// Mutable access (needed by monitor_messages for print_status).
  std::vector<std::shared_ptr<Call>> &active_calls_mut() { return calls_; }

private:
  bool try_start_recording(const std::shared_ptr<Call> &call,
                           TrunkMessage message,
                           const std::shared_ptr<System> &sys);

  void conclude_and_erase(std::vector<std::shared_ptr<Call>>::iterator &it,
                          bool &ended_call);

  void manage_trunked_call(std::vector<std::shared_ptr<Call>>::iterator &it,
                           bool &ended_call);

  void manage_conventional_call(const std::shared_ptr<Call> &call);

  struct MultiSiteResult {
    bool is_duplicate = false;
    bool is_superseding = false;
    std::shared_ptr<Call> original_call;
  };

  MultiSiteResult check_multisite(long talkgroup, int sys_num,
                                  const std::shared_ptr<System> &sys);

  Config &config_;
  std::vector<std::shared_ptr<Source>> &sources_;
  std::vector<std::shared_ptr<Call>> calls_;
};

#endif // CALL_STATE_MANAGER_H
