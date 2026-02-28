#ifndef STATE_H
#define STATE_H

enum CallState {
             MONITORING = 0,
             RECORDING = 1 };

enum RecorderState {
             REC_RECORDING = 1,
             REC_INACTIVE = 2,
             REC_ACTIVE = 3,
             REC_IDLE = 4,
             REC_STOPPED = 6,
             REC_AVAILABLE = 7,
             REC_IGNORE = 8 };

enum MonitoringState {
             UNSPECIFIED = 0,
             UNKNOWN_TG = 1,
             IGNORED_TG = 2,
             NO_SOURCE = 3,
             NO_RECORDER = 4,
             ENCRYPTED = 5,
             DUPLICATE = 6,
             SUPERSEDED = 7};

#endif
