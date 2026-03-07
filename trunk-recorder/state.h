#ifndef STATE_H
#define STATE_H

enum RecorderState {
             REC_RECORDING = 1,
             REC_INACTIVE = 2,
             REC_ACTIVE = 3,
             REC_IDLE = 4,
             REC_STOPPED = 6,
             REC_AVAILABLE = 7,
             REC_IGNORE = 8 };

#endif
