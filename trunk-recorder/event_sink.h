#ifndef EVENT_SINK_H
#define EVENT_SINK_H

#include <cstdint>
#include <memory>
#include <vector>

#include "unit_tags_ota.h"

class Call;
class System;
class Recorder;

class EventSink {
public:
  virtual ~EventSink() = default;

  virtual void audio_callback(const std::shared_ptr<Recorder> &recorder,
                              int16_t *samples, int sampleCount) = 0;
  virtual void unit_alias_discovered(const std::shared_ptr<System> &system,
                                     const OTAAlias &alias) = 0;
};

#endif // EVENT_SINK_H
