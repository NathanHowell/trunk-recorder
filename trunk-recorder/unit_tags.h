#ifndef UNIT_TAGS_H
#define UNIT_TAGS_H

#include "unit_tag.h"
#include "unit_tags_ota.h"

#include <memory>
#include <string>
#include <vector>

class UnitTags {
  std::vector<std::shared_ptr<UnitTagOTA>> unit_tags_ota;           // OTA tags for dedup

public:
  bool add_ota(const OTAAlias& ota_alias);
};
#endif // UNIT_TAGS_H
