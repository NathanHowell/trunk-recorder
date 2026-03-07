#include "unit_tags.h"

#include <boost/log/trivial.hpp>
#include <ctime>

bool UnitTags::add_ota(const OTAAlias& ota_alias) {
  if (!ota_alias.success) {
    return false;
  }

  // Check if this unit already has an OTA tag (search OTA list only)
  std::shared_ptr<UnitTagOTA> existing_ota;
  for (auto it = unit_tags_ota.rbegin(); it != unit_tags_ota.rend(); ++it) {
    if ((*it)->unit_id == ota_alias.radio_id) {
      existing_ota = *it;
      break;
    }
  }

  if (existing_ota) {
    if (existing_ota->alias == ota_alias.alias) {
      // Enrich existing entry with metadata if missing
      bool needs_enrichment = (existing_ota->wacn.empty() && !ota_alias.wacn.empty()) ||
                              (existing_ota->sys.empty() && !ota_alias.sys.empty()) ||
                              (existing_ota->talkgroup_id == -1 && ota_alias.talkgroup_id != -1);

      if (needs_enrichment) {
        BOOST_LOG_TRIVIAL(debug) << "Unit " << ota_alias.radio_id << " (" << ota_alias.alias << "): enriching with metadata (WACN: " << ota_alias.wacn << ", SYS: " << ota_alias.sys << ", TG: " << ota_alias.talkgroup_id << ")";

        if (!ota_alias.source.empty()) existing_ota->source = ota_alias.source;
        if (!ota_alias.wacn.empty()) existing_ota->wacn = ota_alias.wacn;
        if (!ota_alias.sys.empty()) existing_ota->sys = ota_alias.sys;
        if (ota_alias.talkgroup_id != -1) existing_ota->talkgroup_id = ota_alias.talkgroup_id;
        existing_ota->timestamp = std::time(nullptr);
        return false;
      }
      BOOST_LOG_TRIVIAL(debug) << "Unit " << ota_alias.radio_id << " has existing OTA alias: '" << ota_alias.alias << "', skipping";
      return false;
    }
    BOOST_LOG_TRIVIAL(info) << "Unit " << ota_alias.radio_id << " OTA alias updated: '" << existing_ota->alias << "' -> '" << ota_alias.alias << "'";
  }

  auto ota_tag = std::make_shared<UnitTagOTA>(ota_alias.radio_id, ota_alias.alias, ota_alias.source, ota_alias.wacn, ota_alias.sys, ota_alias.talkgroup_id, std::time(nullptr));
  unit_tags_ota.push_back(ota_tag);

  return true;
}
