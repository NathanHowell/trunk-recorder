#include "talkgroups.h"

#include <stdexcept>
#include <boost/algorithm/string/classification.hpp>
#include <boost/algorithm/string/split.hpp>
#include <boost/intrusive_ptr.hpp>
#include <boost/log/trivial.hpp>
#include <boost/tokenizer.hpp>

#include "csv_helper.h"
#include <csv-parser/csv.hpp>

#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>

Talkgroups::Talkgroups() {}

using namespace csv;

void Talkgroups::load_talkgroups(int sys_num, std::string filename) {
  if (filename == "") {
    return;
  } else {
    BOOST_LOG_TRIVIAL(info) << "Reading Talkgroup CSV File: " << filename;
  }

  CSVFormat format;
  format.trim({' ', '\t'});
  CSVReader reader(filename, format);
  std::vector<std::string> headers = reader.get_col_names();
  std::vector<std::string> defined_headers = {"Decimal", "Mode", "Description", "Alpha Tag", "Hex", "Category", "Tag", "Priority", "Preferred NAC", "Comment"};

  if (headers[0] != "Decimal") {

    BOOST_LOG_TRIVIAL(error) << "Column Headers are required for Talkgroup CSV files";
    BOOST_LOG_TRIVIAL(error) << "The first column must be 'Decimal'";
    BOOST_LOG_TRIVIAL(error) << "Required columns are: 'Decimal', 'Mode', 'Description'";
    BOOST_LOG_TRIVIAL(error) << "Optional columns are: 'Alpha Tag', 'Hex', 'Category', 'Tag', 'Priority', 'Preferred NAC'";
    throw std::runtime_error("Talkgroup CSV: first column must be 'Decimal'");
  } else {
    BOOST_LOG_TRIVIAL(info) << "Found Columns: " << internals::format_row(reader.get_col_names(), ", ");
  }

  for (size_t i = 0; i < headers.size(); i++) {
    if (find(defined_headers.begin(), defined_headers.end(), headers[i]) == defined_headers.end()) {
      BOOST_LOG_TRIVIAL(error) << "Unknown column header: " << headers[i];
      BOOST_LOG_TRIVIAL(error) << "Required columns are: 'Decimal', 'Mode', 'Description'";
      BOOST_LOG_TRIVIAL(error) << "Optional columns are: 'Alpha Tag', 'Hex', 'Category', 'Tag', 'Priority', 'Preferred NAC'";
      throw std::runtime_error("Talkgroup CSV: unknown column header '" + headers[i] + "'");
    }
  }

  long lines_pushed = 0;
  for (CSVRow &row : reader) { // Input iterator
    int priority = 1;
    unsigned long preferredNAC = 0;
    long tg_number = 0;
    std::string alpha_tag = "";
    std::string description = "";
    std::string tag = "";
    std::string group = "";
    std::string mode = "";

    if ((reader.index_of("Decimal") >= 0) && !row["Decimal"].is_null() && row["Decimal"].is_int()) {
      tg_number = row["Decimal"].get<long>();
    } else {
      BOOST_LOG_TRIVIAL(error) << "'Decimal' is required for specifying the Talkgroup number - Row: " << reader.n_rows();
      throw std::runtime_error("Talkgroup CSV: missing 'Decimal' value");
    }

    if ((reader.index_of("Mode") >= 0) && row["Mode"].is_str()) {
      mode = row["Mode"].get<std::string>();
    } else {
      BOOST_LOG_TRIVIAL(error) << "Mode is required for Row: " << reader.n_rows();
      throw std::runtime_error("Talkgroup CSV: missing 'Mode' value");
    }

    if (reader.index_of("Description") >= 0) {
      description = row["Description"].get<std::string>();
    } else {
      BOOST_LOG_TRIVIAL(error) << "Description is required for Row: " << reader.n_rows();
      throw std::runtime_error("Talkgroup CSV: missing 'Description' value");
    }

    if (reader.index_of("Alpha Tag") >= 0) {
      alpha_tag = row["Alpha Tag"].get<std::string>();
    }

    if (reader.index_of("Tag") >= 0) {
      tag = row["Tag"].get<std::string>();
    }

    if (reader.index_of("Category") >= 0) {
      group = row["Category"].get<std::string>();
    }

    if ((reader.index_of("Priority") >= 0) && row["Priority"].is_int()) {
      priority = row["Priority"].get<int>();
    }

    if ((reader.index_of("Preferred NAC") >= 0) && row["Preferred NAC"].is_int()) {
      preferredNAC = row["Preferred NAC"].get<unsigned long>();
    }
    talkgroups.push_back(std::make_shared<Talkgroup>(sys_num, tg_number, mode, alpha_tag, description, tag, group, priority, preferredNAC));
    lines_pushed++;
  }

  BOOST_LOG_TRIVIAL(info) << "Read " << lines_pushed << " talkgroups.";
}

void Talkgroups::load_channels(int sys_num, std::string filename) {

  if (filename == "") {
    return;
  } else {
    BOOST_LOG_TRIVIAL(info) << "Reading Channel CSV File: " << filename;
  }

  CSVFormat format;
  format.trim({' ', '\t'});
  CSVReader reader(filename, format);
  std::vector<std::string> headers = reader.get_col_names();
  std::vector<std::string> defined_headers = {"TG Number", "Tone", "Frequency", "Alpha Tag", "Description", "Category", "Tag", "Enable", "Comment", "Signal Detector", "Squelch"};

  if (headers[0] != "TG Number") {

    BOOST_LOG_TRIVIAL(error) << "Column Headers are required for Channel CSV files";
    BOOST_LOG_TRIVIAL(error) << "The first column must be 'TG Number'";
    BOOST_LOG_TRIVIAL(error) << "Required columns are: 'TG Number', 'Frequency'";
    BOOST_LOG_TRIVIAL(error) << "Optional columns are: 'Alpha Tag', 'Tone', 'Description', 'Category', 'Tag', 'Enable', 'Comment', 'Signal Detector', 'Squelch'";
    throw std::runtime_error("Channel CSV: first column must be 'TG Number'");
  } else {
    BOOST_LOG_TRIVIAL(info) << "Found Columns: " << internals::format_row(reader.get_col_names(), ", ");
  }

  for (size_t i = 0; i < headers.size(); i++) {
    if (find(defined_headers.begin(), defined_headers.end(), headers[i]) == defined_headers.end()) {
      BOOST_LOG_TRIVIAL(error) << "Unknown column header: " << headers[i];
      BOOST_LOG_TRIVIAL(error) << "Required columns are: 'TG Number', 'Frequency'";
      BOOST_LOG_TRIVIAL(error) << "Optional columns are: 'Alpha Tag', 'Tone', 'Description', 'Category', 'Tag', 'Enable', 'Comment', 'Signal Detector', 'Squelch'";
      throw std::runtime_error("Channel CSV: unknown column header '" + headers[i] + "'");
    }
  }

  long lines_pushed = 0;
  for (CSVRow &row : reader) { // Input iterator
    long tg_number = 0;
    std::string alpha_tag = "";
    std::string description = "";
    std::string tag = "";
    std::string group = "";
    double squelch_db = DB_UNSET;
    bool signal_detector = true;
    double freq = 0;
    double tone = 0;
    bool enable = true;

    if ((reader.index_of("TG Number") >= 0) && !row["TG Number"].is_null() && row["TG Number"].is_int()) {
      tg_number = row["TG Number"].get<long>();
    } else {
      BOOST_LOG_TRIVIAL(error) << "'TG Number' is required for specifying the Talkgroup number - Row: " << reader.n_rows();
      throw std::runtime_error("Channel CSV: missing 'TG Number' value");
    }

    if ((reader.index_of("Description") >= 0) && row["Description"].is_str()) {
      description = row["Description"].get<std::string>();
    }

    if ((reader.index_of("Alpha Tag") >= 0) && row["Alpha Tag"].is_str()) {
      alpha_tag = row["Alpha Tag"].get<std::string>();
    }

    if ((reader.index_of("Tag") >= 0) && row["Tag"].is_str()) {
      tag = row["Tag"].get<std::string>();
    }

    if ((reader.index_of("Category") >= 0) && row["Category"].is_str()) {
      group = row["Category"].get<std::string>();
    }

    if ((reader.index_of("Tone") >= 0) && row["Tone"].is_float()) {
      tone = row["Tone"].get<double>();
    }

    if ((reader.index_of("Frequency") >= 0) && row["Frequency"].is_num()) {
      freq = row["Frequency"].get<double>();
      // If this is a float under 1000, it must be in MHz so convert to Hz
      if (row["Frequency"].is_float() && freq < 1000.0) {
        freq = freq * 1e+6;
      }
    }

    if ((reader.index_of("Squelch") >= 0) && row["Squelch"].is_num()) {
      squelch_db = row["Squelch"].get<double>();
    }

    if ((reader.index_of("Signal Detector") >= 0) && row["Signal Detector"].is_str()) {
      if (boost::iequals(row["Signal Detector"].get<std::string>(), "false")) {
        signal_detector = false;
      }
    }


    if ((reader.index_of("Enable") >= 0) && row["Enable"].is_str()) {
      if (boost::iequals(row["Enable"].get<std::string>(), "false")) {
        enable = false;
      }
    }
    if (enable) {
      talkgroups.push_back(std::make_shared<Talkgroup>(sys_num, tg_number, freq, tone, alpha_tag, description, tag, group, squelch_db, signal_detector));
      lines_pushed++;
    }

    BOOST_LOG_TRIVIAL(info) << "Read " << lines_pushed << " channels.";
  }
}

std::shared_ptr<Talkgroup> Talkgroups::find_talkgroup(int sys_num, long tg_number) {
  for (auto &tg : talkgroups) {
    if ((tg->sys_num == sys_num) && (tg->number == tg_number)) {
      return tg;
    }
  }
  return nullptr;
}

std::shared_ptr<Talkgroup> Talkgroups::find_talkgroup_by_freq(int sys_num, double freq) {
  for (auto &tg : talkgroups) {
    if ((tg->sys_num == sys_num) && (tg->freq == freq)) {
      return tg;
    }
  }
  return nullptr;
}

std::vector<std::shared_ptr<Talkgroup>> Talkgroups::get_talkgroups() {
  return talkgroups;
}
