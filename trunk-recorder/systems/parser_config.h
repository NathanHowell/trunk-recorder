#ifndef PARSER_CONFIG_H
#define PARSER_CONFIG_H

#include <string>

struct SmartnetParserConfig {
    int sys_num;
    std::string bandplan;
    int bandfreq;
    double bandplan_base;
    double bandplan_high;
    double bandplan_spacing;
    int bandplan_offset;
};

struct P25ParserConfig {
    int sys_num;
    std::string short_name;
    std::string custom_freq_table_file;
};

#endif
