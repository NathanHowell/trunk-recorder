#ifndef _CSV_HELPER_H_
#define _CSV_HELPER_H_

#include <boost/log/trivial.hpp>

#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <string>

std::istream &safeGetline(std::istream &is, std::string &t);

#endif // _CSV_HELPER_H_