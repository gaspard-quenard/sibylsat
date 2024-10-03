#ifndef STRING_UTIL_H
#define STRING_UTIL_H

#include <vector>
#include <string>
#include <sstream>

class StringUtil {
public:
    // Joins elements of a std::vector<std::string> into a single std::string with a specified delimiter
    static std::string join(const std::vector<std::string>& vec, const char* delim) {
        std::ostringstream oss;
        if (!vec.empty()) {
            auto iter = vec.begin();
            oss << *iter++;  // Handle the first element without preceding it with a delimiter
            while (iter != vec.end()) {
                oss << delim << *iter++;
            }
        }
        return oss.str();
    }
};

#endif // STRING_UTIL_H
