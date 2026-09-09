#include "util/process_utils.h"

#include <array>
#include <cerrno>
#include <cstdio>
#include <stdexcept>
#include <system_error>
#include <sys/wait.h>
#include <unistd.h>
#include <vector>

std::string quoteShellArgument(const std::string& argument) {
    std::string quoted = "'";
    for (char character : argument) {
        if (character == '\'') quoted += "'\\''";
        else quoted += character;
    }
    return quoted + "'";
}

bool commandSucceeds(const std::string& command) {
    const int status = std::system(command.c_str());
    return status != -1 && WIFEXITED(status) && WEXITSTATUS(status) == 0;
}

bool commandSucceedsAndOutputContains(const std::string& command, const std::string& expectedOutput) {
    FILE* pipe = popen(command.c_str(), "r");
    if (pipe == nullptr) throw std::runtime_error("Could not execute command: " + command);

    std::array<char, 256> buffer;
    std::string output;
    while (fgets(buffer.data(), buffer.size(), pipe) != nullptr) output += buffer.data();

    const int status = pclose(pipe);
    return status != -1 && WIFEXITED(status) && WEXITSTATUS(status) == 0
            && output.find(expectedOutput) != std::string::npos;
}

TemporaryFile::TemporaryFile(const std::string& prefix) {
    std::string pathTemplate = (std::filesystem::temp_directory_path() / (prefix + "XXXXXX")).string();
    std::vector<char> writablePath(pathTemplate.begin(), pathTemplate.end());
    writablePath.push_back('\0');

    const int fileDescriptor = mkstemp(writablePath.data());
    if (fileDescriptor == -1) throw std::system_error(errno, std::generic_category(), "Could not create temporary file");
    close(fileDescriptor);
    _path = writablePath.data();
}

TemporaryFile::~TemporaryFile() {
    std::error_code error;
    std::filesystem::remove(_path, error);
}
