#ifndef SIBYLSAT_PROCESS_UTILS_H
#define SIBYLSAT_PROCESS_UTILS_H

#include <filesystem>
#include <string>

/** Quote one argument so it is passed literally to a POSIX shell command. */
std::string quoteShellArgument(const std::string& argument);

/** Run a command and return whether it exits successfully. */
bool commandSucceeds(const std::string& command);

/** Run a command and return whether it exits successfully and prints the expected text. */
bool commandSucceedsAndOutputContains(const std::string& command, const std::string& expectedOutput);

/** Own a uniquely named temporary file and remove it when the object leaves scope. */
class TemporaryFile {
private:
    std::filesystem::path _path;

public:
    /** Create an empty temporary file whose name begins with prefix. */
    explicit TemporaryFile(const std::string& prefix);
    ~TemporaryFile();

    TemporaryFile(const TemporaryFile&) = delete;
    TemporaryFile& operator=(const TemporaryFile&) = delete;
    TemporaryFile(TemporaryFile&&) = delete;
    TemporaryFile& operator=(TemporaryFile&&) = delete;

    /** Return the path of the temporary file owned by this object. */
    const std::filesystem::path& getPath() const { return _path; }
};

#endif
