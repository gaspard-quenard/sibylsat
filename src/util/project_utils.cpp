#include "project_utils.h"

// Macro to convert preprocessor macro to string
#define STRINGIFY(x) #x
#define TO_STRING(x) STRINGIFY(x)

// Implementation of the function
std::filesystem::path getProjectRootDir() {
    return std::filesystem::path(TO_STRING(PROJECT_ROOT_DIR));
}
