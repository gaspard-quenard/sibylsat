#ifndef DOMAIN_SETTINGS_MANAGER_H
#define DOMAIN_SETTINGS_MANAGER_H

#include <string>
#include <unordered_map>
#include <mutex>
#include <fstream>
#include <filesystem>

#include "util/json.hpp"
#include "util/project_utils.h"

using json = nlohmann::json;

class DomainSettingsManager {
private:
    json settings;
    const std::filesystem::path settings_file;

    static std::filesystem::path getSettingsFilePath() {
        return getProblemProcessingDir() / "domain_settings.json";
    }

    void load_settings() {
        std::ifstream file(settings_file);
        if (!file) {
            settings = json::object();  // Initialize empty JSON object
            return;
        }
        try {
            settings = json::parse(file);
        } catch (const json::parse_error& e) {
            settings = json::object();  // Initialize empty JSON if file is corrupted
        }
    }

    void save_settings() const {
        std::ofstream file(settings_file);
        if (!file) {
            throw std::runtime_error("Could not open settings file for writing: " + settings_file.string());
        }
        file << settings.dump(4);  // Pretty print with 4 spaces indent
    }

public:
    // Note: This implementation is not thread-safe. It assumes single-threaded access.
    DomainSettingsManager() : settings_file(getSettingsFilePath()) {
        load_settings();
    }

    bool has_setting(const std::string& domain, const std::string& key) const {
        return settings.contains(domain) && settings[domain].contains(key);
    }

    bool get_setting(const std::string& domain, const std::string& key) const {
        return has_setting(domain, key) ? settings[domain][key].get<bool>() : false;
    }

    void set_setting(const std::string& domain, const std::string& key, bool value) {
        settings[domain][key] = value;
        save_settings();
    }
};

#endif // DOMAIN_SETTINGS_MANAGER_H