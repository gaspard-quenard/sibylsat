
#include <iostream>
#include <assert.h>
#include <sys/types.h>
#include <unistd.h>
#include <signal.h>
#include <cstdlib>
#include <sys/wait.h>
#include <exception>
#include <execinfo.h>
#include <signal.h>

#include "data/htn_instance.h"
#include "algo/planner.h"
#include "util/timer.h"
#include "util/signal_manager.h"
#include "util/random.h"

#ifndef LILOTANE_VERSION
#define LILOTANE_VERSION "(dbg)"
#endif

#ifndef IPASIRSOLVER
#define IPASIRSOLVER "(unknown)"
#endif

const char* LILOTANE_ASCII = 
  "    B_           _         _\n"
  "   A\\ C|         A\\ C|       A| C|                       \n"
  "   A| C|     B__  A| C|      B_A| C|B______                \n"
  "   A| C|     A\\C/  A| C|     A/D_   ______C\\                \n"
  "   A| C|      B_  A| C|   B__  A| C|  B___   ___   ___       \n"
  "   A| C|B___  A| C| A| C|  A/ C.\\ A| C| A/ C, | A|   C\\ A/ C·D_C\\    \n"
  "   A\\D_____C\\ A|D_C| A|D__C\\ A\\D__C/ A|D_C| A\\D___C) A|D_C|D_C| A\\D___C\\  \n";

const char* SIBYLSAT_ASCII =
":'A######B::'A####B:'A########B::'A##B:::'A##B:'A##B::::::::'A######B:::::'A###B::::'A########B: \n"
"'A##B... A##B:. A##B:: A##B.... A##B:. A##B:'A##B:: A##B:::::::'A##B... A##B:::'A##B A##B:::... A##B..:: \n"
" A##B:::..::: A##B:: A##B:::: A##B::. A####B::: A##B::::::: A##B:::..:::'A##B:. A##B::::: A##B:::: \n"
". A######B::: A##B:: A########B::::. A##B:::: A##B:::::::. A######B::'A##B:::. A##B:::: A##B:::: \n"
":..... A##B:: A##B:: A##B.... A##B:::: A##B:::: A##B::::::::..... A##B: A#########B:::: A##B:::: \n"
"'A##B::: A##B:: A##B:: A##B:::: A##B:::: A##B:::: A##B:::::::'A##B::: A##B: A##B.... A##B:::: A##B:::: \n"
". A######B::'A####B: A########B::::: A##B:::: A########B:. A######B:: A##B:::: A##B:::: A##B:::: \n"
":......:::....::........::::::..:::::........:::......:::..:::::..:::::..::::: \n";




void outputBanner(bool colors, bool use_sibylsat) {

    const char* ascii = use_sibylsat ? SIBYLSAT_ASCII : LILOTANE_ASCII;

    for (size_t i = 0; i < strlen(ascii); i++) {
        char c = ascii[i];
        switch (c) {
        case 'A': if (colors) std::cout << Modifier(Code::FG_GREEN).str(); break;
        case 'B': if (colors) std::cout << Modifier(Code::FG_CYAN).str(); break;
        case 'C': if (colors) std::cout << Modifier(Code::FG_LIGHT_BLUE).str(); break;
        case 'D': if (colors) std::cout << Modifier(Code::FG_LIGHT_YELLOW).str(); break;
        default : std::cout << std::string(1, c);
        }
    }
    std::cout << Modifier(Code::FG_DEFAULT).str();
}



void handleSignal(int signum) {
    SignalManager::signalExit();
}

void run(Parameters& params) {

    HtnInstance htn(params);
    Planner planner(params, htn);
    int result = planner.findPlan();

    if (result == 0 && !params.isNonzero("cleanup")) {
        // Exit directly -- avoid to clean up :)
        Log::i("Exiting happily (no cleaning up).\n");
        exit(result);
    }
    Log::i("Exiting happily.\n");
    return;
}

int main(int argc, char** argv) {
    
    signal(SIGTERM, handleSignal);
    signal(SIGINT, handleSignal);

    Timer::init();

    Parameters params;
    params.init(argc, argv);
    
    Random::init(params.getIntParam("s"), params.getIntParam("s"));

    int verbosity = params.getIntParam("v");
    Log::init(verbosity, /*coloredOutput=*/params.isNonzero("co"));

    // Add sibysat banner and indicate that it is based on a fork of lilotane

    if (verbosity >= Log::V2_INFORMATION) {
        outputBanner(params.isNonzero("co"), params.isNonzero("sibylsat"));
        if (params.isNonzero("sibylsat")) {
            Log::log_notime(Log::V0_ESSENTIAL, "S i b y l S a t");
            Log::log_notime(Log::V0_ESSENTIAL, "  version %s\n", LILOTANE_VERSION);
            Log::log_notime(Log::V0_ESSENTIAL, "by Gaspard Quenard <gaspard.quenard@univ-grenoble-alpes.fr> 2023-2024\n");
            Log::log_notime(Log::V0_ESSENTIAL, "based on a fork of the Lilotane planner by Dominik Schreiber <dominik.schreiber@kit.edu>\n");
            Log::log_notime(Log::V0_ESSENTIAL, "using SAT solver %s\n", IPASIRSOLVER);
            Log::log_notime(Log::V0_ESSENTIAL, "\n");
        } else {
            Log::log_notime(Log::V0_ESSENTIAL, "L i l o t a n e");
            Log::log_notime(Log::V0_ESSENTIAL, "  version %s\n", LILOTANE_VERSION);
            Log::log_notime(Log::V0_ESSENTIAL, "by Dominik Schreiber <dominik.schreiber@kit.edu> 2020-2021\n");
            Log::log_notime(Log::V0_ESSENTIAL, "using SAT solver %s\n", IPASIRSOLVER);
            Log::log_notime(Log::V0_ESSENTIAL, "\n");
        }
    }

    if (params.isSet("h") || params.isSet("help")) {
        params.printUsage();
        exit(0);
    }

    if (params.getProblemFilename() == "") {
        Log::w("Please specify both a domain file and a problem file. Use -h for help.\n");
        exit(1);
    }

    run(params);
    return 0;
}