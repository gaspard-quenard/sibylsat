import os
import subprocess
import logging
import shlex
import time
from colorama import init, Fore

TIMEOUT_S = 60

PATH_BENCHMARKS = [
    ("Benchmarks/ipc2020-domains/total-order/Blocksworld-GTOHP", 20),
    # ("Benchmarks/ipc2023-domains/total-order/SharpSAT/SharpSAT", 2),
    ("Benchmarks/ipc2023-domains/total-order/Lamps", 10),
    ("Benchmarks/ipc2023-domains/total-order/Robot", 5),
    ("Benchmarks/ipc2023-domains/total-order/Depots", 20),
    # ("Benchmarks/ipc2023-domains/total-order/Multiarm-Blocksworld", 100),
    # ("Benchmarks/ipc2023-domains/total-order/Blocksworld-HPDDL", 100),
    ("Benchmarks/ipc2023-domains/total-order/Monroe-Fully-Observable", 5),
    ("Benchmarks/ipc2023-domains/total-order/Monroe-Partially-Observable", 5),
    ("Benchmarks/ipc2020-domains/total-order/Elevator-Learned-ECAI-16", 20),
    ("Benchmarks/ipc2020-domains/total-order/AssemblyHierarchical", 2),
    ("Benchmarks/ipc2020-domains/total-order/Logistics-Learned-ECAI-16", 8),
    ("Benchmarks/ipc2020-domains/total-order/Minecraft-Regular", 2),
    # ("Benchmarks/ipc2020-domains/total-order/Minecraft-Player", 30),
    ("Benchmarks/ipc2020-domains/total-order/Entertainment", 3),
    ("Benchmarks/ipc2020-domains/total-order/Transport", 20),
    ("Benchmarks/ipc2020-domains/total-order/Towers", 5),
    ("Benchmarks/ipc2020-domains/total-order/Snake", 5),
    ("Benchmarks/ipc2020-domains/total-order/Childsnack", 10),
    ("Benchmarks/ipc2020-domains/total-order/Satellite-GTOHP", 5),
    ("Benchmarks/ipc2020-domains/total-order/Rover-GTOHP", 5),
    ("Benchmarks/ipc2020-domains/total-order/Factories-simple", 3),
    # ("Benchmarks/ipc2020-domains/total-order/Freecell-Learned-ECAI-16", 100),
    ("Benchmarks/ipc2020-domains/total-order/Barman-BDI", 10),
    ("Benchmarks/ipc2020-domains/total-order/Woodworking", 10),
    ("Benchmarks/ipc2020-domains/total-order/Hiking", 5),  
]

# Optimal size plan per benchmark according to PandaDealer Optimal
Optimal_size_plan_per_benchmark = {
    "Blocksworld-GTOHP": [21, 35, 39, 62, 71, 79, 84, 119, 103, 147, 153, 150, 145, 164, 180, 190, 219, 247, 242, 237],
    "SharpSAT": [23, 27],
    "Lamps": [1, 2, 5, 2, 7, 1, 12, 6, 4, 11],
    "Robot": [0, 6, 7, 7, 11],
    "Depots": [15, 24, 44, 51, 71, 92, 34, 55, 93, 38, 73, 96, 37, 47, 101, 41, 43, 109, 57, 108],
    "Monroe-Fully-Observable": [7, 16, 11, 3, 18],
    "Monroe-Partially-Observable": [11, 6, 12, 13, 16],
    "Elevator-Learned-ECAI-16": [11, 10, 21, 21, 21, 22, 22, 32, 32, 33, 32, 32, 44, 43, 44, 44, 44, 55, 55, 53, 55, 55, 65, 64, 65, 66, 66, 77, 75, 77, 76, 77],
    "AssemblyHierarchical": [4, 6],
    "Logistics-Learned-ECAI-16": [63, 58, 40, 89, 50, 27, 81, 43, 81, 74, 115, 133, 96],
    "Minecraft-Regular": [35, 44],
    "Entertainment": [40, 24, 48],
    "Transport": [8, 19, 15, 22, 32, 29, 32, 34, 31, 35, 20, 18, 27, 31, 39, 52, 50, 53, 65, 40],
    "Towers": [1, 3, 7, 15, 31],
    "Snake": [4, 4, 4, 2, 10],
    "Childsnack": [50, 50, 55, 60, 65, 65, 70, 70, 75, 75, 80],
    "Satellite-GTOHP": [12, 18, 16, 40, 63],
    "Rover-GTOHP": [16, 24, 16, 40, 50],
    "Factories-simple": [15, 48, 58],
    "Barman-BDI": [10, 24, 38, 23, 37, 52, 23, 36, 51, 36],
    "Woodworking": [7, 3, 6, 4, 6, 6, 12, 12, 9, 15],
    "Hiking": [26, 38, 50, 62, 74]
}


planner_config = "./sibylsat {domain_path} {problem_path} -optimal=0 -reusePreviousCores=0"


if __name__ == "__main__":


    # Initialize colorama
    init(autoreset=True)

    # Initialize logging
    logging.basicConfig(
        format='%(asctime)s %(levelname)s:%(message)s', level=logging.DEBUG)

    # Add the option to verify the plan if not already present
    if (not "-vp=1" in planner_config):
        print(f"{Fore.MAGENTA}Add the option '-vp=1' to verify the plan{Fore.RESET}")
        planner_config += " -vp=1"
        

    is_optimal = "-optimal=1"  in planner_config
    print(f"{Fore.MAGENTA}Check if the plan is optimal: {is_optimal} {Fore.RESET}")

    initial_time_all = time.time()

    number_instances_checked = 0

    number_of_benchmarks = len(PATH_BENCHMARKS)
    idx_benchmark = 0

    for (path_benchmark, highest_instance_to_solve) in PATH_BENCHMARKS:

        idx_benchmark += 1

        name_benchmark = path_benchmark.split('/')[-1]
        logging.info(
            f"Test benchmark {name_benchmark} ({idx_benchmark}/{number_of_benchmarks})")
        

        # Load all the problems
        all_files_in_benchmark = sorted(os.listdir(path_benchmark))

        full_path_benchmark = os.path.abspath(path_benchmark)

        # Remove all files which do not end with hddl
        files_in_benchmark = [f for f in all_files_in_benchmark if f.endswith("hddl") or f.endswith("pddl")]

        # Get all the domain files
        domain_files = [f for f in files_in_benchmark if "domain" in f.lower() and f.endswith("hddl")]

        # Remove all the files which can contains the "domain" keyword with any case
        files_in_benchmark = [f for f in files_in_benchmark if not "domain" in f.lower()]

        # Keep only the first 2 level of each benchmark
        num_level_to_keep = min(highest_instance_to_solve, len(files_in_benchmark))

        

        initial_time = time.time()
        for i in range(num_level_to_keep):
            files_in_benchmark[i] = files_in_benchmark[i]

            # Check if the domain file exists
            domain_file_name = "domain.hddl"
            if not domain_file_name in domain_files:
                # Check if the domain is the name of the problem + "-domain.hddl"
                domain_file_name = files_in_benchmark[i].split('.')[0] + "-domain.hddl"
                if not domain_file_name in domain_files:
                    logging.error(f"{Fore.RED}Benchmark {name_benchmark} is NOK because domain file is not found{Fore.RESET}")
                    exit(1)

            # Launch planner to test is OK
            command = planner_config.format(domain_path=os.path.join(full_path_benchmark, domain_file_name), problem_path=os.path.join(full_path_benchmark, files_in_benchmark[i]))
            print(command)
            output = subprocess.run(shlex.split(command), check=False, stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True, timeout=TIMEOUT_S)

            return_code = output.returncode

            if (return_code != 0):
                logging.error(f"{Fore.RED}Benchmark {name_benchmark} is NOK{Fore.RESET}")
                exit(1)

            # Get the size of the plan from the output (line with End of solution plan. (counted length of <size_plan>))
            output_str = output.stdout
            output_str = output_str.split('\n')
            
            # Confirm that the plan has been verified as correct (contains the line "Plan has been verified by pandaPIparser")
            verified = False
            for line in output_str:
                if "Plan has been verified by pandaPIparser" in line:
                    verified = True
                    break
            if not verified:
                logging.error(f"{Fore.RED}Benchmark {name_benchmark} is NOK because the plan of problem {files_in_benchmark[i]} has not been verified{Fore.RESET}")
                exit(1)
            
            
            size_plan = 0
            for line in output_str:
                if "End of solution plan. (counted length of" in line:
                    size_plan = int(line.split(' ')[-1][:-1])
                    break

            if is_optimal and len(Optimal_size_plan_per_benchmark[name_benchmark]) > i:
                if size_plan != Optimal_size_plan_per_benchmark[name_benchmark][i]:
                    logging.error(f"{Fore.RED}Benchmark {name_benchmark} is NOK because the plan of problem {files_in_benchmark[i]} is not optimal ({size_plan} instead of {Optimal_size_plan_per_benchmark[name_benchmark][i]}){Fore.RESET}")
                    exit(1)

            # Print the size of the plan
            # logging.info(f"Size of the plan: {size_plan}")
            number_instances_checked += 1

        final_time = time.time()
        logging.info(
            f"{Fore.GREEN}Benchmark {name_benchmark} is OK{Fore.RESET} (done in {round(final_time - initial_time, 2)} s)")
        


    final_time_all = time.time()
    # Get the time with 2 decimals
    time_all = round(final_time_all - initial_time_all, 2)

    logging.info(
        f"{Fore.GREEN}All the tests are OK{Fore.RESET} (Check {number_instances_checked} problems) (done in {time_all} s)")
        
    
