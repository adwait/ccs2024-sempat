

import os
import sys
import json
import datetime
import argparse
from tabulate import tabulate

TIMEOUT = 1800

# Size of the reuse-buffer (Figure 7, Figure 12(c))
RUB_SIZE = [2, 4, 8, 16, 32, 64]
# Grammar depth
DEPTHS = [3, 4]

configwise_times = {}

def get_tg_config (benchname, rub_size, depth):
    return f"{benchname}_rubsize{rub_size}_depth{depth}"

def bvssv2_tg_command (benchname, rub_size, depth):
    config = get_tg_config(benchname, rub_size, depth)
    command = f"secant --verbosity 3 -s {config} -c syntab -p bvcompre -q rubc_size={rub_size},has_cache=0 -a bvcompre:tg --analyzercfg depth={depth},spec_type=1"
    return (config, command)


# Run generation for all configs
def main(args):

    parser = argparse.ArgumentParser()
    # Grab benchname from argparse
    parser.add_argument("benchname", help="Name of benchmark directory (also used as directory to place results into).", type=str)
    parser.add_argument("--dryrun", help="Dry-run mode", dest="dryrun", action="store_true")
    parser.add_argument("--jsonresults", help="Generate results in a JSON file.", dest="jsonresults", action="store_true")
    parser.set_defaults(dryrun=False)    
    parser.set_defaults(json_results=False)    
    args = parser.parse_args(args)
    benchname = args.benchname
    dryrun = args.dryrun
    json_results = args.json_results

    # Make directory for benchmark
    os.makedirs(benchname, exist_ok=True)

    all_times = [["Reuse buffer size", "Generation time (s) with\ngrammar depth = 3", "Generation time (s) with\ngrammar depth = 4"]]


    # RUB size based generation
    for rub_size in RUB_SIZE:
        times = [rub_size]
        for depth in DEPTHS:
            (conf, com) = bvssv2_tg_command(benchname, rub_size, depth)
            command = f"timeout -s 9 {TIMEOUT} {com}"
            pretime = datetime.datetime.now()
            print(f"# Time: {pretime}: Generating pattern with command: {com}")
            if not dryrun:
                output_tab = os.popen(command).read()
            posttime = datetime.datetime.now()
            print(f"# Time: {posttime}: Done generating pattern with command: {com}")
            print(f"# Time taken: {(posttime - pretime).total_seconds()} seconds")
            configwise_times[conf] = (posttime - pretime).total_seconds()
            times.append((posttime - pretime).total_seconds())
        
        all_times.append(times)

    print("========================")
    print("Done with Generation")
    print("========================")

    # Write results to JSON file
    if json_results:
        with open(f"{benchname}/all_times.json", "w") as f:
            json.dump(configwise_times, f, indent=4)

    with open(f"{benchname}/all_times.md", "w") as f:
        f.write("### Pattern generation by reuse-buffer size (Figure 12(c))\n\n")
        f.write(tabulate(all_times, headers="firstrow", tablefmt="pretty"))


if __name__ == "__main__":
    main(sys.argv[1:])