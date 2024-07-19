

import os
import sys
import json
import datetime
import argparse
from tabulate import tabulate

TIMEOUT = 1800

WW = 16
SPECTYPE = 1
DEPTHS = [3, 4]

wayw_sweep = [1, 2, 3, 4, 5, 6]

setw_sweep = [1, 2, 3, 4, 5, 6]

configwise_times = {}

def get_tg_config (benchname, way_width, set_width, depth):
    return f"{benchname}_setind{set_width}_wayind{way_width}_depth{depth}"

# Generate Patterns for the LSQ Cache-based Silent Stores Platform
def bvssv2_tg_command (benchname, way_width, set_width, depth):
    config = get_tg_config(benchname, way_width, set_width, depth)
    command = f"secant --verbosity 3 -c syntab -s {config} -p bvssv2 -q word_width={WW},lsqc_setind_width={set_width},lsqc_wayind_width={way_width},is_load=1, -a bvssv2:tg -b grammardepth={depth},spectype={SPECTYPE}"
    return (config, command)


# run generation for all configs
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

    set_times = [["Set-index width", "Generation time (s) with\ngrammar depth = 3", "Generation time (s) with\ngrammar depth = 4"]]

    for setwidth in setw_sweep:
        times = [setwidth]
        for depth in DEPTHS:
            (conf, com) = bvssv2_tg_command(benchname, 1, setwidth, depth)
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
        set_times.append(times)

    

    way_times = [["Way-index width", "Generation time (s) with\ngrammar depth = 3", "Generation time (s) with\ngrammar depth = 4"]]

    for waywidth in wayw_sweep:
        times = [waywidth]
        for depth in DEPTHS:
            (conf, com) = bvssv2_tg_command(benchname, waywidth, 1, depth)
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
        way_times.append(times)


    print("========================")
    print("Done with Generation")
    print("========================")

    # Write results to JSON file
    if json_results:
        with open(f"{benchname}/all_times.json", "w") as f:
            json.dump(configwise_times, f, indent=4)

    with open(f"{benchname}/all_times.md", "w") as f:
        f.write("### Pattern generation by set-index width (Figure 12(a))\n\n")
        f.write(tabulate(set_times, headers="firstrow", tablefmt="pretty"))
        f.write("\n\n")
        f.write("### Pattern generation by way-index width (Figure 12(b))\n\n")
        f.write(tabulate(way_times, headers="firstrow", tablefmt="pretty"))

if __name__ == "__main__":
    main(sys.argv[1:])
