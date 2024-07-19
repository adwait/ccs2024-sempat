

import os
import sys
import json
import datetime
import argparse

TGTIMEOUT = 3600
CHECKTIMEOUT = 1500


PLATFORM = "bvlsqc"
TGENERATOR = "bvlsqc:tg"
ANALYZER = "bvlsqc:an"

def get_platform_config(ww, setind, wayind):
    return f"-q word_width={ww},lsqc_setind_width={setind},lsqc_wayind_width={wayind}"

def get_analysis_config(tabchoice):
    return f"-b matcher=2,tabchoice={tabchoice},spectype=1"


def get_config_name (benchname, checktype, ww, setind, wayind, tabchoice):
    return f"{benchname}_{checktype}_ww{ww}_setind{setind}_wayind{wayind}_tabchoice{tabchoice}"

def secant_tg_command (benchname, ww, setind, wayind):
    config = get_config_name(benchname, 'tg', ww, setind, wayind, 0)
    return (config, f"secant --verbosity 3 -s {config} -c syntab -p {PLATFORM} {get_platform_config(ww, setind, wayind)} -a {TGENERATOR} {get_analysis_config(0)}")

configwise_times = {}

lsqc_check_sweep = [
     (1, 1), (1, 2), (1, 3), (2, 1), (3, 1)
]

lsqc_gen_sweep = [(1, 1)]

# run generation for all configs
def main(args):

    print("# Generating tableau for BVLSQC")

    parser = argparse.ArgumentParser()
    # Grab benchname from argparse
    parser.add_argument("benchname", help="Name of the benchmark directory", type=str)
    # grab non-sanity (dry-run) from argparse
    parser.add_argument("--dryrun", help="Dry-run mode", dest="non_sanity", action="store_false")
    parser.set_defaults(non_sanity=True)
    
    args = parser.parse_args(args)
    benchname = args.benchname
    non_sanity = args.non_sanity

    # Make directory for benchmark
    os.makedirs(benchname, exist_ok=False)

    # Depth based generation
    for setind, wayind in lsqc_gen_sweep:
        (conf, com) = secant_tg_command(benchname, 8, setind, wayind)
        command = f"timeout -s 9 {TGTIMEOUT} {com}"
        pretime = datetime.datetime.now()
        print(f"# Time: {pretime}: Generating tableau with command: {com}")
        if non_sanity:
            output_tab = os.popen(command).read()
        posttime = datetime.datetime.now()
        print(f"# Time: {posttime}: Done generating tableau with command: {com}")
        print(f"# Time taken: {(posttime - pretime).total_seconds()} seconds")
        configwise_times[conf] = (posttime - pretime).total_seconds()

    print("========================")
    print("Done with Generation")
    print("========================")

    # Write results to JSON file
    with open(f"{benchname}/all_times.json", "w") as f:
        json.dump(configwise_times, f, indent=4)



if __name__ == "__main__":
    main(sys.argv[1:])
