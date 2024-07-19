

import os
import sys
import json
import datetime
import argparse
from tabulate import tabulate, SEPARATING_LINE

CHECKTIMEOUT = 900  # 15 minutes

TEST_ABSPATH = os.getcwd()

from fpr_examples import fpr_examples_runcommand as fpr

configwise_times = {}

lsqc_check_sweep = [1, 2, 3]


def main(args):

    parser = argparse.ArgumentParser()
    # Grab benchname from argparse
    parser.add_argument("benchname", help="Name of benchmark directory (also used as directory to place results into).", type=str)
    # grab non-sanity (dry-run) from argparse
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

    all_times = [["Test", "Set-index\nwidth", "K", "Pat. F (Fig. 13)\nRuntime (s)", "Pattern F\nResult", "Pattern G (Fig. 13)\nRuntime (s)", "Pattern G\nResult"]]


    for setind in lsqc_check_sweep:
        all_times.append(SEPARATING_LINE)
        tab1_cmds = fpr.secant_xtab_commands(TEST_ABSPATH, benchname, 32, setind, 1, 1)
        tab0_cmds = fpr.secant_xtab_commands(TEST_ABSPATH, benchname, 32, setind, 1, 0)
        for (tab0_cmd, tab1_cmd) in zip(tab0_cmds, tab1_cmds):
            
            (test, conf, com, k) = tab0_cmd

            times = [f"test{test}", setind, k]

            command = f"timeout -s 9 {CHECKTIMEOUT} {com}"
            pretime = datetime.datetime.now()
            print(f"# Time: {pretime}: Checking using pattern with command: {com}")
            tc0_failed = False
            if not dryrun:
                output_tab = os.popen(command).read()
                tc0_failed = 'FAILED' in output_tab
            posttime = datetime.datetime.now()
            print(f"# Time: {posttime}: Done checking using pattern with command: {com}")
            print(f"# Time taken: {(posttime - pretime).total_seconds()} seconds")
            configwise_times[conf] = (posttime - pretime).total_seconds()

            times.append((posttime - pretime).total_seconds())
            times.append('UNSAFE' if tc0_failed else 'SAFE')

            (test, conf, com, k) = tab1_cmd
            command = f"timeout -s 9 {CHECKTIMEOUT} {com}"
            pretime = datetime.datetime.now()
            print(f"# Time: {pretime}: Checking using pattern with command: {com}")
            tc1_failed = False
            if not dryrun:
                output_tab = os.popen(command).read()
                tc1_failed = 'FAILED' in output_tab
            posttime = datetime.datetime.now()
            print(f"# Time: {posttime}: Done checking using pattern with command: {com}")
            print(f"# Time taken: {(posttime - pretime).total_seconds()} seconds")
            configwise_times[conf] = (posttime - pretime).total_seconds()
            times.append((posttime - pretime).total_seconds())
            times.append('UNSAFE' if tc1_failed else 'SAFE')

            all_times.append(times)

    print("========================")
    print("Done with Checking")
    print("========================")

    # Write results to JSON file
    if json_results:
        with open(f"{benchname}/all_times.json", "w") as f:
            json.dump(configwise_times, f, indent=4)

    with open(f"{benchname}/all_times.md", "w") as f:
        f.write("### False positive tests (Table 5)\n\n")
        f.write(tabulate(all_times, headers="firstrow", tablefmt="pretty"))



if __name__ == "__main__":
    main(sys.argv[1:])
