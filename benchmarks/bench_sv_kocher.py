
import os
import sys
import logging
import datetime
import json
import argparse
from tabulate import tabulate

TIMEOUT = 900 # 15 minutes

# Get present working directory
TEST_ABSPATH = os.getcwd()

from branchcr_kocher import branchcr_kocher_runcommand as bcr 
from stlcr_kocher import stlcr_kocher_runcommand as scr


# Word width
WW = 32

config_wise_times = {}

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


    bcr_times = [["Test case", "Hyperproperty (assoc=0)\nruntime (s)", "Pattern (assoc=0)\nruntime (s)", \
                  "Hyperproperty (assoc=1)\nruntime (s)", "Pattern (assoc=1)\nruntime (s)"]]
        
    # Check with hyperproperty/pattern for both associativities
    
    xhyp_checks_assoc0 = bcr.secant_xhyp_commands(TEST_ABSPATH, benchname, WW, 1, 1, 0)
    xtab_checks_assoc0 = bcr.secant_xtab_commands(TEST_ABSPATH, benchname, WW, 1, 1, 0)

    xhyp_checks_assoc1 = bcr.secant_xhyp_commands(TEST_ABSPATH, benchname, WW, 1, 1, 1)
    xtab_checks_assoc1 = bcr.secant_xtab_commands(TEST_ABSPATH, benchname, WW, 1, 1, 1)
    
    for (xh0, xt0, xh1, xt1) in zip(xhyp_checks_assoc0, xtab_checks_assoc0, xhyp_checks_assoc1, xtab_checks_assoc1):
        (test, conf, com) = xh0
        
        times = [f"test{test}"]

        
        for check in [xh0, xt0, xh1, xt1]:
            (test, conf, com) = check
            command = f"timeout -s 9 {TIMEOUT} {com}"
            pretime = datetime.datetime.now()
            print(f"# Time: {pretime}: Checking properties with command: {com}")
            if not dryrun:
                output_tab = os.popen(command).read()
            posttime = datetime.datetime.now()
            config_wise_times[conf] = (posttime - pretime).total_seconds()
            times.append((posttime - pretime).total_seconds())

        bcr_times.append(times)

    print("======================")
    print("Done with BCR Checking")
    print("======================")

    stlcr_times = [["Test case", "Hyperproperty \nruntime (s)", "Pattern \nruntime (s)"]]

    xhyp_checks = scr.secant_xhyp_commands(TEST_ABSPATH, benchname, WW)
    xtab_checks = scr.secant_xtab_commands(TEST_ABSPATH, benchname, WW)
    
    for (xh, xt) in zip(xhyp_checks, xtab_checks):
    
        (test, conf, com) = xh
        times = [f"test{test}"]

        for check in [xh, xt]:
            (test, conf, com) = check
            command = f"timeout -s 9 {TIMEOUT} {com}"
            pretime = datetime.datetime.now()
            print(f"# Time: {pretime}: Checking properties with command: {com}")
            if not dryrun:
                output_tab = os.popen(command).read()
            posttime = datetime.datetime.now()

            config_wise_times[conf] = (posttime - pretime).total_seconds()
            times.append((posttime - pretime).total_seconds())

        stlcr_times.append(times)

    print("========================")
    print("Done with STLCR Checking")
    print("========================")
    
    if json_results:
        with open(f"{benchname}/all_times.json", 'w') as f:
            f.write(json.dumps(config_wise_times))

    with open(f"{benchname}/all_times.md", 'w') as f:
        f.write("### Branch + Computation Reuse Tests (Figure 11)\n\n")
        f.write(tabulate(bcr_times, headers="firstrow", tablefmt="pretty"))

        f.write("\n\n")

        f.write("### STL + Computation Reuse Tests (Figure 11)\n\n")
        f.write(tabulate(stlcr_times, headers="firstrow", tablefmt="pretty"))


if __name__ == "__main__":
    main(sys.argv[1:])
