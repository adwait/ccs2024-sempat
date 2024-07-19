import sys


PLATFORM = "bvlsqc"
TGENERATOR = "bvlsqc:tg"
ANALYZER = "bvlsqc:an"

FILEDIR  = "fpr_examples"

COMMANDS = {
    # "1": (65920, 65920, 1, "-")
    "2": (65920, 65920, 1, "-")
    , "3": (65920, 65920, 1, "0")
    , "4": (65920, 65920, 1, "1")
    , "5": (65920, 65920, 1, "2")
    , "6": (65920, 65920, 1, "3")
    , "7": (65920, 65920, 1, "4")
    , "8": (65920, 65920, 1, "5")
    , "9": (65920, 65920, 1, "6")
}

def get_platform_config(ww, setind, wayind):
    return f"-q word_width={ww},lsqc_setind_width={setind},lsqc_wayind_width={wayind}"

def get_analysis_config(tabchoice):
    return f"-b matcher=2,tabchoice={tabchoice},spectype=1"


def get_config_name (benchname, checktype, ww, setind, wayind, tabchoice):
    return f"{benchname}_{checktype}_ww{ww}_setind{setind}_wayind{wayind}_tabchoice{tabchoice}"

def secant_tg_command (benchname, ww, setind, wayind):
    config = get_config_name(benchname, 'tg', ww, setind, wayind, 0)
    return (config, f"secant --verbosity 3 -s {config} -c syntab -p {PLATFORM} {get_platform_config(ww, setind, wayind)} -a {TGENERATOR} {get_analysis_config(0)}")

# def secant_xhyp_commands(abspath, benchname, ww, has_cache, cindex, assoc):
#     checks = []
#     for i in COMMANDS:
#         startloc = COMMANDS[i][1]
#         limit = COMMANDS[i][2]
#         config = get_config_name(benchname, f"xhyp_test{i}", ww, has_cache, cindex, assoc)
#         checks.append((config, f'secant --verbosity 3 -s {config} -c xhyp -p {PLATFORM} {get_platform_config(ww, has_cache, cindex, assoc)} -a {ANALYZER} -f {abspath}/{FILEDIR}/virfiles/test{i}.vir:{startloc}:{limit} -t {abspath}/{FILEDIR}/tcontexts/test{i}/taintcontext_{startloc}.json'))
#     return checks


def secant_xtab_commands(abspath, benchname, ww, setind, wayind, tabchoice):
    checks = []
    for i in COMMANDS:
        startloc = COMMANDS[i][1]
        limit = COMMANDS[i][2]
        config = get_config_name(benchname, f"xtab_test{i}", ww, setind, wayind, tabchoice)
        checks.append((i, config, f'secant --verbosity 3 -s {config} -c xtab -p {PLATFORM} {get_platform_config(ww, setind, wayind)} -a {ANALYZER} {get_analysis_config(tabchoice)} -f {abspath}/{FILEDIR}/virfiles/test{i}.vir:{startloc}:{limit} -t {abspath}/{FILEDIR}/tcontexts/test{i}/taintcontext_{startloc}.json', COMMANDS[i][3]))
    return checks

def get_command(i, abspath):
    startloc = COMMANDS[i][1]
    limit = COMMANDS[i][2]
    # print(startloc)
    print("Taint generation command")
    print(f'run -v 3 -c taint -p {PLATFORM} -a {ANALYZER} -f {abspath}/{FILEDIR}/virfiles/test{i}.vir -t {abspath}/{FILEDIR}/test{i}_init.json -u {abspath}/{FILEDIR}/tcontexts/test{i}/ -l {limit}')

    print("Run hyperproperty-based check command")
    print(f'run -v 3 -c xhyp -p {PLATFORM} -a {ANALYZER} -f {abspath}/{FILEDIR}/virfiles/test{i}.vir:{startloc}:{limit} -t {abspath}/{FILEDIR}/tcontexts/test{i}/taintcontext_{startloc}.json')

    print("Run pattern-based check command")
    print(f'run -v 3 -c xtab -p {PLATFORM} -q lsqc_ishashed=1,lsqc_setind_width=1 -a {ANALYZER} -b matcher=2 -f {abspath}/{FILEDIR}/virfiles/test{i}.vir:{startloc}:{limit} -t {abspath}/{FILEDIR}/tcontexts/test{i}/taintcontext_{startloc}.json')

    print("Run pattern-based check command with fine-grained pattern")
    print(f'run -v 3 -c xtab -p {PLATFORM} -q lsqc_ishashed=1,lsqc_setind_width=1 -a {ANALYZER} -b matcher=2,tabchoice=1 -f {abspath}/{FILEDIR}/virfiles/test{i}.vir:{startloc}:{limit} -t {abspath}/{FILEDIR}/tcontexts/test{i}/taintcontext_{startloc}.json')


def main (arg):
    print("Run command:")
    get_command(arg[0], arg[1])
    

if __name__ == '__main__':
    main(sys.argv[1:])