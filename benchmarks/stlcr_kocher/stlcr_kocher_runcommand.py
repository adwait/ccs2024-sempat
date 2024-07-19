import sys


PLATFORM = "bvstlcr1"
ANALYZER = "bvstlcr1:an"
TGENERATOR = "bvstlcr1:tg"

FILEDIR  = "stlcr_kocher"

COMMANDS = {
    "1": (66032, 65920, 3)
    , "2": (66048, 65920, 3)
    , "3": (66044, 65920, 3)
    , "4": (66052, 65920, 3)
}

def get_platform_config(ww):
    return f"-q word_width={ww}"
    
def get_config_name (benchname, checktype, ww):
    return f"{benchname}_{PLATFORM}_{checktype}_ww{ww}"

def secant_tg_command (benchname, ww):
    config = get_config_name(benchname, 'tg', ww)
    return (config, f"secant --verbosity 3 -s {config} -c syntab -p {PLATFORM} {get_platform_config(ww)} -a {TGENERATOR}")

def secant_xhyp_commands(abspath, benchname, ww):
    checks = []
    for i in COMMANDS:
        startloc = COMMANDS[i][1]
        limit = COMMANDS[i][2]
        config = get_config_name(benchname, f"xhyp_test{i}", ww)
        checks.append((i, config, f'secant --verbosity 3 -s {config} -c xhyp -p {PLATFORM} {get_platform_config(ww)} -a {ANALYZER} -f {abspath}/{FILEDIR}/virfiles/test{i}.vir:{startloc}:{limit} -t {abspath}/{FILEDIR}/tcontexts/test{i}/taintcontext_{startloc}.json'))
    return checks

def secant_xtab_commands(abspath, benchname, ww):
    checks = []
    for i in COMMANDS:
        startloc = COMMANDS[i][1]
        limit = COMMANDS[i][2]
        config = get_config_name(benchname, f"xtab_test{i}", ww)
        checks.append((i, config, f'secant --verbosity 3 -s {config} -c xtab -p {PLATFORM} {get_platform_config(ww)} -a {ANALYZER} -b matcher=2 -f {abspath}/{FILEDIR}/virfiles/test{i}.vir:{startloc}:{limit} -t {abspath}/{FILEDIR}/tcontexts/test{i}/taintcontext_{startloc}.json'))
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
    print(f'run -v 3 -c xtab -p {PLATFORM} -a {ANALYZER} -b matcher=2 -f {abspath}/{FILEDIR}/virfiles/test{i}.vir:{startloc}:{limit} -t {abspath}/{FILEDIR}/tcontexts/test{i}/taintcontext_{startloc}.json')


def main (arg):
    print("Run command:")
    get_command(arg[0], arg[1])
    

if __name__ == '__main__':
    main(sys.argv[1:])