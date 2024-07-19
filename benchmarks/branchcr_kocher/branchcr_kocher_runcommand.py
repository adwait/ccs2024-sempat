import sys


PLATFORM = "bvbranchcr"
TGENERATOR = "bvbranchcr:tg"
ANALYZER = "bvbranchcr:an"

FILEDIR  = "branchcr_kocher"

COMMANDS = {
    "1": (66024, 65920, 3)
    , "2": (66100, 65988, 4)
    , "3": (66100, 65988, 4)
    , "4": (66032, 65920, 3)
    , "5": (66064, 65920, 4)
    , "5b": (66064, 65920, 4)
    , "6": (66044, 65920, 3)
    , "7": (66052, 65920, 4)
    , "8": (66032, 65920, 4)
}

def get_platform_config(ww, has_cache, cindex, assoc):
    return f"-q word_width={ww},has_cache={has_cache},cache_index_width={cindex},full_assoc={assoc}"

def get_config_name (benchname, checktype, ww, has_cache, cindex, assoc):
    return f"{benchname}_{PLATFORM}_{checktype}_ww{ww}_cwidth{cindex}_assoc{assoc}"


def secant_tg_command (benchname, ww, has_cache, cindex, assoc):
    config = get_config_name(benchname, 'tg', ww, has_cache, cindex, assoc)
    return (config, f"secant --verbosity 3 -s {config} -c syntab -p {PLATFORM} {get_platform_config(ww, has_cache, cindex, assoc)} -a {TGENERATOR}")

def secant_xhyp_commands(abspath, benchname, ww, has_cache, cindex, assoc):
    checks = []
    for i in COMMANDS:
        startloc = COMMANDS[i][1]
        limit = COMMANDS[i][2]
        config = get_config_name(benchname, f"xhyp_test{i}", ww, has_cache, cindex, assoc)
        checks.append((i, config, f'secant --verbosity 3 -s {config} -c xhyp -p {PLATFORM} {get_platform_config(ww, has_cache, cindex, assoc)} -a {ANALYZER} -f {abspath}/{FILEDIR}/virfiles/test{i}.vir:{startloc}:{limit} -t {abspath}/{FILEDIR}/tcontexts/test{i}/taintcontext_{startloc}.json'))
    return checks


def secant_xtab_commands(abspath, benchname, ww, has_cache, cindex, assoc):
    checks = []
    for i in COMMANDS:
        startloc = COMMANDS[i][1]
        limit = COMMANDS[i][2]
        config = get_config_name(benchname, f"xtab_test{i}", ww, has_cache, cindex, assoc)
        checks.append((i, config, f'secant --verbosity 3 -s {config} -c xtab -p {PLATFORM} {get_platform_config(ww, has_cache, cindex, assoc)} -a {ANALYZER} -b matcher=2 -f {abspath}/{FILEDIR}/virfiles/test{i}.vir:{startloc}:{limit} -t {abspath}/{FILEDIR}/tcontexts/test{i}/taintcontext_{startloc}.json'))
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