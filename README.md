
# Artifact for CCS 24: SemPat: Using Hyperproperty-based Semantic Analysis to Generate Microarchitectural Attack Patterns

Paper (arXiV Version): https://arxiv.org/abs/2406.05403

Contact: Adwait Godbole, UC Berkeley (adwait@berkeley.edu)

---

## Setup

### Requirements

1. **Scala and SBT**: We have built/tested with OpenJDK 11, Scala 2.12.11 and SBT 1.4.2. Probably the easiest way to install these is using SDKMAN: https://sdkman.io/.


2. **Z3**: SECANT requires the Z3 SMT solver: https://github.com/Z3Prover/z3. We have tested with `z3` version 4.8.8. The convenience script `secant/get-z3-linux.sh` downloads and installs `z3`, (run: `source get-z3-linux.sh`). The helper sub-script `secant/setup-z3-linux.sh` adds the Z3 binary/libraries to `$PATH`.


3. **Python3**: Benchmark scripts have been tested with Python3 (3.5+ should suffice) and require the tabulate package: `pip install tabulate` (for pretty-printing results).


### Building from source

1. Run the command: `sbt clean compile universal:packageBin` from the `secant` directory.

2. The build targets are placed  tool can be found in the `secant/target/universal` directory. The convienence script `secant/unpack-secant.sh` can be used to extract the binary. Please add the binary location `secant/target/universal/secant-0.0.1/bin` to your `$PATH` variable.


---

## Benchmarks

The `benchmarks` directory provides convenience scripts to run all the examples. There are 5 scripts:

1. `bench_sv_kocher.py` (for Figure 11)
2. `bench_tg_bvssv2.py`, `bench_tg_bvcompre.py`, `bench_tg_synthetic.py` (for Figure 12)
3. `bench_sv_fpr.py` (for Table 5)

Further the super-script `bench_all.py` calls all these scripts in order and combines the results into a single file (this may take 6-7 hours to run).

Each script can be called individually (from `benchmarks`) as: `python3 <scriptname> <resultsdir> [--dryrun]` where results are placed in `<resultsdir>`, and the `--dryrun` flag performs a dry-run without actually calling the tool. Running the script produces a table `all_times.md` in `<resultsdir>`. 

We now list the scripts, with estimated runtime and results to validate.

### Kocher's Modified Tests (Figure 11)

**bench_sv_kocher (Figure 11)**: Run command `python3 bench_sv_kocher.py bench_sv_kocher` from `benchmarks`. Time estimate: ~3 hours.

This scripts perform verification using both hyperproperties and patterns for modified Kocher's benchmarks (Figure 11). In particular check that:
1. All generation times have reasonably precise order magnitude
2. Run-time with hyperproperties dominates that with patterns and that the results match.
3. The claim that larger platform complexity affects hyperproperty time, but does not affect pattern generation time.


### Pattern Generation Scalability (Figure 12)


**bench_tg_bvssv2 (Figure 12(a,b))**: Run command `python3 bench_tg_bvssv2.py bench_tg_bvssv2` from `benchmarks`. Time estimate: ~3 hours.

**bench_tg_compre (Figure 12(c))**: Run command: `python3 bench_tg_compre.py bench_tg_compre`. Time estimate: ~20 minutes.


**bench_tg_synthetic (Figure 12(d))**: Run command `python3 bench_tg_synthetic.py bench_tg_synthetic` from `benchmarks`. Time estimate: ~15 minutes.

These scripts perform pattern generation (and are used for) produce results for Figure 12. In particular check that:
1. All generation times have reasonably precise order magnitude.
2. Run-time with increasing set-index grows faster than that with way-index (Figure 12(a,b) with `bench_tg_bvssv2`).  


### False Positive Experiment (Table 5)

**bench_sv_fpr (Figure 11)**: Run command `python3 bench_sv_fpr.py bench_sv_fpr` from `benchmarks`. Time estimate: ~5 minutes.

This scripts performs verification of a set of litmus tests using two versions of a pattern: one that is more coarse and one that includes finer predicates (see Section 7.3). Check that:
1. The results match Table 5: in particular, false positives (`UNSAFE` results) occur when using pattern F (Figure 13) with $K > \texttt{setindex}$.

---