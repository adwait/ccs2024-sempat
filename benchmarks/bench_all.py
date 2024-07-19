

"""
    Run all benchmarks
"""


import bench_sv_kocher

import bench_tg_bvssv2
import bench_tg_bvcompre
import bench_tg_synthetic

import bench_sv_fpr


# Figure 11
bench_sv_kocher.main(["bench_sv_kocher"])

# Figure 12
bench_tg_bvssv2.main(["bench_tg_bvssv2"])
bench_tg_bvcompre.main(["bench_tg_bvcompre"])
bench_tg_synthetic.main(["bench_tg_synthetic"])

# Table 5
bench_sv_fpr.main(["bench_sv_fpr"])


# Merge results into a single file
with open('all_results.md', 'w') as outf:
    outf.write(f"# All results:\n---\n\n")
    for f in ["bench_sv_kocher", "bench_tg_bvssv2", "bench_tg_bvcompre", "bench_tg_synthetic", "bench_sv_fpr"]:
        with open(f"{f}/all_times.md", "r") as infile:
            outf.write(infile.read())
            outf.write("\n\n")
