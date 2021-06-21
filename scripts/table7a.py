#!/usr/bin/env python3
import sys
import subprocess
import re

num_repeats = 1
csv_output_file = "inputs/table7a/timings.csv"
table_file = "table7a.txt"

table7a_benchmarks = {
    "cozp.minic":    ["Count 1(0+)", ["--no-break"]],
    "cozst.minic":   ["Count 1(0*)2", ["--no-break"]],
    "coststs.minic": ["Count 1*2*3", []],
    "mdbo.minic":    ["Max dist. between 1s", ["--no-break"]],
    "msbz.minic":    ["Max dist. between 0s", []],
    "lis.minic":     ["LIS", []],
    "lmo.minic":     ["Largest peak", []],
    "los.minic":     ["Longest 1*", []],
    "lozst.minic":   ["Longest 1(0*)2", []],
    "lezs.minic":    ["Longest even 0*", []],
    "lozos.minic":   ["Longest odd (01)*", []],
}


def run_experiments():
    for _ in range(0, num_repeats):
        with open(csv_output_file, 'a') as o:
            for bench_file, args in table7a_benchmarks.items():
                subprocess.run(["./Parsynt", ("inputs/table7a/%s" %
                                              bench_file), "--quiet"] + args[1], stdout=o)
        o.close()


def avg_or_unsat(nums):
    n = len(nums)
    if n <= 0:
        return "NaN"
    s = 0.0
    for x in nums:
        if x == "unsat" or x == "err":
            return x
        s += float(x)
    return "%.1f" % (s / n)


def line_format(bname, ps, js):
    return f"..{bname:.<21s}|{ps: >5s}  |{js: >6s}\n"


caption = "\
       This table presents the results\n\
    in Table 7(a) of the paper. Times\n\
    are reported in seconds. For each\n\
    of the 11 benchmarks, the second\n\
    column (p + v) indicates how much\n\
    time is spent synthesizing the \n\
    predicate and the lifted function.\n\
    The third column ( ⊙ ) reports the\n\
    join synthesis time.\n"


def write_table(data):
    with open(table_file, 'w') as tbl:
        tbl.write("..Benchmark name ......| p + v |  ⊙   \n")
        tbl.write("--------------------------------------\n")
        for key, args in table7a_benchmarks.items():
            long_name = str(args[0])
            psynt = avg_or_unsat(data[key][0])
            jsynt = avg_or_unsat(data[key][1])
            tbl.write(line_format(long_name, psynt, jsynt))
        tbl.write("--------------------------------------\n")
        tbl.write(caption)


def table():
    data = {}
    for key, _ in table7a_benchmarks.items():
        data[key] = [[], []]

    with open(csv_output_file, 'r') as csv:
        for line in csv.readlines():
            elts = line.strip().split(",")
            if len(elts) == 8:
                data[str(elts[0])][0] += [elts[5]]
                data[str(elts[0])][1] += [elts[7]]
    csv.close()
    write_table(data)


if __name__ == "__main__":
    # plot_pareto_stair_scatter_threads("exp_par_stair_scatter.csv")
    if len(sys.argv) > 1:
        num_repeats = int(sys.argv[1])
    if num_repeats > 0:
        run_experiments()
    table()
