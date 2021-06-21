#!/usr/bin/env python3
import sys
import subprocess

num_repeats = 1
csv_output_file = "../inputs/table1/timings.csv"
table_file = "../table1.txt"

table1_benchmarks = {
    "sorting.minic":                ["Sorting", [[0, 2, 2]]],
    "klargest.minic":               ["k-largest", [[0, 2, 2]]],
    "closest_pair.minic":           ["Closest pair", [[0, 2, 2]]],
    "intersecting_intervals.minic": ["Intersecting intervals", [[0, 2, 2], [0, 3, 3]]],
    "histo.minic":                  ["Histogram", [[0, 2, 2], [2, 2, 2]]],
    "pareto.minic":                 ["POP", [[0, 2, 2], [1, 2, 2], [2, 2, 2], [0, 2, 3]]],
    "minpoints.minic":              ["Minimal points", [[0, 2, 2], [1, 2, 2], [2, 2, 2], [0, 2, 3]]],
    "quadrant.minic":               ["Quadrant Orthogonal Hull", [[0, 2, 2], [1, 2, 2], [2, 2, 2], [0, 2, 3]]],
    "orthohull.minic":              ["Orthogonal Convex Hull*", [[2, 2, 2]]]
}


def run_experiments():
    for _ in range(0, num_repeats):
        for bench_file, opts in table1_benchmarks.items():
            with open(csv_output_file, 'a') as o:
                for k, m, c in opts[1]:
                    subprocess.run(["./Parsynt", ("../inputs/table1/%s" %
                                                  bench_file), "-k", str(k), "-m", str(m), "-c", str(c), "--quiet"],
                                   stdout=o)
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


def first_line_format(bname, fs, budget, ps, ds, js):
    return f"   {bname:.<25s} | {fs:>5s}  | {budget} | {ps: >5s} | {ds:>5s} | {js: >6s}\n"


def line_format(budget, ps, ds, js):
    x = ".."
    return f"..{x:<25s}  |   -    | {budget} | {ps: >5s} | {ds:>5s} | {js: >6s}\n"


def budgetstr(k, m, c):
    return "(%i,%i,%i)" % (k, m, c)


caption = "\
    \tThis table presents the results shown in Table 1 of the paper.\n\
    Times are reported in seconds. For each of the 8 benchmarks, the second \n\
    column reports how much time has been spent synthesizing the single \n\
    pass function (see Appendix C). The budget (Section 5.1) column shows\n\
    the budgets for which a solution is synthesized. For each of the budgets,\n\
    the column p reports how much time is spent synthesizing the predicate,\n\
    the column v reports the synthesis time of the divide function and the\n\
    the column ⊙ the join function.\n"


def write_table(data):
    with open(table_file, 'w') as tbl:
        tbl.write(
            "....Benchmark name ..........| s.pass | Budget  |  p    |   v   |  ⊙   \n")
        tbl.write(
            "------------------------------------------------------------------------\n")
        for key, opts in table1_benchmarks.items():
            name = str(opts[0])
            k0, m0, c0 = opts[1][0]
            if key in data:
                sf = avg_or_unsat(data[key][0])
                ps0, ds0, js0 = "unsat", "unsat", "unsat"
                if (k0, m0, c0) in data[key][1]:
                    ps0 = avg_or_unsat(data[key][1][k0, m0, c0][0])
                    ds0 = avg_or_unsat(data[key][1][k0, m0, c0][1])
                    js0 = avg_or_unsat(data[key][1][k0, m0, c0][2])

                tbl.write(first_line_format(name, sf, budgetstr(
                    k0, m0, c0), ps0, ds0, js0))

                for k, m, c in opts[1][1:]:
                    ps, ds, js = "unsat", "unsat", "unsat"
                    if (k, m, c) in data[key][1]:
                        ps = avg_or_unsat(data[key][1][k, m, c][0])
                        ds = avg_or_unsat(data[key][1][k, m, c][1])
                        js = avg_or_unsat(data[key][1][k, m, c][2])
                        tbl.write(line_format(budgetstr(k, m, c), ps, ds, js))
        tbl.write(
            "------------------------------------------------------------------------\n")
        tbl.write(caption)


def table():
    data = {}
    for key, opts in table1_benchmarks.items():
        bres = {}
        for k, m, c in opts[1]:
            bres[(k, m, c)] = [[], [], []]
        data[key] = [[], bres]

    with open(csv_output_file, 'r') as csv:
        for line in csv.readlines():
            elts = line.strip().split(",")
            if len(elts) == 8:
                key = str(elts[0])
                budget = int(elts[1]), int(elts[2]), int(elts[3])
                if key in data:
                    data[key][0] += [elts[4]]
                    if budget in data[key][1]:
                        data[key][1][budget][0] += [elts[5]]
                        data[key][1][budget][1] += [elts[6]]
                        data[key][1][budget][2] += [elts[7]]

    csv.close()
    write_table(data)


if __name__ == "__main__":
    # plot_pareto_stair_scatter_threads("exp_par_stair_scatter.csv")
    if len(sys.argv) > 1:
        num_repeats = int(sys.argv[1])
    if num_repeats > 0:
        run_experiments()
    table()
