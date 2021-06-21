#!/usr/bin/env python3
import matplotlib.pyplot as plt
import csv
import math
from statistics import mean


def add_or_append(_dict, _key, _elt):
    if _key in _dict:
        _dict[_key] += [_elt]
    else:
        _dict[_key] = [_elt]


def constr_dict(_list, _keygen):
    _dict = {}
    for x in _list:
        y, z = _keygen(x)
        add_or_append(_dict, y, z)
    return _dict


par_style = {
    'seq0': ['sequential naive ', '-'],
    'seq1': ['seq. d&c 2,0,2   ', '-.'],
    'seq2': ['seq. d&c 2,1,2   ', '-.'],
    'seq3': ['seq. d&c 3,0,2   ', ':'],
    'par0': ['par. d&c 2,2,2   ', '-'],
    'par1': ['par. d&c 2,0,2   ', '-'],
    'par2': ['par. d&c 2,1,2   ', '-'],
    'par3': ['par. d&c 3,0,2   ', '-']
}

axes_fontsize = 15
legend_fontsize = 17


def plot_pareto_stair_scatter_threads(datafile):
    with open(datafile, 'r') as csvfile:
        data = constr_dict(csv.reader(csvfile, delimiter=","),
                           lambda x: (x[0], x[1:]))

    for name, measures in data.items():
        for_size = constr_dict(measures, lambda l: (
            (int(l[1]), int(l[2])), [l[0]] + l[3:]))

        # For each size and radius plot results
        for (size, r), m2 in for_size.items():
            # group by distribution
            by_d = constr_dict(m2,
                               lambda l: (int(l[1]),
                                          [str(l[0]).strip(" "),
                                           int(l[2]), float(l[3]), float(l[4])]))

            chartname = "experiment_%s_size_%i_numpts_%i.pdf" % (name, size, r)
            fig = plt.figure(figsize=(14, 10), dpi=80,
                             facecolor='w', edgecolor='k')
            ax = fig.add_subplot(1, 1, 1)

            for d, d_group in by_d.items():

                div_seq_time = 0.0
                c1, c2 = 0, 0

                par_alg = {}
                for g in d_group:
                    if g[1] > 1:
                        add_or_append(par_alg, g[0], [g[1], g[3]])

                for alg, thread_speedups in par_alg.items():
                    _label = "%s for d = %i" % (alg, d)
                    threads, speedups = zip(*thread_speedups)
                    ax.plot(threads, speedups, label=_label,
                            linestyle=par_style[alg][1])
            plt.minorticks_on()
            plt.setp(ax.get_xticklabels(), fontsize=axes_fontsize)
            plt.setp(ax.get_yticklabels(), fontsize=axes_fontsize)
            plt.legend(bbox_to_anchor=(0.01, 0.51, 0.45, 1.102), loc=3,
                       ncol=2, mode="expand", borderaxespad=0.,
                       prop={'size': legend_fontsize})
            ax.set_ylabel('speedup parallel / sequential',
                          fontsize=axes_fontsize)
            ax.set_xlabel('number of threads', fontsize=axes_fontsize)
            ax.grid(b=True, which="major", color=(0.8, 0.8, 0.8))
            ax.grid(b=True, which="minor", color=(0.9, 0.9, 0.9))
            fig.tight_layout()
            plt.savefig(chartname)
            plt.show()


def plot_for_thread_count(name, size, r, threadcount, t_group):
    chartname = "experiment_%s_size_%i_numpts_threads_%i.pdf" % (
        name, size, threadcount)
    print("Plotting %s ..." % chartname)
    fig = plt.figure(figsize=(7, 4), dpi=80, facecolor='w', edgecolor='k')
    ax = fig.add_subplot(1, 1, 1)

    par_alg = {}
    for g in t_group:
        if g[1] > 1:
            add_or_append(par_alg, g[0], [g[1], g[2]])

    for alg, numpoint_speedups in par_alg.items():
        print(alg)
        _label = "%s" % alg
        spd = constr_dict(numpoint_speedups, lambda l: (l[0] / size, l[1]))
        XY = []
        for optratio, speedups in spd.items():
            print(optratio)
            XY += [[optratio, mean(speedups)]]
        XY.sort(key=(lambda x: x[0]))
        XY = filter(lambda x: x[0] > (30 / size), XY)
        X, Y = zip(*XY)
        ax.plot(X, Y, label=_label, linestyle=par_style[alg][1])

    ax.minorticks_on()
    plt.setp(ax.get_xticklabels(), fontsize=axes_fontsize)
    plt.setp(ax.get_yticklabels(), fontsize=axes_fontsize)
    ax.legend(bbox_to_anchor=(0.51, 0.60, 0.45, 1.102), loc=3,
              ncol=2, mode="expand", borderaxespad=0.,
              prop={'size': legend_fontsize})
    ax.set_ylabel('speedup  / sequential', fontsize=axes_fontsize)
    ax.set_xlabel('ratio of optimal points', fontsize=axes_fontsize)
    ax.grid(b=True, which="major", color=(0.8, 0.8, 0.8))
    ax.grid(b=True, which="minor", color=(0.9, 0.9, 0.9))
    ax.set_xscale("log")
    fig.tight_layout()
    plt.savefig(chartname)
    plt.close()


def plot_pareto_stair_scatter_numpoints(datafile):
    with open(datafile, 'r') as csvfile:
        data = constr_dict(csv.reader(csvfile, delimiter=","),
                           lambda x: (x[0], x[1:]))

    for name, measures in data.items():
        for_size = constr_dict(measures, lambda l: (
            (int(l[1]), int(l[2])), [l[0]] + l[3:]))

        # For each size and radius plot results
        for (size, r), m2 in for_size.items():
            # group by threads
            # by_d = constr_dict(m2,
            #                    lambda l: (int(l[1]),
            #                               [str(l[0]).strip(" "),
            #                                int(l[2]), float(l[3]), float(l[4])]))
            by_threadcount = constr_dict(m2, lambda l: (int(l[2]),  # threadcount
                                                        [str(l[0]).strip(" "),  # algorithm
                                                         # numpoints
                                                         int(l[1]),
                                                         float(l[4])]  # speedup
                                                        ))

            for threadcount, t_group in by_threadcount.items():
                if threadcount == 2:
                    plot_for_thread_count(name, size, r, threadcount, t_group)


if __name__ == "__main__":
    # plot_pareto_stair_scatter_threads("exp_par_stair_scatter.csv")
    plot_pareto_stair_scatter_numpoints("exp_par_stair_scatter.csv")
