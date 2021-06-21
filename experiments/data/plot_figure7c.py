#!/usr/bin/env python3
import matplotlib.pyplot as plt
import csv
import math
from statistics import mean
import sys


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


axes_fontsize = 13
legend_fontsize = 13

threadNumFilter = [2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16]
methodName = {"par0": "Lifted", "par1": "Splitting"}
methodColor = {"par0": "#B00020", "par1": "#3700B3"}
sizeLineStyle = {1: ':',
                 2: (0, (2, 10)),
                 3: (0, (3, 9)),
                 4: (0, (4, 8)),
                 5: (0, (5, 10)),
                 6: (0, (6, 5)),
                 7: (0, (5, 1)),
                 8: '-.',
                 9: '-'}

# lis       ,      par1,         100000,         0,         8, 0.0001696,   2.70873
nameIndex = 0
methodIndex = 1
sizeIndex = 2
distrIndex = 3
numThreadsIndex = 4
speedupIndex = 6


def plot_for_size(name, size, s_measures, sizeFilter):
    fig = plt.figure(figsize=(7, 5), dpi=80, facecolor='w', edgecolor='k')
    ax = fig.add_subplot(1, 1, 1)
    chartname = "lis_n=%i.pdf" % size
    print(chartname)
    for_method = constr_dict(s_measures, lambda l: (l[methodIndex], l))

    for method, m_measures in for_method.items():
        method = method.strip()
        if not (method == "seq0"):
            for_distr = constr_dict(m_measures,
                                    lambda l: (int(l[distrIndex]),
                                               [int(l[numThreadsIndex]), float(l[speedupIndex])]))

            for distr, d_measures in for_distr.items():
                distrNum = math.log10(distr)
                if distrNum in sizeFilter:
                    for_thread = constr_dict(
                        d_measures, lambda l: (l[0], l[1]))
                    plot_data = []
                    for tc, speedups in for_thread.items():
                        if tc in threadNumFilter:
                            plot_data += [(tc, mean(speedups))]
                    threads, speedups = zip(*plot_data)
                    _label = "%s (%1.2f)" % (
                        methodName[method], float(math.log10(distr) / math.log10(size)) * 0.75)
                    ax.plot(threads, speedups,
                            color=methodColor[method],
                            label=_label,
                            linestyle=sizeLineStyle[distrNum])

            # plt.minorticks_on()
    plt.setp(ax.get_xticklabels(), fontsize=axes_fontsize)
    plt.setp(ax.get_yticklabels(), fontsize=axes_fontsize)
    plt.legend(bbox_to_anchor=(0.01, 0.75, 0.60, 1.102), loc=3,
               ncol=2, mode="expand", borderaxespad=0.,
               prop={'size': legend_fontsize})
    ax.set_ylabel('speedup parallel / sequential', fontsize=axes_fontsize)
    ax.set_xlabel('number of threads', fontsize=axes_fontsize)
    ax.grid(b=True, which="major", color=(0.8, 0.8, 0.8))
    ax.axhline(y=1, color=(0.9, 0.9, 0.9))
    ax.margins(x=0.01)
    # ax.grid(b=True, which="minor", color=(0.9, 0.9, 0.9))
    fig.tight_layout(pad=0.05)
    plt.savefig(chartname)
    return chartname


def plot_lis(datafile, nofilter=False):
    chartNames = []
    sizeFilter = [1, 5, 7, 8, 9]
    if nofilter:
        sizeFilter = [1, 2, 3, 4, 5, 6, 7, 8, 9]

    with open(datafile, 'r') as csvfile:
        data = constr_dict(csv.reader(csvfile, delimiter=","),
                           lambda x: (x[nameIndex], x))

    for name, measures in data.items():
        for_size = constr_dict(measures, lambda l: (int(l[sizeIndex]), l))

        for size, s_measures in for_size.items():
            chartNames.append(plot_for_size(
                name, size, s_measures, sizeFilter))
    return chartNames


if __name__ == "__main__":
    # plot_pareto_stair_scatter_threads("exp_par_stair_scatter.csv")
    if len(sys.argv) < 2:
        print("Usage: python3 plot_figure7c.py CSV_INPUT_FILE")
    else:
        csvInputFileName = sys.argv[1].strip()
        plot_lis(csvInputFileName, nofilter=(len(sys.argv) > 2))
