import matplotlib.pyplot as plt
import csv
import math
from statistics import mean
import pandas as pd
import numpy as np


def ps1_chartname(size, ratio, bname):
    return "exp_partition_divide_parallels_n%i_r%i_b%s.pdf" % (size, ratio, bname)


def ps2_chartname(size):
    return "exp_partition_divide_sequentials_(n=%i).pdf" % size


legend_fontsize = 13
axes_fontsize = 13
examples = {
    "pop": 'solid',
    "ins": 'dashed',
}

methods = {
    "par222": ['par', 'red'],
    "par022": ['par', 'blue'],
    "par122": ['par', 'green'],
    "par023": ['par', 'black'],
    "par033": ['par', 'brown'],
    "seq000": ['seq', 'red'],
    "seq111": ['seq', 'pink'],
    "seq022": ['seq', 'blue'],
    "seq122": ['seq', 'green'],
    "seq023": ['seq', 'black'],
    "seq033": ['seq', 'brown'],
    "seq222": ['seq', 'red'],
}

input_sizes = [100000, 500000]

header = ["benchmark_name", "method", "input_size",
          "delta", "num_threads", "time_s",  "speedup_seq_base"]

data_types = {
    'benchmark_name': str,
    'method': str,
    'input_size': int,
    'delta': int,
    'num_threads': int,
    'time_s': np.float64,
    'speedup_seq_base': np.float64
}

data = pd.read_csv("../exp_partition_divide.csv",
                   names=header, dtype=data_types).dropna()

data['speedup_seq_base'] = pd.to_numeric(data['speedup_seq_base'])

data = data.groupby(["benchmark_name", "method", "input_size",
                     "delta", "num_threads"]).mean()

data = data.reset_index()

""" Plot Set #1 : Speedup of Parallel implementations, with varying ratios """
for size in input_sizes:

    sdf = data[data['input_size'] == size].drop(
        columns=['input_size', 'time_s'])

    seqs = sdf[sdf['num_threads'] == 1].drop(columns=['num_threads'])

    seqs = seqs.groupby(['benchmark_name'])

    fig = plt.figure(figsize=(14, 10), dpi=80,
                     facecolor='w', edgecolor='k')
    ax = fig.add_subplot(1, 1, 1)

    for benchn, bench_gp in seqs:
        bgp = bench_gp.drop(columns='benchmark_name').groupby(['method'])

        for method, group in bgp:
            method = method.strip()
            minfo = methods[method]
            group = group.drop(columns=['method'])
            xy = group.to_numpy().transpose()
            x = [(float(x) / size) for x in xy[0]]
            y = [float(x) for x in xy[1]]
            label = "%s - %s" % (benchn.strip(), method)
            ax.plot(x, y, linestyle=examples[benchn.strip()],
                    color=minfo[1], label=label)

    plt.minorticks_on()
    plt.setp(ax.get_xticklabels(), fontsize=axes_fontsize)
    plt.setp(ax.get_yticklabels(), fontsize=axes_fontsize)
    plt.legend(bbox_to_anchor=(0.01, 0.51, 0.45, 1.102), loc=3,
               ncol=2, mode="expand", borderaxespad=0.,
               prop={'size': legend_fontsize})
    ax.set_ylabel('speedup sequential / base',
                  fontsize=axes_fontsize)
    ax.set_xlabel('ratio', fontsize=axes_fontsize)
    ax.grid(b=True, which="major", color=(0.8, 0.8, 0.8))
    ax.grid(b=True, which="minor", color=(0.9, 0.9, 0.9))
    ax.set_xscale("log")
    fig.tight_layout()
    plt.savefig(ps2_chartname(size))

    # Plot 2 : plot sequential methods speedups, compared to base naive algorithm.

    sdf = sdf.groupby(['delta', 'benchmark_name'])

    for delta, delta_gp in sdf:
        bname = delta[1].strip()
        delta = int(delta[0])

        fig = plt.figure(figsize=(14, 10), dpi=80,
                         facecolor='w', edgecolor='k')
        ax = fig.add_subplot(1, 1, 1)

        mdf = delta_gp.drop(
            columns=['benchmark_name', 'delta']).groupby(['method'])

        for method, group in mdf:
            method = method.strip()
            minfo = methods[method]
            gd = group.drop(columns=['method'])
            ar = gd.to_numpy().transpose()
            x = [int(i) for i in ar[0]]
            y = [float(i) for i in ar[1]]

            label = "%s - %s" % (bname, method)
            if minfo[0] == 'par':
                ax.plot(x, y, linestyle='solid', color=minfo[1], label=label)

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
        plt.title("%s with n = %i and %i optimal points " %
                  (bname, size, delta))
        fig.tight_layout()
        plt.savefig(ps1_chartname(size, delta, bname))
        plt.close()
