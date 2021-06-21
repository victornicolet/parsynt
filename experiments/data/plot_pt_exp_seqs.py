#!/usr/bin/env python3
from matplotlib import rcParams
import matplotlib.pyplot as plt
import csv
import math
from statistics import mean
import pandas as pd
import numpy as np
import argparse
import os

_description = "Plot graphs for performance of sequential implementations of Pareto."
_default_input_csv = "./data/pop_data.csv"
_default_size = 100000
rcParams['font.family'] = 'monospace'
legend_fontsize = 13
axes_fontsize = 13
examples = {
    "pop": 'solid',
    "ins": 'dashed',
}


def ps2_chartname(expname, size):
    chartname = "data/exp_%s_%i.pdf" % (expname, size)
    print("Output in %s" % chartname)
    return chartname


""" Methods contains information about each method for plotting.
    Keys are the method codes.
"""
methods = {
    "par222": ['par', 'red',       'Parallel - B = (2, 2, 2)'],
    "par022": ['par', 'blue',      'Parallel - B = (0, 2, 2)'],
    "par122": ['par', 'green',     'Parallel - B = (1, 2, 2)'],
    "par033": ['par', 'brown',     'Parallel - B = (0, 3, 3)'],
    "par023": ['par', 'brown',     'Parallel - B = (0, 2, 3)'],
    "par100": ['par', 'teal', 'Parallel - Sort & Conquer'],
    # "seq000": ['seq', 'red',       'Default sequential (linear)'],
    # "seq111": ['seq', 'pink',      'Default sequential (quadratic)'],
    "seq022": ['seq', 'blue',      'B = (0,2,2)'],
    "seq122": ['seq', 'green',     'B = (1,2,2)'],
    "seq023": ['seq', 'black',     'B = (0,2,3)'],
    # "seq033": ['seq', 'brown',     'B = (0,3,3)'],
    "seq222": ['seq', 'red',       'B = (2,2,2)'],
    # "seq100": ['seq', 'teal', 'sort and conquer'],
}

input_sizes = [100000, 500000, 30000, 20000, 15000, 10000]

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


def plot(expname, input_csv, input_size, plot_error_bars, display=False, xlabel='ratio optimal points / total points'):
    data = pd.read_csv(input_csv, names=header, dtype=data_types).dropna()
    data = data.drop(columns=['time_s'])

    data['speedup_seq_base'] = pd.to_numeric(data['speedup_seq_base'])

    data = data.groupby(["benchmark_name", "method", "input_size",
                         "delta", "num_threads"]).agg(['mean', 'std'])
    data = data.reset_index()
    data.columns = ['benchmark_name', 'method', 'input_size',
                    'delta', 'num_threads',
                    'speedup_mean', 'speedup_std']

    data = data.reindex(columns=sorted(data.columns))

    sdf = data[data['input_size'] == input_size].drop(columns=['input_size'])

    seqs = sdf[sdf['num_threads'] == 1].drop(columns=['num_threads'])

    seqs = seqs.groupby(['benchmark_name'])

    fig = plt.figure(figsize=(8, 5), dpi=80,
                     facecolor='w', edgecolor='k')
    ax = fig.add_subplot(1, 1, 1)

    for benchn, bench_gp in seqs:
        bgp = bench_gp.drop(columns='benchmark_name').groupby(['method'])

        for method, group in bgp:
            method = method.strip()
            if method not in methods:
                continue
            minfo = methods[method]
            group = group.drop(columns=['method'])
            xy = group.to_numpy().transpose()
            x = [(float(x) / input_size) for x in xy[0]]
            y = [float(x) for x in xy[1]]
            z = [float(z) for z in xy[2]]
            label = methods[method][2]
            if plot_error_bars:
                ax.errorbar(x, y, z, linestyle="solid",
                            color=minfo[1], label=label,
                            elinewidth=0.7, capsize=3)
            else:
                ax.plot(x, y, linestyle="solid",
                        color=minfo[1], label=label)

    plt.minorticks_on()
    plt.setp(ax.get_xticklabels(), fontsize=axes_fontsize)
    plt.setp(ax.get_yticklabels(), fontsize=axes_fontsize)
    plt.legend(bbox_to_anchor=(0.3, 0.4, 0.34, 0.4), loc=3,
               ncol=1, mode="expand", borderaxespad=0.,
               prop={'size': legend_fontsize})
    ax.set_ylabel('speedup d&c implementation / iterative',
                  fontsize=axes_fontsize)
    ax.set_xlabel(xlabel, fontsize=axes_fontsize)
    ax.grid(b=True, which="major", color=(0.8, 0.8, 0.8))
    ax.grid(b=True, which="minor", color=(0.9, 0.9, 0.9))
    ax.set_xscale("log")
    ax.margins(x=0.01)
    fig.tight_layout(pad=0.1)
    chartname = ps2_chartname(expname, input_size)
    plt.savefig(chartname)
    if display:
        os.system("xdg-open %s" % chartname)
    return chartname


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=_default_input_csv)
    parser.add_argument('--size', type=int, nargs='?',
                        default=_default_size, help='Size of the input points array.')
    parser.add_argument('--name',
                        default="experiment", help='Experiment name to plot.')
    parser.add_argument('--input', nargs='?',
                        default=_default_input_csv, help='Input csv file containing the experimental data')
    parser.add_argument('--plot-error-bars',
                        help='Plot error bars.', action='store_true')
    parser.add_argument('--open-output', action='store_true',
                        help='Display output chart.')
    parser.add_argument('--plot33', action='store_true',
                        help='Display output chart.')
    parser.add_argument('--xlabel',
                        default='ratio optimal points / total points',
                        help='Output chart x label.')

    args = parser.parse_args()
    if args.plot33:
        methods["seq033"] = ['seq', 'brown',     'B = (0,3,3)']
    plot(args.name, args.input, args.size,
         args.plot_error_bars, display=args.open_output, xlabel=args.xlabel)
