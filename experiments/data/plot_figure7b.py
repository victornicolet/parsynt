#!/usr/bin/env python3
import matplotlib.pyplot as plt
import csv
import math
from statistics import mean
import pandas as pd
import numpy as np
import argparse

inputDataFile = "./data/exp_prefix_divide.csv"
input_sizes = [1705032704]


def chartname(size):
    print("./data/exp_prefix_divide_(n=%i)_(avg_plen=100).pdf\n" % size)
    return "./data/exp_prefix_divide_(n=%i)_(avg_plen=100).pdf" % size


legend_fontsize = 15
axes_fontsize = 15
examples = {
    "cozp":   ['red',         '-', 'Count 1(0+)'],
    "cozst":  ['green',       '-', 'Count 1(0*)2'],
    "cott":   ['purple',      '-', 'Count (1)*(2)*3'],
    "mdo":    ['orange',      '-', 'Max dist. between 1'],
    "msz":    ['cyan',        '-', 'Max sum between 0'],
    "lis":    ['blue',        '-', 'LIS'],
    "lmo":    ['black',       '-', 'Largest peak'],
    "mbo":    ['pink',        '-', 'Longest 1*'],
    "mbozst": ['brown',       '-', 'Longest 1(0*)2'],
    "mlozos": ['indigo',      '-', 'Longest odd (01)*'],
    "mlez":   ['gray',        '-', 'Longest even 0*'],
    # "mlbo":   ['deepskyblue', '-', 'Max dist. btw 1'],
}

methods = {
    "seq": 'seq',
    "seq0": 'seq',
    "seq1": 'seq',
    "lifted": 'lifted',
    "par1": 'splitting',
    "par0": 'lifted',
    "prefix": 'splitting'
}


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


def plot():
    data = pd.read_csv(inputDataFile,
                       names=header, dtype=data_types).dropna()

    data['speedup_seq_base'] = pd.to_numeric(data['speedup_seq_base'])

    data = data.groupby(["benchmark_name", "method", "input_size",
                         "delta", "num_threads"]).mean()

    data = data.reset_index()

    for size in input_sizes:

        data = data[data['input_size'] == size].drop(
            columns=['input_size', 'delta', 'time_s'])

        x = data[data["num_threads"] < 2].index
        data.drop(x, inplace=True)

        data = data.groupby(['benchmark_name', 'method'])

        fig = plt.figure(figsize=(8, 8), dpi=80,
                         facecolor='w', edgecolor='k')
        ax = fig.add_subplot(1, 1, 1)

        labels = []

        for name, group in data:
            benchmark_name = name[0].strip()
            if benchmark_name in examples.keys():
                color = examples[benchmark_name][0]
                method = methods[name[1].strip()]
                gd = group.drop(columns=['benchmark_name', 'method'])
                ar = gd.to_numpy().transpose()
                x = [int(i) for i in ar[0]]
                y = [float(i) for i in ar[1]]
                benchmark_fullname = examples[benchmark_name][2]
                # label = "%s-%s" % (benchmark_fullname, method)
                label = benchmark_fullname

                if method == 'splitting' or method == 'lifted':
                    if method == 'lifted':
                        linestyle = 'dashed'
                    else:
                        linestyle = None

                    if label not in labels:
                        labels.append(label)
                    ax.plot(
                        x, y, linestyle=linestyle, color=color, label=label)

        plt.minorticks_on()
        plt.setp(ax.get_xticklabels(), fontsize=axes_fontsize)
        plt.setp(ax.get_yticklabels(), fontsize=axes_fontsize)
        #  Set the legend to show only one of the two implementations
        seen = []
        lines = ax.get_lines()
        lines.reverse()
        for i, p in enumerate(lines):
            if p.get_label() in seen:    # check for Name already exists
                idx = labels.index(p.get_label())       # find ist index
                p.set_label('_' + p.get_label())
            else:
                seen.append(p.get_label())

        ax.legend(bbox_to_anchor=(0.01, 0.51, 0.41, 1.102), loc=3,
                  ncol=1, mode="expand", borderaxespad=0.,
                  prop={'size': legend_fontsize})
        ax.set_ylabel('speedup parallel / sequential', fontsize=axes_fontsize)
        ax.set_xlabel('number of threads', fontsize=axes_fontsize)
        ax.grid(b=True, which="major", color=(0.8, 0.8, 0.8))
        ax.grid(b=True, which="minor", color=(0.9, 0.9, 0.9))
        fig.tight_layout()
        plt.savefig(chartname(size))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Generate plot of Figure 7b.")

    parser.add_argument('--input', nargs='?',
                        default=inputDataFile, help='Input csv file.')

    parser.add_argument('--insize', nargs='?',
                        default=input_sizes[0], help='Plot for given size')

    args = parser.parse_args()
    inputDataFile = args.input
    input_sizes = [int(args.insize)]
    plot()
