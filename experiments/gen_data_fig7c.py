#!/usr/bin/env python3
import os
import subprocess
import sys
import data.plot_figure7c as plotScript
import argparse

average_prefix_lengths = [1, 10, int(1e2), int(1e3), int(1e4), int(1e5),
                          int(1e6), int(1e7), int(1e8), int(1e9)]
size = int(10e9)
max_threads = 16
default_distr = 1
num_repeats = 4
output_file = "./data/lis.csv"


def launchExp(average_prefix_length):
    with open(output_file, 'a') as out_channel:
        process_cmd = ["./PdExpLis", str(size), str(max_threads),
                       str(default_distr),
                       str(average_prefix_length)]
        #print(" ".join(process_cmd))
        subprocess.run(process_cmd, stdout=out_channel)
        out_channel.close()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Generate data to plot Figure 7b.")
    parser.add_argument('--expsize', type=int,
                        default=size, help='Size of the input points array.')
    parser.add_argument('--max-cores', type=int,
                        default=max_threads, help='Maximum number of threads for the experiment.')
    parser.add_argument('--repeats', type=int,
                        default=num_repeats, help='How many times to repeat the experiment.')
    parser.add_argument('--output',
                        default=output_file, help='Output csv file to write the data.')

    args = parser.parse_args()

    size = max(0, args.expsize)
    max_threads = max(0, args.max_cores)
    num_repeats = max(0, args.repeats)
    output_file = args.output

    for i in range(num_repeats):
        for pl in average_prefix_lengths:
            if pl < size:
                launchExp(pl)
