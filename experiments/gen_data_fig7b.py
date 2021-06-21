#!/usr/bin/env python3
import os
import subprocess
import argparse

experiments = [
    "Cozp",
    "Cozst",
    "Cott",
    "Mdo",
    "Msz",
    "Mbo",
    "Lis",
    "Lmo",
    "Mbozst",
    "Mlbo",
    "Mlez",
    "Mlozos"
]

experiment_size = 1705032704
output_file = "./data/fig7b_reviewer_data.csv"
num_max_cores = 16
num_repeats = 10


def executable_name(experiment_name):
    return "./PdExp" + experiment_name


def do_experiment(experiment_name):
    command = [executable_name(experiment_name),
               str(experiment_size),
               str(num_max_cores)]
    #print(" ".join(command))
    with open(output_file, 'a') as outchan:
        subprocess.run(command,
                       stdout=outchan)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Generate data to plot Figure 7b.")
    parser.add_argument('--expsize', type=int,
                        default=experiment_size, help='Size of the input points array.')
    parser.add_argument('--max-cores', type=int,
                        default=num_max_cores, help='Maximum number of threads for the experiment.')
    parser.add_argument('--repeats', type=int,
                        default=num_max_cores, help='How many times to repeat the experiment.')
    parser.add_argument('--output',
                        default=output_file, help='Output csv file to write the data.')

    args = parser.parse_args()

    experiment_size = max(0, int(args.expsize))
    num_max_cores = max(0, int(args.max_cores))
    num_repeats = max(0, int(args.repeats))
    output_file = args.output

    for i in range(num_repeats):
        for experiment in experiments:
            do_experiment(experiment)
