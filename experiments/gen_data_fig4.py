#!/usr/bin/env python3
import data.dutils as du
import data.plot_pt_exp_seqs as plot_exp
from multiprocessing import Process, Pipe
import os
import subprocess
import sys
import enlighten
import argparse
import math

BAR_FMT = u'{desc}{desc_pad}{percentage:3.0f}%|{bar}| {count:{len_total}.1f}/{total:.1f} ' + \
          u'[{elapsed}<{eta}, {rate:.2f}{unit_pad}{unit}/s]'

COUNTER_FMT = u'{desc}{desc_pad}{count:.1f} {unit}{unit_pad}' + \
              u'[{elapsed}, {rate:.2f}{unit_pad}{unit}/s]{fill}'

_default_description = "Launch experiments for sequential implementations of POP."


def launch_sequential_pop(exp_params, k, conn):
    conn.send(0)
    err = open(exp_params['error_log'], "w")
    tmp_file_name = exp_params['tmp_file_name'](k)
    expcode = exp_params['expcode']

    with open(tmp_file_name, 'w') as _tmp:
        pass

    sizes = exp_params['sizes']

    #print("[ID:%i] Size = %s" % (k, " ".join([str(s) for s in sizes])))

    # Parameters for printing progress
    ecount = 0
    for size in sizes:
        for _ in range(0, exp_params['repeats']):
            for rpow in range(exp_params['pow_min'], exp_params['pow_max'] + 1):
                for ratio_mult in exp_params['ratio_mult']:
                    ratio = ratio_mult * pow(10, -rpow)
                    if int(ratio * size) >= 0:
                        ecount += 1

    pb_incr = float(100.0 / ecount)

    # Proceed with running experiments
    for size in sizes:
        for _ in range(0, exp_params['repeats']):
            for rpow in range(exp_params['pow_min'], exp_params['pow_max'] + 1):
                for ratio_mult in exp_params['ratio_mult']:
                    ratio = ratio_mult * pow(10, -rpow)

                    if int(ratio * size) >= 0:
                        with open(tmp_file_name, 'a') as o:
                            subprocess.run(
                                [exp_params['binary'], str(size), "1", str(ratio), str(expcode)], stdout=o, stderr=err)
                    conn.send(pb_incr)

    conn.send(-1)
    ok = conn.recv()
    if ok:
        conn.close()
    else:
        print("ERROR closing %i." % k)
    err.close()


def progress_printer(exp_params, connections):
    manager = enlighten.get_manager()
    bars = list()
    for pno, _ in enumerate(connections):
        name = "Process %i" % pno
        bars.append(manager.counter(total=100.00, desc=name, unit='%',
                                    bar_format=BAR_FMT, counter_format=COUNTER_FMT))

    stopped = 0
    open_conns = [True] * len(connections)
    while stopped < len(connections):
        for pno, conn in enumerate(connections):
            if not open_conns[pno]:
                continue
            if conn.poll(exp_params['poll_timeout']):
                progress_update = conn.recv()
                if progress_update == -1:
                    bars[pno].update()
                    conn.send(True)
                    open_conns[pno] = False
                    stopped = stopped + 1
                else:
                    if isinstance(progress_update, float):
                        bars[pno].update(incr=progress_update)
    manager.stop()


def copy_to_main_csv(k):
    tmp_file_name = exp_params['tmp_file_name'](k)
    tmp_file = open(tmp_file_name, 'r')
    data = tmp_file.read()
    tmp_file.close()
    fout = open(exp_params['csv_file_name'], "a")
    fout.write(data)
    fout.close()
    os.remove(tmp_file_name)


if __name__ == "__main__":

    exp_params = {
        'binary': './PtExpPop',
        'repeats': 4,
        'pow_max': 5,
        'pow_min': 1,
        'expcode': '11111',
        'num_processes': 1,
        'ratio_mult': [9, 8, 7, 6, 5, 4, 3, 2, 1],
        'tmp_file_name': (lambda k: "./tmp/exp_partition_divide_%i.csv" % k),
        'csv_file_name': "./exp_partition_divide_review.csv",
        'error_log': './data/errors.log',
        'poll_timeout': 0.01,
        'sizes': [2000],
    }

    parser = argparse.ArgumentParser(description=_default_description)
    parser.add_argument('--binary',
                        default=exp_params['binary'], help='The binary executable.')
    parser.add_argument('--sizes', type=int, nargs='+',
                        default=exp_params['sizes'],
                        help='Run experiments for different sizes (default: 2000).')
    parser.add_argument('--numprocs', type=int,
                        default=exp_params['num_processes'],
                        help='Number of parallel processes running experiments (default: 1).')
    parser.add_argument('--output',
                        default=exp_params['csv_file_name'],
                        help='Output csv file containing the experimental data (default : exp_partition_divide.csv).')
    parser.add_argument('--powmin', default=exp_params['pow_min'], type=int,
                        help='Min ratio power of 10 (default : 1).')
    parser.add_argument('--powmax', default=exp_params['pow_max'], type=int,
                        help='Max ratio power of 10 (default : 5).')
    parser.add_argument('--repeats', default=exp_params['repeats'], type=int,
                        help='Number of runs for each experiment (default : 4).')
    parser.add_argument('--expcode', default=exp_params['expcode'],
                        help='Expcode, a binary number (default: 11111)')
    args = parser.parse_args()

    if args.numprocs > 0 and args.numprocs < 32:
        exp_params['num_processes'] = args.numprocs

    #exp_params['csv_file_name'] = "data/exp_pt_seq/%s.csv" % expname

    exp_params['csv_file_name'] = args.output

    if args.powmin >= 0 and args.powmin < 10:
        exp_params['pow_min'] = args.powmin
    if args.powmax >= 0 and args.powmax < 10:
        exp_params['pow_max'] = args.powmax
    if args.repeats > 0:
        exp_params['repeats'] = args.repeats
    if len(args.sizes) >= 1:
        exp_params['sizes'] = args.sizes
    if len(args.expcode) == 5:
        exp_params['expcode'] = args.expcode

    exp_params['binary'] = args.binary
    expname = exp_params['binary'].strip('./').lower()

    exp_params['tmp_file_name'] = (
        lambda k: "./tmp/exp_%s_seq_%i.csv" % (expname, k))

    procs = list()
    pipes = list()
    q = exp_params['num_processes']
    # Launch q processes that are connected to the progress printer via pipes.
    # Each parallel process has their own temporary csv.
    for pno in range(0, q):
        c1, c2 = Pipe()
        _p = Process(target=launch_sequential_pop, args=(exp_params, pno, c2,))
        procs.append(_p)
        pipes.append(c1)
        procs[pno].start()

    printer = Process(target=progress_printer, args=(exp_params, pipes,))
    printer.start()

    for pno in range(0, q):
        procs[pno].join()
    printer.join()
    # Once every process has finished, copy all data to output csv
    for pno in range(0, q):
        copy_to_main_csv(pno)

    chartnames = []
    for size in exp_params['sizes']:
        chartname = plot_exp.plot(
            expname, exp_params['csv_file_name'], size, False)
        chartnames += [chartname]
        #os.system("xdg-open %s" % chartname)
    print(chartnames)
