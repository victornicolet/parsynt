import csv
import numpy
from collections import defaultdict
import csv
import sqlite3

db = sqlite3.connect(':memory:')

examples = (
    "sum", "len", "max", "min", "mi2", "mps",
    "mts", "mss", "los", "sor", "pop", "pot",
    "fs1", "bal", "s01", "lbk", "co1","ham", "abn")

sizes = (2147483648)
num_cores = (-1, 0, 2, 4, 8, 16, 24, 32, 40, 48, 56, 64)

def get_ex_file_dump (exname):
    return "data/" + exname + ".csv"

def clean_csv():
    rdr = csv.reader(open("experiments.csv", 'rb'), delimiter=",")
    wtr = csv.writer(open("experiments_clean.csv", 'wb'), delimiter=",")
    for row in rdr:
        if len(row) == 4:
            wtr.writerow(row)

def fetch_results():
    fieldnames = ['example', 'num_cores', 'size', 'time']
    rdr = csv.reader(open("experiments_clean.csv", 'rb'), delimiter=",")
    per_example_csv = {}
    for ex in examples:
        per_example_csv[ex] = csv.writer (open (get_ex_file_dump (ex)),
                                          delimiter = ",")
        per_example_csv[ex].writerow(("num_cores", "example_size", "time"))

    for row in rdr:
        per_example_csv[row[0]].writerow(row[1:4])



def get_res_example(ex):
    ex_csv = csv.reader (open (get_ex_file_dump (ex), 'r'), delimiter = ",")
    data = defaultdict(dict)
    next(ex_csv)
    for row in ex_csv:
        if len(row) == 3:
            if row[0] in data[row[1]]:
                data[row[1]][row[0]].append(float(row[2]));
            else:
                data[row[1]][row[0]] = [float(row[2])];

    avg = defaultdict(dict)
    stddev = defaultdict(dict)
    for size, sgrp in data.iteritems():
        for num_core, ngrp in sgrp.iteritems():
            av = numpy.mean(ngrp, axis=0)
            stdv = numpy.mean(ngrp, axis=0)
            avg[size][num_core]= av
            stddev[size][num_core]= stdv


def fetch_results():
    fieldnames = ['example', 'num_cores', 'size', 'time']
    rdr = csv.reader(open("experiments_clean.csv", 'rb'), delimiter=",")
    per_example_csv = {}
    for ex in examples:
        per_example_csv[ex] = csv.writer (open (get_ex_file_dump (ex) ,'w'),
                                          delimiter = ",")
        per_example_csv[ex].writerow(("num_cores", "example_size", "time"))

    for row in rdr:
        per_example_csv[row[0]].writerow(row[1:4])

    for ex in examples:
        get_res_example (ex)


clean_csv()
fetch_results()
