import csv

import csv
import sqlite3

db = sqlite3.connect(':memory:')

examples = (
    "sum", "len", "max", "min", "mi2", "mps",
    "mts", "mss", "los", "sor", "pop", "pot", "fs1", "bal", "s01", "lbk", "co1")

def clean_csv():
    rdr = csv.reader(open("experiments.csv", 'rb'), delimiter=",")
    wtr = csv.writer(open("experiments_clean.csv", 'wb'), delimiter=",")
    for row in rdr:
        if len(row) == 4:
            wtr.writerow(row)

def fetch_results():
    fieldnames = ['example', 'num_cores', 'size', 'time']
    rdr = csv.reader(open("experiments_clean.csv", 'rb'), delimiter=",")
    per_example_csv = {
        "sum": csv.writer(open("data/sum.csv", 'w'), delimiter = ","),
        "len": csv.writer(open("data/len.csv", 'w'), delimiter = ","),
        "max": csv.writer(open("data/max.csv", 'w'), delimiter = ","),
        "min": csv.writer(open("data/min.csv", 'w'), delimiter = ","),
        "mi2": csv.writer(open("data/mi2.csv", 'w'), delimiter = ","),
        "mps": csv.writer(open("data/mps.csv", 'w'), delimiter = ","),
        "mts": csv.writer(open("data/mts.csv", 'w'), delimiter = ","),
        "mss": csv.writer(open("data/mss.csv", 'w'), delimiter = ","),
        "los": csv.writer(open("data/los.csv", 'w'), delimiter = ","),
        "sor": csv.writer(open("data/sor.csv", 'w'), delimiter = ","),
        "pop": csv.writer(open("data/pop.csv", 'w'), delimiter = ","),
        "pot": csv.writer(open("data/pot.csv", 'w'), delimiter = ","),
        "fs1": csv.writer(open("data/fs1.csv", 'w'), delimiter = ","),
        "bal": csv.writer(open("data/bal.csv", 'w'), delimiter = ","),
        "s01": csv.writer(open("data/s01.csv", 'w'), delimiter = ","),
        "lbk": csv.writer(open("data/lbk.csv", 'w'), delimiter = ","),
        "co1": csv.writer(open("data/co1.csv", 'w'), delimiter = ",")
    }

    for row in rdr:
        per_example_csv[row[0]].writerow(row[1:4])

clean_csv()
fetch_results()
