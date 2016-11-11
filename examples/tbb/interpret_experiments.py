import csv

import csv
import sqlite3

db = sqlite3.connect(':memory:')

def init_db(cur):
    cur.execute('''CREATE TABLE experiment (
    Example TEXT,
    Size INTEGER,
    Num_cores INTEGER,
    Time REAL)''')

def populate_db(cur, csv_fp):
    rdr = csv.reader(csv_fp)
    cur.executemany('''
        INSERT INTO foo (Example, Size, Num_cores, Time)
        VALUES (?,?,?,?)''', rdr)

cur = db.cursor()
init_db(cur)
populate_db(cur, open('experiments.csv'))
db.commit()
