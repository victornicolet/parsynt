import csv

INFILE = "explog_compsbk2.csv"
OUTFILE = "speedups_compsbk2.csv"

data = {}

exp_cores = [1, 2, 3, 4, 6, 8, 10, 12, 16, 24, 32, 46, 58, 64]

with open(INFILE, 'rb') as csvfile:
    sreader = csv.reader(csvfile, delimiter=',')
    for row in sreader:
        exname = row[0][5:]
        ncores = int(row[1])
        time = float(row[2])

        if exname in data:
            data[exname][ncores] = time
        else:
            data[exname] = { ncores : time }

with open(OUTFILE, 'w') as csvout:

    csvout.write("Example name," + ",".join([str(x) for x in exp_cores]) + "\n")

    for ex, stats in data.iteritems():
        onec = stats[1]
        st = [onec / stats[k] for k in sorted(stats.iterkeys())]
        csvout.write(ex + "," + ",".join([str(x) for x in st]) + "\n")
