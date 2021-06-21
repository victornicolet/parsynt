import matplotlib.pyplot as plt
import csv

def add_or_append(_dict, _key, _elt):
    if _key in _dict:
        _dict[_key] += [_elt]
    else:
        _dict[_key] = [_elt]


def constr_dict(_list, _keygen):
    _dict = {}
    for x in _list:
        y, z = _keygen(x)
        add_or_append(_dict, y, z)
    return _dict

exp_types = {
    "dnc": {
        "fields": ["name", "algo", "size", "r", "d", "num_threads", "time"]
    },
    "cau": {
        "fields": ["name", "algo", "num_threads", "time"]
    }
}

exp_files = {
    "dnc": [
        # "exp_par_circ_scatter.csv",
        "exp_ins.csv"],
    "cau": ["exp_lis_block_10_10.csv"]
}

alg_style = {
    "naive": "-",
    "pardiv": ":",
    "pdvomp": "--"
}

axes_fontsize = 10
legend_fontsize = 10

def plot_dnc(datafile):
    with open(datafile, 'r') as csvfile:
        data = constr_dict(csv.reader(csvfile, delimiter=","), lambda x: (x[0], x[1:]))

    for name, measures in data.items():
        for_size = constr_dict(measures, lambda l: ((int(l[1]), int(l[2])), [l[0]] + l[3:]))

        # For each size and radius plot results
        for (size, r), m2 in for_size.items():
            # group by distribution
            by_d = constr_dict(m2,
                               lambda l: (int(l[1]),
                                          [str(l[0]).strip(" "), int(l[2]), float(l[3])]))

            chartname = "experiment_%s_size_%i_radius_%i.pdf" % (name, size, r)
            fig = plt.figure(figsize=(14, 10), dpi=80, facecolor='w', edgecolor='k')
            ax = fig.add_subplot(1, 1, 1)

            for d, d_group in by_d.items():
                seq_time = 0.0
                div_seq_time = 0.0
                c1, c2 = 0, 0
                for g in d_group:
                    if g[0] == "seq" and g[1] == 1:
                        seq_time += g[2]
                        c1 += 1
                    if g[0] == "seqdiv" and g[1] == 1:
                        div_seq_time += g[2]
                        c2 += 1

                seq_time = seq_time / c1
                if c2 > 0:
                    div_seq_time = div_seq_time / c2
                    print("%s - %s - %s - %3i = %3.4f" % (name, size, r, d, seq_time / div_seq_time))

                par_alg = {}
                for g in d_group:
                    if g[1] > 1:
                        add_or_append(par_alg, g[0], [g[1], seq_time/g[2]])

                for alg, thread_speedups in par_alg.items():
                    _label = "%s for d = %i" % (alg, d)
                    threads, speedups = zip(*thread_speedups)
                    ax.plot(threads, speedups, label=_label, linestyle=alg_style[alg])
            plt.minorticks_on()
            plt.setp(ax.get_xticklabels(), fontsize=axes_fontsize)
            plt.setp(ax.get_yticklabels(), fontsize=axes_fontsize)
            plt.legend(bbox_to_anchor=(0.01, 0.51, 0.45, 1.102), loc=3,
                       ncol=2, mode="expand", borderaxespad=0.,
                       prop={'size': legend_fontsize})
            ax.set_ylabel('speedup parallel / sequential', fontsize=axes_fontsize)
            ax.set_xlabel('number of threads', fontsize=axes_fontsize)
            ax.grid(b=True, which="major", color=(0.8, 0.8, 0.8))
            ax.grid(b=True, which="minor", color=(0.9, 0.9, 0.9))
            fig.tight_layout()
            plt.savefig(chartname)
            plt.show()



def allplot():
    for dncf in exp_files["dnc"]:
        plot_dnc(dncf)


if __name__ == "__main__":
    allplot()
