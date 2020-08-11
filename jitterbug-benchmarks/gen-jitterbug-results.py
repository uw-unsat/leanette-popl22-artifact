#!/usr/bin/env python3

# Generate verification performance table

import argparse
import pandas
import os
import jinja2
import sys
import scipy.stats

parser = argparse.ArgumentParser()
parser.add_argument("--debug", action="store_true")
parser.add_argument("--template", type=str, required=True)
args = parser.parse_args()
debug = args.debug

ARCHS = ["rv32", "rv64", "arm32", "arm64", "x86_32", "x86_64"]
AXES = ["realtime", "cputime", "solvertime", "terms"]

ARCHMAP = {
    "x86_64": "x86-64",
    "x86_32": "x86-32",
    "arm64": "Arm64",
    "arm32": "Arm32",
    "rv64": "RV64",
    "rv32": "RV32",
}

THISDIR = os.path.dirname(os.path.abspath(__file__))


def fmt_1(val):
    return f"{round(val):,}".rjust(6)


def fmt_1k(val):
    t = round(val / 1000.0)
    return f"{t:,}".rjust(6)


def fmt_ms_as_h_m(milliseconds):
    seconds = milliseconds / 1000.0
    minutes = seconds / 60
    hours, minutes = divmod(minutes, 60)
    return f"{round(hours)}h{round(minutes)}m"


def load_data(filename):
    path = os.path.join(THISDIR, filename)
    df = pandas.read_csv(path, sep="\\s*,\\s*", engine="python")
    df["solvertime"] = df["realtime"] - df["cputime"]
    return df


def process_perf(data):
    result = {}
    result["all"] = {
        axis: {
            "mean": data[axis].mean(),
            "median": data[axis].median(),
            "min": data[axis].min(),
            "max": data[axis].max(),
            "total": data[axis].sum(),
            "count": len(data[axis]),
        }
        for axis in AXES
    }

    return result


def compare_perf(old_data, new_data):
    old_data = old_data.set_index(["arch", "instr"])
    new_data = new_data.set_index(["arch", "instr"])
    speedups = new_data / old_data
    return {
        axis: {
            "max": speedups.max()[axis],
            "min": speedups.min()[axis],
            "avg": scipy.stats.gmean(speedups[axis]),
        }
        for axis in AXES
    }


rosette3_data = load_data("jitterbug-rosette3-data.csv")
rosette4_data = load_data("jitterbug-rosette4-data.csv")

oldrosette = process_perf(rosette3_data)
newrosette = process_perf(rosette4_data)
comparison = compare_perf(rosette3_data, rosette4_data)

assert oldrosette["all"]["realtime"]["count"] == newrosette["all"]["realtime"]["count"]

comparison["speedup"] = round(
    oldrosette["all"]["realtime"]["total"] / newrosette["all"]["realtime"]["total"], 2
)

if debug:
    print(f"Old Rosette:\n{oldrosette}")
    print(f"New Rosette:\n{newrosette}")
    print(f"Comparisons:\n{comparison}")

templateLoader = jinja2.FileSystemLoader(searchpath=THISDIR)
templateEnv = jinja2.Environment(
    loader=templateLoader, variable_start_string="@@", variable_end_string="@@"
)
templateEnv.globals.update(fmt_1=fmt_1)
templateEnv.globals.update(fmt_1k=fmt_1k)
template = templateEnv.get_template(args.template)
out = template.render(
    oldrosette=oldrosette, newrosette=newrosette, comparison=comparison
)
print(out)
