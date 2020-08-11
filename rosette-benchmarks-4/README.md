# Rosette benchmarks

This repository holds a collection of Rosette benchmarks extracted from
real-world Rosette projects.

We intend for this repository to remain private,
because although every benchmark here has been open sourced,
many have been stripped down and modified to run without external dependencies,
and run on only a single interesting input.

## Running benchmarks

The [`run.rkt`](run.rkt) program is a command-line runner for the
benchmarks in this repository.
To run benchmarks, pass their names as arguments to that program;
for example:

    racket run.rkt quivela bagpipe

To run all benchmarks, pass "all":

    racket run.rkt all

To run only the fast benchmarks (everything except GreenThumb and RTR):

    racket run.rkt fast

Benchmarks or benchmark groups can also be prefixed with "~" to remove them from the set;
for example, to run everything except GreenThumb and RTR:

    racket run.rkt all ~greenthumb ~rtr

To see all available benchmarks and groups:

    racket run.rkt -h


The benchmark runner accepts three additional options:

* `-c` to produce CSV output instead of pretty output
* `-v` to not discard the standard output of each benchmark
* `-n <n>` to run each benchmark `<n>` times, and report the average time with a 95% confidence interval

## Output

For each benchmark, the runner produces output of the form:

    === bagpipe ===
    cpu time: 14876 real time: 15618 gc time: 1074

The measured times do not include initial Racket expansion and compilation.