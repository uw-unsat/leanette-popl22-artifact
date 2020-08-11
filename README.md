# "A formal foundation for symbolic evaluation with merging" Artifact

This is the artifact for the POPL 2022 paper "A formal foundation for symbolic evaluation with merging".
A copy of the paper is included in the artifact.

The artifact is packaged as a Docker image. See the [hardware requirements](#hardware-requirements) and [installation](#installation-and-sanity-testing) sections for more details.
The repository is simply the source of the Docker image.

The paper uses Rosette and Rosette* to refer to versions 3 and 4 of the Rosette system, respectively.
The artifact may refer to them as Rosette 3 and Rosette 4.

## Table of contents

- [List of claims](#list-of-claims)
  - [Mechanization and Lean implementation (Leanette)](#mechanization-and-lean-implementation-leanette)
  - [Racket implementation (Rosette*)](#racket-implementation-rosette)
  - [Solver-aided differential testing](#solver-aided-differential-testing)
  - [Comparing the interface of Rosette* and Rosette](#comparing-the-interface-of-rosette-and-rosette)
  - [Comparing the performance of Rosette* and Rosette](#comparing-the-performance-of-rosette-and-rosette)
- [Hardware requirements](#hardware-requirements)
- [Installation and sanity testing](#installation-and-sanity-testing)
- [Evaluation instructions](#evaluation-instructions)
  - [Eval: Mechanization and Lean implementation (Leanette)](#eval-mechanization-and-lean-implementation-leanette)
  - [Eval: Racket implementation (Rosette*)](#eval-racket-implementation-rosette)
  - [Eval: Solver-aided differential testing](#eval-solver-aided-differential-testing)
  - [Eval: Comparing the interface of Rosette* and Rosette](#eval-comparing-the-interface-of-rosette-and-rosette)
  - [Eval: Comparing the performance of Rosette* and Rosette](#eval-comparing-the-performance-of-rosette-and-rosette)
- [Additional artifact description](#additional-artifact-description)

## List of claims

### Mechanization and Lean implementation (Leanette)

We mechanized our symbolic semantics and proved its correctness in Lean.
We also created a reference interpreter named Leanette, which is proven correct.
These are inside the subdirectory `lean`.
The following table links sections in the paper with files under the directory `lean`.

| File                                                                             | Description                            | Note        |
|----------------------------------------------------------------------------------|----------------------------------------|-------------|
| [`lean/src/cs/lang.lean`](lean/src/cs/lang.lean)                                 | Syntax and concrete semantics of `λ_c` | Section 3.1 |
| [`lean/src/cs/detc.lean`](lean/src/cs/detc.lean)                                 | Determinism of `λ_c`                   | Theorem 1   |
| [`lean/src/cs/sym.lean`](lean/src/cs/sym.lean)                                   | Symbolic factory interface             | Section 4.1 |
| [`lean/src/cs/svm.lean`](lean/src/cs/svm.lean)                                   | Evaluation rules for `S_c`             | Section 4.2 |
| [`lean/src/cs/thm.lean`](lean/src/cs/thm.lean)                                   | Properties and correctness of `S_c`    | Theorem 2—8 |
| [`lean/src/interp/sym/defs.lean`](lean/src/interp/sym/defs.lean)                 | Leanette implementation                | Section 6.1 |
| [`lean/src/interp/sym/thm.lean`](lean/src/interp/sym/thm.lean)                   | Correctness of Leanette                | Theorem 9   |
| [`lean/src/sym_factory/sym_factory.lean`](lean/src/sym_factory/sym_factory.lean) | Symbolic factory `F_L`                 | Section 6.1 |
| [`lean/src/sym_factory/red.lean`](lean/src/sym_factory/red.lean)                 | Reducibility and correctness of `F_L`  | Theorem 10  |

### Racket implementation (Rosette*)

We also created a Racket implementation, known as Rosette*, which implements the symbolic semantics with an optimized symbolic factory.
The subdirectory `rosette-4/rosette` ([or this link](https://github.com/sorawee/rosette/tree/9fefa68ad171be497050230f7a8a65f62a99c5d9) if you wish to view it outside the Docker image)
contains an implementation of Rosette*, as described in Section 6.2.

### Solver-aided differential testing

To make sure that Rosette* is implemented correctly, we tested it via solver-aided differential testing.
The subdirectory `diff-testing` contains the differential testing setup that tests Leanette against Rosette*,
as described in Section 6.3 (and also Figure 7, Table 1, and Table 2).

### Comparing the interface of Rosette* and Rosette

We compared the interface of Rosette* and Rosette by porting benchmarks written in Rosette to Rosette*.
Two subdirectories `rosette-benchmarks-3` and `rosette-benchmarks-4` contain the benchmarks described in Section 7.1.1 and 7.1.2.
The directory `interface` contains tools that read these benchmarks to generate Table 3.

### Comparing the performance of Rosette* and Rosette

We tested that the performance of Rosette* matches that of Rosette on the benchmarks mentioned above.
The subdirectory `perf` contains a tool that tests the performance of Rosette* and Rosette for SymPro benchmarks
(which are in `rosette-benchmarks-3` and `rosette-benchmarks-4`), as described in Section 7.2 (and Table 4).
The following table lists SymPro benchmarks.

| Benchmark   | ID            | Entry file                                       |
|-------------|---------------|--------------------------------------------------|
| Bagpipe     | `bagpipe`     | `bagpipe/setups/textbook/run.rkt`                |
| Bonsai      | `bonsai`      | `bonsai/nanoscala.rkt`                           |
| Cosette     | `cosette`     | `cosette/cidr-benchmarks/oracle-12c-bug.rkt`     |
| Ferrite     | `ferrite`     | `ferrite/rename.rkt`                             |
| Fluidics    | `fluidics`    | `fluidics/ex2.rkt`                               |
| GreenThumb  | `greenthumb`  | `greenthumb/GA/output/0/driver-0.rkt`            |
| IFCL        | `ifcl`        | `ifcl/test.rkt`                                  |
| Memsynth    | `memsynth`    | `memsynth/case-studies/synthesis/ppc/ppc0.rkt`   |
| Neutrons    | `neutrons`    | `neutrons/filterWedgeProp.rkt`                   |
| Nonograms   | `nonograms`   | `nonograms/puzzle/src/run-batch-learn-rules.rkt` |
| Quivela     | `quivela`     | `quivela/test-inc-arg.rkt`                       |
| RTR         | `rtr`         | `rtr/benchmarks/all.rkt`                         |
| SynthCL     | `synthcl`     | `synthcl/examples/sobelFilter/test.rkt`          |
| Wallingford | `wallingford` | `wallingford/tests/all-tests.rkt`                |
| WebSynth    | `websynth`    | `websynth/test/all-tests.rkt`                    |

Separately, the subdirectory `jitterbug-benchmarks` contains a tool that tests the performance of Rosette* and Rosette for Jitterbug benchmarks.

## Hardware requirements

To use this artifact, you will need a machine capable of running Docker with at least 8GB of free disk space, and at least 16GB of RAM.
It is known that Docker does **not** work on ARM-based systems such as Apple M1.

For reference, we tested this artifact on a machine running
Linux 5.4.0 and Docker 20.10.8 with an
Intel Core i7-7700K CPU @ 4.20GHz, configured with 16GB of RAM.
The results you obtain may vary from ours depending on your particular machine
setup, including CPU, available RAM, concurrently running processes, etc.

## Installation and sanity testing

The only required installation is Docker. See <https://docs.docker.com/install/>
for details on how to install Docker. If you are using macOS (non-ARM-based),
[Docker For Mac](https://docs.docker.com/docker-for-mac/install/)
is a good solution.

After installing Docker, you can download and run the Docker image by running:

```sh
# Download image (~2GB download)
$ docker pull unsat/leanette-popl22-artifact:latest

# Run Image
$ docker run -it --name leanette-artifact unsat/leanette-popl22-artifact:latest
```

This will drop you into a shell inside the container,
in the `/workspace` directory, the main directory containing
source code and experiments.

We have installed `vim` into the container for convenience to edit and view files;
you can also use Docker to copy files into and out of the container,
see <https://docs.docker.com/engine/reference/commandline/cp/>.

If you leave the container and wish to get back, you will
need to restart it with the command
`docker start -ia leanette-artifact`. If you wish to instead start from a fresh
copy of the image, run `docker rm leanette-artifact` to remove the container and then follow the instructions
for the first run of the container above.

### Sanity test: Mechanization and Lean implementation (Leanette)

To test that Leanette works, run:

``` sh
$ cd /workspace/lean
$ lean src/workspace/load.lean
```

This should output:

```
"(ans (state #t #t) (term_bool #t))"
```

### Sanity test: Racket implementation (Rosette*)

To test that Rosette* works, run:

```sh
$ cd /workspace
$ raco cross -q --workspace /workspace/rosette-4 racket examples/correct-ex-1.rkt
```

This should produce the output `(unsat)`.

Next, run:

```sh
$ raco cross -q --workspace /workspace/rosette-4 racket examples/incorrect-ex-1.rkt
```

This should produce a model, for example:

```
(model
 [y 0])
```

Compared to Rosette, Rosette* adds the statement `assume` to the language.
Therefore, `correct-ex-1.rkt`, which uses the `assume` statement, should fail to run in Rosette.

```sh
$ raco cross -q --workspace /workspace/rosette-3 racket examples/correct-ex-1.rkt
```

should fail with output beginning with `examples/correct-ex-1.rkt:12:4: assume: unbound identifier`.

However, the program `examples/rosette-3.rkt` which does not use the `assume` statement, should succeed when run with Rosette.

``` sh
$ raco cross -q --workspace /workspace/rosette-3 racket examples/rosette-3.rkt
```

This should produce a model, for example:

```
(model
 [y -1])
```

### Sanity test: Solver-aided differential testing

Test the oracle on a predefined program that passes the differential testing (Figure 7b in the paper) by running:

```sh
$ cd /workspace/diff-testing
$ ./reset.sh
$ raco cross -q --workspace /workspace/rosette-4 racket tester.rkt ./predefined/fig-7b.rkt
```

You should see the following output:

```
======= Program ./predefined/fig-7b.rkt =======
Computed in X.XXs
Rosette*:
(halt (state #t #f))

Rosette* evaluation is trivial
Rosette* state size: 2
Computed in X.XXs
Leanette:
(ans (state #t #f) (undef))

Leanette evaluation is non-trivial
Leanette state size: 46
Leanette and Rosette* agree
```

Note: it may appear that Leanette's state is trivial, but that's because the output shown above is also reduced by Rosette's symbolic factory.
The actual state size is 46, which is not trivial.

Next, test the reporter by running:

```sh
$ raco cross -q --workspace /workspace/rosette-4 racket report.rkt
```

You should see the following output:

```
┌─────┬─────┬───┬────────────────────┬───┬───┬────────────────────┬──────┬──────┬───────────────────┬───┬──────────────────┬───┬──────────┐
│Range│Count│Avg│(Leanette state) Sym│Max│Avg│(Rosette* state) Sym│Max   │Avg   │(Leanette time) Max│Avg│(Rosette time) Max│Avg│Validated?│
├─────┼─────┼───┼────────────────────┼───┼───┼────────────────────┼──────┼──────┼───────────────────┼───┼──────────────────┼───┼──────────┤
│9 - 9│1    │9  │1                   │46 │46 │0                   │+nan.0│+nan.0│X.X                │X.X│X.X               │X.X│✓         │
└─────┴─────┴───┴────────────────────┴───┴───┴────────────────────┴──────┴──────┴───────────────────┴───┴──────────────────┴───┴──────────┘
```

Similarly, test the oracle on a predefined program that does **not** pass the differential testing (Figure 7a in the paper) by running:

```sh
$ cd /workspace/diff-testing
$ ./reset.sh
$ raco cross -q --workspace /workspace/rosette-4 racket tester.rkt ./predefined/fig-7a.rkt
```

You should see the following output:

```
======= Program ./predefined/fig-7a.rkt =======
Computed in X.XXs
Rosette*:
(ans (state #t #t) #t)

Rosette* evaluation is trivial
Rosette* state size: 2
Leanette runs out of fuel
Leanette evaluation is trivial
Leanette state size: 0
```

Next, test the reporter by running:

```sh
$ raco cross -q --workspace /workspace/rosette-4 racket report.rkt
```

You should see the following output:

```
program at ./predefined/fig-7a.rkt fails differential testing because Leanette runs out of fuel
```

Note that `report.rkt` is a script to generate Table 1.
Because in sanity test runs there is only one trivial data point, a lot of values do not make sense, so it results in `+nan.0`.

### Sanity test: Comparing the interface of Rosette* and Rosette

Run the following command:

```sh
$ cloc --version
```

It should produce the output `1.86`.

### Sanity test: Comparing the performance of Rosette* and Rosette

There is no sanity test for this step (the previous sanity tests already verify that Rosette* and Rosette can be run).

## Evaluation instructions

In general, the output related to time duration will not exactly match the paper due to
differences in hardware and machine configuration. However, we hope it won't deviate significantly,
and that the data you obtain will maintain relative order with respect to other data points.
For example, if a table in the paper indicates that that Rosette* is faster than Rosette in a particular benchmark,
Rosette* should still be faster than Rosette in your run too, even though the measured times will not exactly match.

### Eval: Mechanization and Lean implementation (Leanette)

Expected time: less than 1 minute

To check all proofs, run the following commands:

```sh
$ cd /workspace/lean
$ ./reset.sh
$ leanproject build
```

The script `reset.sh` resets the `lean` directory (e.g., clears compiled files).

The command `leanproject build` checks proofs in every file and warns for any uses of `sorry` (i.e., unchecked proofs).

There should be exactly one warning, as follows:

```
lean/src/test_sorry.lean:1:0: warning: declaration 'test_sorry' uses sorry
```

This is an intentional `sorry` inserted into the project to ensure that `leanproject build` can detect unchecked proofs.
The file `test_sorry.lean` is not used otherwise. To validate this, you can run:

```sh
$ git rm src/test_sorry.lean
$ git commit -m "remove test_sorry.lean" # we require that the worktree is clean, so commit the change
$ ./reset.sh
$ leanproject build
```

To check proofs in a specific file, run `lean <file.lean>`.
Unless the file is `test_sorry.lean`, there should be no warning or error.

### Eval: Racket implementation (Rosette*)

Expected time: N/A

You can find the the implementation in `/workspace/rosette-4/rosette`
([or this link](https://github.com/sorawee/rosette/tree/9fefa68ad171be497050230f7a8a65f62a99c5d9) if you wish to view it outside the Docker image).

If you wish, you may create your own Rosette* files and run them. See the [reference](reference.md) for more details.

More thorough evaluation of Rosette* is described in the next sections of this guide (solver-aided differential testing and performance evaluation).

### Eval: Solver-aided differential testing

Expected time: less than 4 hours

The results of Figure 7 should already be reproduced as a part of the sanity testing process.
This section details differential testing of randomly generated programs, which consists of multiple steps:

- Compile Leanette so that it can readily run tests
- Generate tests
- Run the oracle on the generated tests
- Check the quality of the tests (coverage) by seeing if the tests can detect mistakes in intentionally incorrect interpreters.

#### Preparing Leanette

Expected time: less than 1 minute

Simply run:

```sh
$ cd /workspace/lean
$ leanproject build
```

If you have already done this as a part of the previous step (and have not run `reset.sh` after that), this step can be skipped.

#### Test generation

Expected time: less than 1 minute

There are two possible choices here. **You do not need to do both**. Only one suffices.

##### Full run

Generate 10,000 test files as described in the paper by running:

```sh
$ cd /workspace/diff-testing
$ ./reset.sh
$ raco cross -q --workspace /workspace/rosette-4 racket generation.rkt
```

The script `reset.sh` resets the `diff-testing` directory (e.g., clear previously generated test files and results).

The script `generation.rkt` generates 10,000 test files in the directory `generation` with seed 42.
Feel free to inspect them if you wish to. If you wish to reproduce Table 1, we recommend that you keep using the default test generation setting,
but otherwise, you can change the seed to other numbers. See the [reference](reference.md) for how to do so.

##### Quick run

If you don't have enough time to run the oracle on all 10,000 test files, you can generate fewer programs by running:

```sh
$ cd /workspace/diff-testing
$ ./reset.sh
$ raco cross -q --workspace /workspace/rosette-4 racket generation.rkt --sub-iterations <sub> --iterations <main>
```

The above command will generate `<sub>` * `<main>` test files.

In the default test generation setting, `<sub>` is 20 and `<main>` is 500. We recommend that you consider lowering `<sub>` first.

For example, the command:

``` sh
$ raco cross -q --workspace /workspace/rosette-4 racket generation.rkt --sub-iterations 1 --iterations 500
```

will generate 500 test files. On our machine with four threads, the oracle can check all 500 programs under 10 minutes.

Note however that any setting that deviates from the default will not reproduce Table 1.
However, the differential testing should still pass (see the [test report](#test-report) section for more details).

#### Test oracle

Expected time: depends on how many tests you generate. For 10,000 tests:

- Expected time with one thread: less than 16 hours
- Expected time with four threads: less than 4 hours

Run the oracle:

```sh
$ cd /workspace/diff-testing
$ raco cross -q --workspace /workspace/rosette-4 racket tester.rkt ./generation
```

This command runs the oracle with 4 threads and 80s timeout and outputs the result to the screen.
It also creates a log file at `/workspace/diff-testing/workspace/log.rktd` that the reporter will read.
Due to hardware difference, you may need to adjust these parameters. 
See the [reference](reference.md) for more details.

(Note that in the paper, we used the timeout of 40s, but inside Docker, we find that 40s is not enough,
so we bump the timeout up to 80s.)

#### Test report

Expected time: less than 1 minute

Report the result by running:

```sh
$ cd /workspace/diff-testing
$ raco cross -q --workspace /workspace/rosette-4 racket report.rkt
```

The output consists of two parts: the programs that do not pass the differential testing and a table similar to Table 1 in the paper.

First, for programs that do not pass the differential testing, there are 5 possible reasons:

- Leanette and Rosette* disagree: this case should never happen, as it indicates that Rosette* and Leanette actually disagree.
  If you found one, please let the authors know!
- Leanette has a fatal error: this case should never happen. It's likely that there is a technical error somewhere.
  If you found one, please let the authors know!
- Leanette runs out of fuel: this case is possible when the generated program contains an unreachable infinite loop,
  but Leanette's symbolic factory is not strong enough to deduce the unreachability.
  The case is accounted for in our framework (see Section 5 and Example 9) and should not be counted as a mistake.
  It would be very rare for this case to happen.
  In our evaluation in the paper, this case does not arise from randomly generated programs on our machine.
- Rosette* timeout: either the program takes a really long time to evaluate or it contains an infinite loop.
  It would be very rare for this case to happen.
  In our evaluation in the paper, this case does not arise from randomly generated programs on our machine.
- Leanette timeout: the program takes a really long time to evaluate.
  It would be very rare for this case to happen.
  In our evaluation in the paper, this case does not arise from randomly generated programs on our machine.

You can re-run the oracle on each program that doesn't pass the differential testing to see more details.

If you encounter the timeout problems with the default test generation setting for the generation process,
it should be the case that all generated programs are terminated.
So you can also re-run that specific program with higher timeout.

Second, for the table, if you use the default test generation setting,
the result should be similar to Table 1 with minor differences in evaluation time.

```
┌─────────┬─────┬───┬────────────────────┬───────┬─────┬────────────────────┬───┬───┬───────────────────┬───┬──────────────────┬───┬──────────┐
│Range    │Count│Avg│(Leanette state) Sym│Max    │Avg  │(Rosette* state) Sym│Max│Avg│(Leanette time) Max│Avg│(Rosette time) Max│Avg│Validated?│
├─────────┼─────┼───┼────────────────────┼───────┼─────┼────────────────────┼───┼───┼───────────────────┼───┼──────────────────┼───┼──────────┤
│1 - 12   │1,006│6  │220                 │635    │41   │88                  │20 │4  │3.0                │2.7│0.3               │0.1│✓         │
├─────────┼─────┼───┼────────────────────┼───────┼─────┼────────────────────┼───┼───┼───────────────────┼───┼──────────────────┼───┼──────────┤
│13 - 24  │1,021│19 │349                 │1,142  │77   │174                 │36 │6  │2.9                │2.6│1.2               │0.1│✓         │
├─────────┼─────┼───┼────────────────────┼───────┼─────┼────────────────────┼───┼───┼───────────────────┼───┼──────────────────┼───┼──────────┤
│25 - 38  │1,042│32 │430                 │2,855  │102  │224                 │34 │6  │2.8                │2.7│0.3               │0.1│✓         │
├─────────┼─────┼───┼────────────────────┼───────┼─────┼────────────────────┼───┼───┼───────────────────┼───┼──────────────────┼───┼──────────┤
│39 - 50  │1,036│44 │433                 │16,979 │242  │187                 │34 │7  │3.0                │2.7│0.4               │0.1│✓         │
├─────────┼─────┼───┼────────────────────┼───────┼─────┼────────────────────┼───┼───┼───────────────────┼───┼──────────────────┼───┼──────────┤
│51 - 65  │1,040│58 │450                 │7,523  │186  │227                 │30 │8  │2.9                │2.7│0.3               │0.1│✓         │
├─────────┼─────┼───┼────────────────────┼───────┼─────┼────────────────────┼───┼───┼───────────────────┼───┼──────────────────┼───┼──────────┤
│66 - 77  │1,040│72 │459                 │30,386 │474  │239                 │45 │8  │3.6                │2.7│0.3               │0.1│✓         │
├─────────┼─────┼───┼────────────────────┼───────┼─────┼────────────────────┼───┼───┼───────────────────┼───┼──────────────────┼───┼──────────┤
│78 - 88  │1,053│83 │454                 │19,835 │426  │231                 │36 │8  │3.3                │2.7│0.5               │0.1│✓         │
├─────────┼─────┼───┼────────────────────┼───────┼─────┼────────────────────┼───┼───┼───────────────────┼───┼──────────────────┼───┼──────────┤
│89 - 102 │1,042│95 │427                 │45,893 │482  │190                 │41 │9  │4.4                │2.7│0.3               │0.2│✓         │
├─────────┼─────┼───┼────────────────────┼───────┼─────┼────────────────────┼───┼───┼───────────────────┼───┼──────────────────┼───┼──────────┤
│103 - 119│1,009│111│425                 │61,439 │686  │218                 │45 │9  │5.2                │2.7│0.4               │0.2│✓         │
├─────────┼─────┼───┼────────────────────┼───────┼─────┼────────────────────┼───┼───┼───────────────────┼───┼──────────────────┼───┼──────────┤
│120 - 158│711  │129│324                 │293,171│2,001│159                 │36 │9  │40.0               │2.7│0.4               │0.2│✓         │
└─────────┴─────┴───┴────────────────────┴───────┴─────┴────────────────────┴───┴───┴───────────────────┴───┴──────────────────┴───┴──────────┘
```

#### Coverage

The following list details our injected mistakes:

| Patch file                                                                                             | Description                                                                                        |
|--------------------------------------------------------------------------------------------------------|----------------------------------------------------------------------------------------------------|
| [`diff-testing/patch/incorrect_and.patch`](diff-testing/patch/incorrect_and.patch)                     | Make `and(b_a, b_b)` = `b_a` where `b_a` and `b_b` are non-literal symbolic booleans               |
| [`diff-testing/patch/incorrect_or.patch`](diff-testing/patch/incorrect_or.patch)                       | Make `or(b, b)` = `tt` where `b` is a non-literal symbolic boolean                                 |
| [`diff-testing/patch/incorrect_lt.patch`](diff-testing/patch/incorrect_lt.patch)                       | Make `op(<, z_a, z_b)` = `z_b < z_a` where either `z_a` or `z_b` is a non-literal symbolic integer |
| [`diff-testing/patch/incorrect_call_op.patch`](diff-testing/patch/incorrect_call_op.patch)             | In `CallOp`, skip `strengthen`                                                                     |
| [`diff-testing/patch/incorrect_call.patch`](diff-testing/patch/incorrect_call.patch)                   | In `Call`, change the guards for evaluation of the body to be `tt`                                 |
| [`diff-testing/patch/incorrect_call_bad.patch`](diff-testing/patch/incorrect_call_bad.patch)           | In `CallBad`, use the input symbolic state without asserting `γ`                                   |
| [`diff-testing/patch/incorrect_let.patch`](diff-testing/patch/incorrect_let.patch)                     | In `Let`, do not bind any variable                                                                 |
| [`diff-testing/patch/incorrect_if_sym.patch`](diff-testing/patch/incorrect_if_sym.patch)               | In `IfSym`, swap `not(truth(v))` and `truth(v)` when calling `merge_R(., .)`                       |
| [`diff-testing/patch/incorrect_if_true_false.patch`](diff-testing/patch/incorrect_if_true_false.patch) | In `IfTrue` and `IfFalse`, swap the conditions                                                     |
| [`diff-testing/patch/incorrect_error.patch`](diff-testing/patch/incorrect_error.patch)                 | In `Err`, do `Abort`                                                                               |
| [`diff-testing/patch/incorrect_abort.patch`](diff-testing/patch/incorrect_abort.patch)                 | In `Abort`, do `Err`                                                                               |

There are two possible choices here. **You do not need to do both**. Only one suffices.
We recommend the default test generation setting as it's going to be much quicker and matches the paper.

##### Default test generation setting

Expected time: less than 5 minute

We have already identified test programs in `generation` that cause faultily patched Leanette (BadLeanette) to produce incorrect results.

First, run:

```sh
$ cd /workspace/lean
$ leanproject build

$ cd /workspace/diff-testing
$ ./reset.sh
$ raco cross -q --workspace /workspace/rosette-4 racket generation.rkt
$ git status
```

The commands will generate 10,000 test files and prepare Leanette.

`git status` should report that the worktree is clean (no "Untracked files" or "Changes").
If it is not clean, running `git clean -df` and `git reset --hard` from `/workspace` will make the worktree clean.

Second, run:

```sh
$ ./test-coverage.sh
```

The script `test-coverage.sh` will patch Leanette with each patch file and run the oracle on known test programs that cause them to fail differential testing.
The expected output is that the oracle reports failure on all of them.

```
program at ./generation/prog23160718406451015591104819237807520888040421765198.rkt fails differential testing because Leanette and Rosette* disagree
program at ./generation/prog100208336541399653250221187751391297369.rkt fails differential testing because Leanette and Rosette* disagree
program at ./generation/prog478473500332049125701102687487886134892618785332689813519393109671586439862663588789828131845030156.rkt fails differential testing because Leanette and Rosette* disagree
program at ./generation/prog16803.rkt fails differential testing because Leanette and Rosette* disagree
program at ./generation/prog666831569393266787587089860792333636466692132130.rkt fails differential testing because Leanette and Rosette* disagree
program at ./generation/prog19436053114232394.rkt fails differential testing because Leanette and Rosette* disagree
program at ./generation/prog15.rkt fails differential testing because Leanette and Rosette* disagree
program at ./generation/prog1331343393596762924043919245445877806201864368967369509032193564215325013490794460521988648842748377343143771160948246706431109369.rkt fails differential testing because Leanette and Rosette* disagree
program at ./generation/prog271706286423030047271490064405043091576078507211894322485583089278608494173230103175221675458186681751625690187786390.rkt fails differential testing because Leanette and Rosette* disagree
program at ./generation/prog735983.rkt fails differential testing because Leanette and Rosette* disagree
program at ./generation/prog100026410668776740492900673318090171927233255361720922983271273849413253676502727166331182369672360102050306966877856993674940497.rkt fails differential testing because Leanette and Rosette* disagree
```

Note that Lean will also emit a lot of errors and warnings.
This is expected, since the proofs are no longer valid after patching.
However, Lean should still be able to run Leanette with no problem.

##### Manual setting

Expected time: depends on various factors, but generally, it could take extremely long time, as you will run the test oracle on all generated tests for 11 times.

If you don't want to use the default test generation setting, you can instead run:

```sh
$ git status # should report the directory is clean
$ raco cross -q --workspace /workspace/rosette-4 racket patcher.rkt ./patch/<file.patch> ./generation
$ git reset --hard
```

which will apply a given patch to Leanette, and run the oracle on programs in `generation`.
You can interrupt (ctrl-c) the process when you notice that the oracle reports that Rosette* and (Bad)Leanette disagree.

If you know Lean, you can also modify Leanette to create your own BadLeanette and run the oracle yourself on `generation`.
Note that the modification must make the interpreter incorrect (it is possible to modify it without compromising its correctness, so you need to be careful).

The expected result is that for every patch, one of the generated tests in `generation` will catch the discrepancy between Rosette* and BadLeanette, _provided that_ there are enough generated tests.

### Eval: Comparing the interface of Rosette* and Rosette

Expected time: less than 20 minutes

To generate Table 3, run:

```sh
$ cd /workspace/interface
$ ./reset.sh
$ ./run.sh # (~17 minutes)
```

The script `reset.sh` removes any previously generated outputs.

The script `run.sh` counts the number of lines by going through module dependencies,
performs line diffing, and reports the result. It will print out the intermediate results
as it runs, ending with a table that matches Table 3 from the paper:

```
┌───────────────────────────────────────────┬───────────┬────────────┬────────┬────┬─────────┐
│Benchmark                                  │Rosette LoC│Rosette* LoC│LoC diff│    │Solver   │
├───────────────────────────────────────────┼───────────┼────────────┼────────┼────┼─────────┤
│Bagpipe~\cite{weitz:bagpipe}               │2,643      │2,643       │+2      │-2  │Z3       │
├───────────────────────────────────────────┼───────────┼────────────┼────────┼────┼─────────┤
│Bonsai~\cite{chandra:bonsai}               │437        │437         │+1      │-1  │Boolector│
├───────────────────────────────────────────┼───────────┼────────────┼────────┼────┼─────────┤
│Cosette~\cite{chu:cosette}                 │774        │774         │+0      │-0  │Z3       │
├───────────────────────────────────────────┼───────────┼────────────┼────────┼────┼─────────┤
│Ferrite~\cite{ferrite}                     │348        │348         │+2      │-2  │Z3       │
├───────────────────────────────────────────┼───────────┼────────────┼────────┼────┼─────────┤
│Fluidics~\cite{willsey:puddle}             │98         │98          │+0      │-0  │Z3       │
├───────────────────────────────────────────┼───────────┼────────────┼────────┼────┼─────────┤
│GreenThumb~\cite{phothilimthana:greenthumb}│3,554      │3,556       │+13     │-11 │Boolector│
├───────────────────────────────────────────┼───────────┼────────────┼────────┼────┼─────────┤
│IFCL~\cite{rosette:pldi}                   │483        │483         │+13     │-13 │Boolector│
├───────────────────────────────────────────┼───────────┼────────────┼────────┼────┼─────────┤
│MemSynth~\cite{memsynth}                   │13,303     │13,307      │+8      │-4  │Z3       │
├───────────────────────────────────────────┼───────────┼────────────┼────────┼────┼─────────┤
│Neutrons~\cite{pernsteiner:neutrons}       │37,174     │37,174      │+2      │-2  │Z3       │
├───────────────────────────────────────────┼───────────┼────────────┼────────┼────┼─────────┤
│Nonograms~\cite{butler:nonograms}          │3,368      │3,374       │+11     │-5  │Z3       │
├───────────────────────────────────────────┼───────────┼────────────┼────────┼────┼─────────┤
│Quivela~\cite{aws:quivela}                 │1,010      │1,009       │+10     │-11 │Z3       │
├───────────────────────────────────────────┼───────────┼────────────┼────────┼────┼─────────┤
│RTR~\cite{kazerounian:rtr}                 │1,649      │1,640       │+12     │-21 │CVC4     │
├───────────────────────────────────────────┼───────────┼────────────┼────────┼────┼─────────┤
│SynthCL~\cite{rosette:pldi}                │2,257      │2,256       │+42     │-43 │Boolector│
├───────────────────────────────────────────┼───────────┼────────────┼────────┼────┼─────────┤
│Wallingford~\cite{borning:wallingford}     │2,532      │2,533       │+12     │-11 │Z3       │
├───────────────────────────────────────────┼───────────┼────────────┼────────┼────┼─────────┤
│WebSynth~\cite{rosette:pldi}               │1,181      │1,189       │+14     │-6  │Z3       │
├───────────────────────────────────────────┼───────────┼────────────┼────────┼────┼─────────┤
│Jitterbug~\cite{jitterbug}                 │29,280     │28,935      │+478    │-823│Boolector│
└───────────────────────────────────────────┴───────────┴────────────┴────────┴────┴─────────┘
```

### Eval: Comparing the performance of Rosette* and Rosette


#### SymPro benchmarks performance comparison: Tables 4a and 4c

Expected time: less than 1 hour

Run the following command:

```
$ cd /workspace/perf
$ ./reset.sh
$ ./perf.sh sympro
```

The output should roughly match Table 4a and the SymPro row of Table 4c in the paper, with minor differences in columns about time duration.

```
┌───────────┬───────────────┬────┬───────┬─────┬────────────────┬────┬───────┬─────┐
│Benchmark  │(Rosette) Total│Eval│Solving│Terms│(Rosette*) Total│Eval│Solving│Terms│
├───────────┼───────────────┼────┼───────┼─────┼────────────────┼────┼───────┼─────┤
│Bagpipe    │25             │24  │2      │47   │26              │24  │2      │48   │
├───────────┼───────────────┼────┼───────┼─────┼────────────────┼────┼───────┼─────┤
│Bonsai     │23             │21  │3      │664  │46              │42  │3      │1,222│
├───────────┼───────────────┼────┼───────┼─────┼────────────────┼────┼───────┼─────┤
│Cosette    │13             │9   │5      │131  │14              │10  │5      │154  │
├───────────┼───────────────┼────┼───────┼─────┼────────────────┼────┼───────┼─────┤
│Ferrite    │23             │13  │10     │34   │32              │13  │19     │40   │
├───────────┼───────────────┼────┼───────┼─────┼────────────────┼────┼───────┼─────┤
│Fluidics   │20             │7   │13     │284  │25              │8   │18     │308  │
├───────────┼───────────────┼────┼───────┼─────┼────────────────┼────┼───────┼─────┤
│GreenThumb │56             │8   │48     │239  │6               │2   │4      │74   │
├───────────┼───────────────┼────┼───────┼─────┼────────────────┼────┼───────┼─────┤
│IFCL       │154            │11  │143    │383  │119             │12  │107    │438  │
├───────────┼───────────────┼────┼───────┼─────┼────────────────┼────┼───────┼─────┤
│MemSynth   │24             │22  │2      │61   │27              │25  │2      │163  │
├───────────┼───────────────┼────┼───────┼─────┼────────────────┼────┼───────┼─────┤
│Neutrons   │44             │43  │<\,1   │444  │13              │12  │<\,1   │172  │
├───────────┼───────────────┼────┼───────┼─────┼────────────────┼────┼───────┼─────┤
│Nonograms  │17             │3   │14     │51   │23              │4   │19     │73   │
├───────────┼───────────────┼────┼───────┼─────┼────────────────┼────┼───────┼─────┤
│Quivela    │35             │33  │2      │1,113│39              │34  │4      │1,340│
├───────────┼───────────────┼────┼───────┼─────┼────────────────┼────┼───────┼─────┤
│RTR        │353            │332 │21     │741  │135             │101 │34     │1,106│
├───────────┼───────────────┼────┼───────┼─────┼────────────────┼────┼───────┼─────┤
│SynthCL    │252            │16  │236    │726  │247             │18  │229    │732  │
├───────────┼───────────────┼────┼───────┼─────┼────────────────┼────┼───────┼─────┤
│Wallingford│12             │<\,1│11     │4    │12              │<\,1│11     │5    │
├───────────┼───────────────┼────┼───────┼─────┼────────────────┼────┼───────┼─────┤
│WebSynth   │17             │12  │5      │1,012│24              │19  │5      │778  │
└───────────┴───────────────┴────┴───────┴─────┴────────────────┴────┴───────┴─────┘



┌────────────┬─────┬────┬───────────┬─────┬────┬──────────────┬─────┬────┬────────────┬─────┬────┐
│(Total) Best│Worst│Avg │(Eval) Best│Worst│Avg │(Solving) Best│Worst│Avg │(Terms) Best│Worst│Avg │
├────────────┼─────┼────┼───────────┼─────┼────┼──────────────┼─────┼────┼────────────┼─────┼────┤
│0.11        │1.95 │0.85│0.26       │2.06 │0.90│0.09          │1.90 │1.00│0.31        │2.65 │1.06│
└────────────┴─────┴────┴───────────┴─────┴────┴──────────────┴─────┴────┴────────────┴─────┴────┘
```

Also see the [reference](reference.md) for how to run a specific benchmark or fewer benchmarks.

#### Jitterbug performance comparison: Tables 4b and 4c

Expected time: less than 24 hours

This step describes how to generate the results described in section 7.2
that compare the performance of the Rosette version of Jitterbug to that of the Rosette* port.

First, switch to the directory containing the Jitterbug benchmarks.

```sh
$ cd /workspace/jitterbug-benchmarks
```

Generating the performance results will take several hours, as the benchmarks are run single-threaded for consistency across runs.
The script will output the raw performance data to the console and to the files `jitterbug-rosette3-data.csv` and `jitterbug-rosette4-data.csv` in this directory.
You may choose to skip this step and instead use the pre-computed copies of the data to see the
formatted data without waiting for benchmarks to complete.
To run the benchmarks and generate fresh versions of the data, run the following:

```sh
$ ./run-jitterbug-benchmarks.sh # ~19 hours
```

Note that running the benchmarks will overwrite the pre-computed copies of the data. You can revert to the pre-computed
versions with `git checkout '*.csv'`.
After the command completes (or if you are using the pre-computed copies of the data),
run the following command to format the data as it appears in Table 4b and the Jitterbug row of table 4c in the paper.

```sh
$ ./show-performance-table.sh # <1 second
```

If using the pre-computed data, this will produce the output below.
If you ran the benchmarks to generate the data yourself, the results
may vary depending on your particular machine (e.g., CPU, amount of available RAM, etc.)

```
Table 4b:
         |          Total (s.)      ||      Evaluation (s.)     ||       Solving (s.)       ||       Terms (*10^3)      ||
         +  mean  + median +   max  ++  mean  + median +   max  ++  mean  + median +   max  ++  mean  + median +   max  ++
Rosette  |     50 |     22 |  9,963 ||      2 |      1 |     69 ||     48 |     20 |  9,894 ||    119 |     15 |  1,678 ||
Rosette* |     38 |     20 |  4,100 ||      1 |      1 |     73 ||     36 |     19 |  4,027 ||    120 |     23 |  1,837 ||

Performance results for the 668 ported and original Jitterbug benchmarks.

Table 4c (Jitterbug results only)
          |           Total        ||       Evaluation       ||         Solving        ||          Terms         ||
          + best + worst + average ++ best + worst + average ++ best + worst + average ++ best + worst + average ++
Jitterbug | 0.23 |  6.03 |    0.91 || 0.33 |  2.18 |    0.87 || 0.22 |  6.48 |    0.91 || 0.79 |  8.12 |    1.09 ||

Performance ratios between the ported and original code for SymPro and Jitterbug benchmarks.
```

## Additional artifact description

See the [reference](reference.md) for additional artifact description.
