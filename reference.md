# Reference 

## Table of contents 

- [Software installation in Docker](#software-installation-in-docker)
- [Running Rosette* and Rosette](#running-rosette-and-rosette)
- [Creating a Rosette* file](#creating-a-rosette-file)
- [Running Leanette and Lean](#running-leanette-and-lean)
- [Creating a Leanette file](#creating-a-leanette-file)
- [Running the test generator (solver-aided differential testing)](#running-the-test-generator-solver-aided-differential-testing)
- [Running the test oracle (solver-aided differential testing)](#running-the-test-oracle-solver-aided-differential-testing)
- [Creating a manual test file (solver-aided differential testing)](#creating-a-manual-test-file-solver-aided-differential-testing)
- [Running the test reporter (solver-aided differential testing)](#running-the-test-reporter-solver-aided-differential-testing)
- [Running the patcher (solver-aided differential testing)](#running-the-patcher-solver-aided-differential-testing)
- [Running SymPro benchmarks performance comparison](#running-sympro-benchmarks-performance-comparison)

## Software installation in Docker

The Docker image uses Ubuntu 20.04. Feel free to install any additional software that you need.
For instance, to install the text editor `nano`, run:

```sh
$ apt update
$ apt install nano
```

## Running Rosette* and Rosette

Given a Rosette* file `<file.rkt>`, it can be run with the command:

```sh
$ raco cross -q --workspace /workspace/rosette-4 racket <file.rkt>
```


Similarly, given a Rosette file `<file.rkt>`, it can be run with the command:

```sh
$ raco cross -q --workspace /workspace/rosette-3 racket <file.rkt>
```

## Creating a Rosette* file 

The documentation of Rosette* can be viewed at https://docs.racket-lang.org/rosette-guide/. 
[This section](https://docs.racket-lang.org/rosette-guide/ch_essentials.html#%28part._sec~3aasserts%29) in particular explains the essence of Rosette*.

We recommend that you create a Rosette* file in the home directory so that it doesn't pollute the worktree.

## Running Leanette and Lean

Given a Leanette or Lean file `<file.lean>`, it can be run with the command:

```sh
$ lean <file.lean>
```

In particular, always run Lean files within `/workspace/lean`. 
Running it outside the directory will cause errors.

## Creating a Leanette file

You need to create a file `/workspace/lean/src/workspace/load-<filename>.lean` using the following template:

```
import ..sym_factory.sym_factory
import ..generation.main
import ..generation.printer
import ..interp.sym.defs
import ..op.sym

open lang.exp
open op.sym

def input_exp : lang.exp op.lang.datum op.lang.op
  := <prog>

#eval result.to_str $
  (interp.interpS sym_factory.sym_factory <fuel>
    input_exp
    <env>
    initial_state)
```

- `<prog>` should be a Lean expression representing a Leanette AST.
- `<env>` should be a list of Lean expressions representing a Leanette environment (which is a list of Leanette values).
- `<fuel>` should be a fuel number. We recommend the value `100`.

For example:

```
import ..sym_factory.sym_factory
import ..generation.main
import ..generation.printer
import ..interp.sym.defs
import ..op.sym

open lang.exp
open op.sym

def input_exp : lang.exp op.lang.datum op.lang.op
  := (let0 0 (datum (op.lang.datum.int 0))
       (let0 1 (app (op.lang.op.int_2 op.lang.op_int_2.mul) [0, 1])
         (let0 1 (app (op.lang.op.int_2 op.lang.op_int_2.eq) [0, 1])
           (if0 1
                error
                (bool tt)))))

#eval result.to_str $
  (interp.interpS sym_factory.sym_factory 100
    input_exp
    [(val.atom (val_atom.term (term.var (var.mk type.int 0)))), (val.atom (val_atom.term (term.var (var.mk type.int 1))))] 
    initial_state)
```

is the program in Fig 7b. 

The initial environment has two variables: `0` and `1`. For the sake of readability, we will call them `zero` and `n` respectively.
Both are initially bound to symbolic integer constants.

The program roughly translates to Rosette-like syntax as follows:

```
(let ([zero 0])
  (let ([n (* n zero)])
    (let ([n (= zero n)])
      (if n
          (assert #f) 
          #t))))
```

## Running the test generator (solver-aided differential testing)

First, run:

```sh
$ cd /workspace/diff-testing
$ ./reset.sh
```

to make sure the `generation` directory is clean.

Then, the test generator can be invoked with:

```sh
$ raco cross -q --workspace /workspace/rosette-4 racket generation.rkt
```

The test generator accepts the following flags:

```
  --max-bool-vars <v> : Number of max bool variables (default: 5)
  --max-int-vars <v> : Number of max int variables (default: 5)
  --iterations <main> : Number of iterations (default: 500)
  --sub-iterations <sub> : Number of sub-iterations (default: 20)
  --seed <s> : Random seed. `-` means no seed. (default: 42)
  --int-scope <n> : Integer scope (default: 2)
```

which will generate `<sub>` * `<main>` test programs. 

- `--max-bool-vars` refers to the number of symbolic boolean variables that the program can use.
- `--max-int-vars` refers to the number of symbolic integer variables that the program can use.
- `--iterations` refers to the the number of iterations to generate programs of varying sizes.
- `--sub-iterations` refers to the number of iterations to generate programs of similar sizes in each group of varying sizes.
- `--seed` controls the random seed.
- `--int-scope` controls integer constants that could appear. `2` means `-2` to `2`. 
   Note that the program could still compute a large integer by performing arithmetic on these constants.

## Running the test oracle (solver-aided differential testing)

The test oracle can be invoked with:

```sh
$ raco cross -q --workspace /workspace/rosette-4 racket tester.rkt </path/to/file/or/directory> ...
```

If the inputs are generated test programs, the oracle will operate on those test programs. 
If the inputs are directories, the oracle will operate on all test programs in the directories.

The test oracle accepts the following flags:

```
  --fuel <f> : Fuel used for Lean interpretation (default: 100)
  --timeout <t> : Timeout in seconds (default: 80)
  --num-threads <n> : Number of threads (default: 4)
  --out <o> : Output path (default: workspace/log.rktd)
  --verbose : Print Lean and Rosette code
```

`--out` refers to the log file path that the oracle will write to. 
This is useful for preventing log files from overwriting each other.

## Creating a manual test file (solver-aided differential testing)

Feel free to create your own test file by adapting from predefined test files in `/workspace/diff-testing/predefined` 
or generated test files in `/workspace/diff-testing/generation`. 
Similar to writing a Leanette file, you need to indicate the program and the initial environment. 
Unlike a Leanette file, it uses an S-expression syntax, which could be translated to both Rosette* and Leanette easily.

For example, the file `/workspace/diff-testing/predefined/fig-7b.rkt` has the following content

```
(define expr
  '(let0 0 #;0 (datum (op.lang.datum.int 0))
         (let0 1 #;(* 0 s) (app * 0 1)
               (let0 1 #;(= 0 (* 0 s)) (app = 0 1)
                     (if0 1
                          (make-error)
                          #t)))))

(define env '(int int))
```

(Note that `#;` is an S-expression comment.)

The meaning of this program is described in the section [Creating a Leanette file](#creating-a-leanette-file).

## Running the test reporter (solver-aided differential testing)

The test reporter will always read a log file at `/workspace/diff-testing/workspace/log.rktd` to report the result.

## Running the patcher (solver-aided differential testing)

Before running the patcher, make sure that the worktree is clean.
If it is not clean, running `git clean -df` and `git reset --hard` from `/workspace` will make the worktree clean.

The patcher can be invoked with:

```sh
$ raco cross -q --workspace /workspace/rosette-4 racket patcher.rkt </path/topatch-file.patch> </path/to/file/or/directory>
```

The first argument is the path to a patch file. Subsequent arguments are the same as the arguments to the test oracle.

The patcher accepts one flag, `--timeout`, which is the same as `--timeout` in the test oracle.

Since the patcher will modify Leanette, you probably should run `git reset --hard` afterward to discard any changes to Leanette.

## Running SymPro benchmarks performance comparison

`perf.sh` can be invoked with:

```sh
$ ./perf.sh <benchmark> ...
```

Each benchmark can be either a benchmark ID or a negation (`~`) of a benchmark ID (which will exclude the benchmark).
Additionally, `sympro` means all benchmarks.

For example, if you want to run all SymPro benchmarks, execute:

```sh
$ ./perf.sh sympro
```

If you want to run SymPro benchmarks excluding `rtr` and `synthcl`, execute:

```sh
$ ./perf.sh sympro ~rtr ~synthcl
```

If you want to only run `rtr` and `synthcl`, execute:

```sh
$ ./perf.sh rtr synthcl
```

