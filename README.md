# Installation

Running `./setup.sh` on a linux distribution with the apt package manager should take care 
of all the requirements. This has been tested on Ubuntu 20.04 (and WSL).


# Requirements

All the requirements are checked in the script, and installed if they are not satisfied.
 This is in case you want to install everything manually, or you encounter problems.

## Z3

The tool uses [Z3](https://github.com/Z3Prover/z3) as backend solver, and finds 
the executable using the command-line tool `which`. As long as Z3 can be found on your path, 
any installation method will work.


## Racket
We use Rosette as a backend solver for program synthesis, so you will need
 [Racket 6.4](https://racket-lang.org/download/). You can install Rosette using the Racket 
 command line tools :
```$ raco pkg install rosette```

Or you can install it from source, [more information here](https://github.com/emina/rosette).

You will also need to install the project package:

``` $ cd src/synthools```
``` $ raco pkg install ```

## OCaml
Most of the functionalities are written in OCaml : input C code parsing, code transformations 
and sketch generation. You will need some libraries to compile the tool.
You can get the Opam package manager to install everything by typing:
`opam install . --deps-only`


## Compiling
We only tested the tool on Ubuntu 20.04 (including a fresh installation of Ubuntu on a virtual machine). 
However, if every component is installed, you should be able to compile the project by executing the Makefile, which calls `dune build`.

# Evaluation 
A more detailed guide on evaluating the tool can be found in `scripts/README_EVALUATION.md`. 
Note that the scripts in the folder should be executed from the root folder.
For example, typing `scripts/table7a.py` should generate `table7a.txt` in the root folder 
within a few minutes.
