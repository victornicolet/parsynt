# Installation

Run ```./setup.sh``` in the base folder. You will need an active internet connection because the script will try to install missing packages and components.

We tested the tool on Ubuntu 16.04, if you don't have Ubuntu, please use a virtual machine running Ubuntu on it.
You can also install the required packages manually (look at the script and requirements below) if you wish to use a different distribution.

However, you should stil run the script at the end to setup the tool!

### REMARK : we use Ocaml's OPAM package manager, so you should have the environment variables correctly set if you have already installed it. Otherwise, you will be asked during the installation of OPAM is you want it to write into your ```.profile```. We assume the environment has access to OPAM's binaries, so please agree.

## Using the tool

When ```setup.sh``` succeeds, you have a link to an executable in the base folder. Try the tool on a file ```example.c``` :

```./Parsynth examples/c/<example_name.c>```

The tool will search for all the innermost for loops and try to find a divide-and-conquer parallelization for them. If it succeeds, it will produce a TBB implementation in ```examples/tbb/<name of the function where the loop appears>.cpp``` and a proof to be checked by Dafny in ```examples/dafny/<name of the function where the loop appears>.dfy```.

To check the proofs, the user might want to install the Dafny Proof checker.

# Requirements

All the requirements are checked in the script, and installed if they are not satisfied. This is in case you want to install everything manually, or you encounter problems.

## Racket
We use Rosette as a backend solver for program synthesis, so you will need [Racket 6.4](https://racket-lang.org/download/). You can install Rosette using Racket command line tools :
```$ raco pkg install rosette```
Or you can install it from source, [more information here](https://github.com/emina/rosette).

You will also need to install the project package in order to run the different tests :

``` $ cd consynth```

``` $ raco pkg install ```


## OCaml
Most of the functionalities are written in OCaml : input C code parsing, code transformations and sketch generation. You will need some libraries to compile the tool.

### We use a modified Cil
We use a custom version of [Cil](https://github.com/cil-project/cil) that marks the temporary variables it introduces. You can download it [here](https://github.com/victornicolet/alt-cil) and follow the installation instructions. **Don't use opam to install cil!** You should also remove or set a specific environment for this project if you are already using Cil.

### Other packages
The installation script uses ocamlfind to look for packages and tries to install them with [opam](https://opam.ocaml.org/). Also, please make sure ```opam``` is correctly configured (try to find the packages you installed through ```opam``` using ```ocamlfind```).
If you don't wish to use opam, please install all the packages manually, and make sure ```ocamlfind``` can find them.

- Project management : oasis.

  ``` opam install oasis ```

- [Menhir](http://gallium.inria.fr/~fpottier/menhir/) for parsing and lexing :

``` opam install menhir ```

- Getopt ```opam install getopt``` and Extlib ```opam install extlib```


To set up the Makefiles, in each directory where you can find a ```_oasis``` file, run :

```oasis setup -setup-update dynamic```

And then compile using make in ```ocamllibs```.


**If every component is installed, the script ```setup.sh``` should terminate without any error.**

## Compiling
We only tested the tool on Ubuntu 16.04 (including a fresh installation of Ubuntu on a virtual machine). However, if every component is installed, you should be able to compile the project.

### Compile the Ocaml exectuable
```cd ocamllibs```

```oasis setup -setup-update dynamic```

```make```

The compilation and execution of the Ocaml executable relies on some project structure that is setup at the end of the ```setup.sh``` script.

### Install the Racket library
```cd src/synthools```

```raco pkg install```

# Source code

## Solving the sketch using Rosette

The sketch of the join is written in Racket and we use Rosette to solve it. The grammar for the completions of the holes of the sketch is defined in the library in ```parsynth_racket```.

## The tool is written in Ocaml

The Ocaml source is in ```ocamllibs/src``` organized into different libraries. If you want to look at the source, see ```Canalyst.ml``` first, as it describes the transformations of the code to generate a sketch (translation to a functional form, creating the holes and the sketch structure).
The generation of auxiliary material (proof and TBB implementation) is in ```codegen/```.
