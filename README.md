# Installation

Run ```./setup.sh``` in the base folder. You will need an active internet connection because the script will try to install missing packages and components.

REMARK : we use Ocaml's OPAM package manager, so you should have the environment variables correctly set if you have already installed it. Otherwise, you will be asked during the installation of OPAM is you want it to write into your ```.profile```. We assume the environment has access to OPAM's binaries, so please agree.

## Using the tool

When ```setup.sh``` succeeds, you have a link to an executable in the base folder. Try the tool on a file ```example.c``` :

```./Parsynth example.c```

The tool will search for all the innermost for loops and try to find a divide-and-conquer parallelization for them. If it succeeds, it will produce a TBB implementation in ```tbb_examples/<name of the function where the loop appears>.cpp``` and a proof to be checked by Dafny in ```dafny_examples/<name of the function where the loop appears>.dfy```.

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
We use a custom version of Cil that marks the temporary variables it introduces. You can download it [here](https://github.com/victornicolet/alt-cil) and follow the installation instructions. *Don't use opam to install cil!* You should also remove or set a specific environment for this project if you are already using Cil.

The installation script uses ocamlfind to look for packages and tries to install them with [opam](https://opam.ocaml.org/). If you don't wish to use opam, please install all the packages manually, and make sure ```ocamlfind``` can find them.

- Project management : oasis.

  ``` opam install oasis ```

- Parser & lexers :

``` opam install menhir ```

- Getopt ```opam install getopt``` and Extlib ```opam install extlib```


To set up the Makefiles, in each directory where you can find a ```_oasis``` file, run :

```oasis setup -setup-update dynamic```

And then compile using make in ```ocamllibs```.
