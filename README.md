# ConSynth

## Requirements
Most of the source files are written in [Racket 6.4](https://racket-lang.org/download/). You can install Rosette using Racket command line tools :
```$ raco pkg install rosette```
Or you can install it from source, [more information here](https://github.com/emina/rosette).

You will also need to install the project package in order to run the different tests :
``` $ cd consynth```
``` $ raco pkg install ```

### OCaml
C code analysis is partially done using the Cil library in Ocaml, so you will need to install Ocaml and some packages.
- Project management : oasis. \\
  ``` opam install oasis ```
- Cil ``` opam install cil ```

To set up the Makefiles, in each directory where you can find a ```_oasis``` file, run :\\
```oasis setup -setup-update dynamic``` \\
And then compile using make.

## Project

### Parsing and analyzing input C code.
The parsing and the analysis of the input code is done with the Cil library in consynth/canalysis. To run the tests, execute the makefile in the consynth/canalysis directory and run ```./Main [filename]```

### Synthesis examples with Rosette.