OCAML_LIBS=ocamllibs
RACKET_LIBS=parsynth_racket
PROJECT_DIR=$(shell pwd)

.PHONY: links clean libs


config:
	@echo "Creating Makefiles for Ocaml sources ..."
	rm ./ocamllibs/src/conf/project_dir.ml
	echo "let base = \"$(PROJECT_DIR)\"" >> ./ocamllibs/src/conf/project_dir.ml
	cd $(OCAML_LIBS) && oasis setup -setup-update dynamic
	@echo "Makefiles created in <./$(OCAML_LIBS)> ."

links:
	@echo "Create links for compiled files directories at project root."
	cp -r $(OCAML_LIBS)/test/experiments c_examples
	ln -sf $(OCAML_LIBS)/Parsy.native Parsynth
	ln -sf $(OCAML_LIBS)/templates/
	ln -sf $(OCAML_LIBS)/conf
	ln -sf $(OCAML_LIBS)/tbb_examples/
	ln -sf $(OCAML_LIBS)/dafny_examples/
	ln -sf $(OCAML_LIBS)/conf.csv
	ln -sf $(OCAML_LIBS)/src/conf/verification.params
# We don't care about the error here
	mkdir $(OCAML_LIBS)/dump/  &> /dev/null

clean:
	cd $(OCAML_LIBS) && make clean

ocamllibs: config
	cd $(OCAML_LIBS) && make


libs:
	cd $(RACKET_LIBS) && raco pkg install &> /dev/null;
	cd $(OCAML_LIBS) && make

test:
	eval "./Parsynth c_examples/experiments/sum.c"

all: links libs	test

fresh: clean all
