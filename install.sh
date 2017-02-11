#!/bin/bash

# Pretty-printing helper
msg_fail () {
    echo "FAILED : $1";
}
msg_success () {
    echo "OK : $1"
}
contact () {
    echo "Please report error to victor.nicolet@polytechnique.edu";
    exit
}
sep () {
    echo ""
    echo "----------------------------------------------------------------"
}


echo "Installing Parsynth."
#Check for Racket installation
sep
echo "Checking Racket installation ..."
sep

RACKET_VERSION=$(racket -v | sed -n 's/^.*Racket v\([0-9]*.[0-9]*\).*$/\1/p')
if [ -z $RACKET_VERSION ]
then
    msg_fail "Racket not installed !"
    sep
    echo "Installing Racket using ppa:plt/racket."
    sudo add-apt-repository ppa:plt/racket
    sudo apt-get update
    sudo apt-get install racket
fi
sep
RACKET_VERSION=$(racket -v | sed -n 's/^.*Racket v\([0-9]*.[0-9]*\).*$/\1/p')
if [[ $(bc <<< "$RACKET_VERSION > 6.0") ]]
then
    msg_success "Racket $RACKET_VERSION is installed."
else
    msg_fail "Racket $RACKET_VERSION is installed, but we need at least 6.0."
    echo "Please install a more recent version of Racket."
    exit 1;
fi


echo "Checking installation of Racket components : rosette, c-utils ..."
declare -a REQUIRED_PACKAGES=("rosette" "c-utils")

# Function to query the source of a package. If empty, it means the package
# is not installed in raco.
raco_install_src () {
    eval "raco pkg show $1 | sed -n 's/^\s*$1\s*\([a-ZA-Z\-\s]+[^/][a-zA-Z/_]+\)*/\1/p'"
}

for REQ_PACKAGE in "${REQUIRED_PACKAGES[@]}"
do
    INSTALLATION_SOURCE=$(raco_install_src $REQ_PACKAGE)
    #IF the installation source is empty the package is not installed
    if [[ -z $INSTALLATION_SOURCE ]]
    then
        echo $REQ_PACKAGE "is not installed !"
        echo "Do you want to try to install it automatically using raco ?"
        select yn in "Yes" "No"; do
            case $yn in
                Yes )
                    raco pkg install $REQ_PACKAGE;
                    if [[ -z $(raco_install_src $REQ_PACKAGE) ]]
                    then
                        echo "Failed to install $REQ_PACKAGE automatically."
                        msg_fail "Please install $REQ_PACKAGE manually."
                        exit
                    else
                        break
                    fi;;
                No )
                    echo "Please install $REQ_PACKAGE manually."
                    exit;;
            esac
        done
    else
        msg_success "$REQ_PACKAGE is installed. Source: $INSTALLATION_SOURCE"
    fi
done

# Install the collection in raco
PKG_CONSYNTH='parsynth_racket'
CONSYNTH_INSTL_SRC=$(raco_install_src $PKG_CONSYNTH)
if [[ -z $CONSYNTH_INSTL_SRC ]]
then
    echo "Installing local package consynth ..."
    cd parsynth_racket;
    # Errors printed come from the fact that the generator uses racket
    # skeletons for the sketches. Probably should think about a better
    # solution ...
    raco pkg install &> /dev/null
    cd ..;
    #Check if the package has been successfully installed
    if [[ -z $(raco_install_src $PKG_CONSYNTH) ]]
    then
        msg_fail "Couldn't install package consynth."
        contact
    else
        msg_success "Package $PKG_CONSYNTH successfully installed!"
    fi
else
    msg_success "Package $PKG_CONSYNTH already present."
fi

msg_success "All Racket components present."


# Ocaml componenets
sep
echo "Checking Ocaml components."
sep
# Ocaml version (and if Ocaml is present)
OCAML_VERSION=$(ocaml -vnum)
if [ -z $OCAML_VERSION ]
then
    msg_fail "Ocaml not installed !"
    sudo apt-get install ocaml
    # Check ocaml installation
    if [ -z $(ocaml -vnum)]
    then
	msg_fail "couldn't install Ocaml, please install it manually and run the script again."
	exit 0
    else
	msg_success "Ocaml succesfully installed."
    fi
else
    msg_success "Ocaml $OCAML_VERSION is installed."
fi

# Check if OPAM is installed
OPAM_VERSION=$(opam --version)
if [[ -z $OPAM_VERSION ]]
then
    msg_fail "Opam not installed ! Trying to install opam..."
    sudo apt-get install opam
    eval $(opam config env)
    opam init
    opam install depext
    if [ $? -eq 0 ]; then
	echo "Opam installed, you should restart your computer and re-run the script."
	exit 0;
    fi
else
    msg_success "opam $OPAM_VERSION is installed."
fi

# Install oasis
oasis version
if [ $? -eq 0 ]; then
    OASIS_VERSION=$(oasis version)
    msg_success "Oasis $OASIS_VERSION is already installed!"
else
    echo "Installing Oasis and m4"
    sudo apt-get install m4
    sudo apt-get install oasis
    opam install oasis
    oasis version
    if [ $? -eq 0 ]; then
	OASIS_VERSION=$(oasis version)
	echo "Oasis version $OASIS_VERSION installed."
    else
	msg_fail "Failed to install Oasis. Please install it manually."
	exit 1;
    fi
fi

#Install menhir for parser/lexer compilation."
MENHIR_VERSION=$(menhir --version)
if [ $? -eq 0 ]; then
    MENHIR_VERSION=$(menhir --version)
    msg_success "$MENHIR_VERSION is already installed!"
else
    echo "Installing menhir"
    sudo apt-get install menhir
    opam install menhir
    menhir --version
    if [ $? -eq 0 ]; then
	MENHIR_VERSION=$(menhir --version)
	echo "$MENHIR_VERSION installed."
    else
	msg_fail "Failed to install Menhir. Please install it manually."
	exit 1;
    fi
fi


# Automatic package installation with OPAM
opam_install () {
    if [[ -z $OPAM_VERSION ]]
    then
	msg_fail "Opam is not installed. Please install it manually."
	exit 1;
    else
	opam install $1;
	PKG_VERSION=$(opam show $1 | sed -n "s/^\s*version:\s\([0-9]\)*/\1/p")
	if [[ -z $PACKAGE_VERSION ]]
	then
	    msg_success "$1 $PACKAGE_VERSION has been successfully installed."
	else
	    msg_fail "Failed to install package $1. Please install it manually!"
	    exit 1;
	fi
    fi
}
# Check for Ocaml packages
# We rely on ocamlfind to find OCaml packages but on OPAM for installation
declare -a OCAML_PACKAGES=("extlib" "getopt")

for OCAML_REQ_PACKAGE in "${OCAML_PACKAGES[@]}"
do
    PKG_SRC=$(ocamlfind query $OCAML_REQ_PACKAGE)
    if [[ -z $PKG_SRC ]]
    then
       	msg_fail "Couldn't find $OCAML_REQ_PACKAGE"
	opam_install $OCAML_REQ_PACKAGE
    else
	msg_success "Found OCaml package $OCAML_REQ_PACKAGE in $PKG_SRC (ocamlfind)"

    fi
done

sep
echo "Installing modified version of Cil."
sep

# Retrieve and install our modified version
if [[ -d "alt-cil" ]]; then
    echo "Modified Cil implementation already downloaded."
else
    echo "Cloning Git repository for modified version of Cil ..."
    eval "git clone https://github.com/victornicolet/alt-cil.git"
fi

cd alt-cil
echo "Creating local cil package and installing it with opam .."
echo "If you already went through this step, and you are sure that the cil package installed is the one we provide, then just type 'n' when asked for confirmation."
opam pin add cil . -n
opam install cil --verbose


cd ..

# sep
# echo "Installing z3 and z3 bindings."
# sep
# if [[ -d "z3-master" ]]; then
#     echo "z3 already downloaded."
# else
#     echo "Cloning Z3 source repository."
#     eval "git clone https://github.com/Z3Prover/z3.git"
#     cd z3
#     python scripts/mk_make.py --ml
#     cd build
#     make
#     sudo make install
#     cd ../..
# fi

# sep

sep
msg_success "Installed all requirements."
sep

sep
echo "Creating Makefiles for Ocaml sources ..."
sep

cd ocamllibs
oasis setup -setup-update dynamic
#cd ..
msg_success "Makefiles created, trying make in ocamllib"
#cd ./consynth
make $1

if [ $? -eq 0 ]; then
    msg_success "Successfully compiled sources! Let us finish with a small test..."
else
    msg_fail "Try reloading .profile or restarting the computer"
    echo "If it fails again, contact victor.nicolet@polytechnique.edu"
fi
cd ..
#Add links to binaries in base dir
ln -sf ocamllibs/Parsy.native Parsynth
ln -sf ocamllibs/templates/
ln -sf ocamllibs/conf
ln -sf ocamllibs/tbb_examples/
ln -sf ocamllibs/dafny_examples/
ln -sf ocamllibs/conf.csv
ln -sf ocamllibs/src/conf/verification.params

sep
echo "Testing with simple example Sum."
sep
eval "./Parsynth c_examples/solved/sum.c"
