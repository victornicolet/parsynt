#!/bin/bash

# This shell script installs all the requirements needed to compile the
# executable Parsynth on a system using the aptitude package manager.

# Pretty-printing helper

msg_fail () {
    echo -e "\033[31m FAILED : $1\033[0m";
}
msg_success () {
    echo -e "\033[32m OK : $1\033[0m"
}
contact () {
    echo -e "\033[46m Please report error to victorn@cs.toronto.edu\033[0m";
    exit 0
}
sep () {
    echo ""
    echo -e "\033[44m $1 \033[0m"
}

sep "Installing z3 and python3"

sudo apt install z3 python3

# Check for Racket installation

sep "Checking Racket installation ..."


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

RACKET_VERSION=$(racket -v | sed -n 's/^.*Racket v\([0-9]*.[0-9]*\).*$/\1/p')

if [[ $(bc <<< "$RACKET_VERSION > 6.8") ]]
then
    msg_success "Racket $RACKET_VERSION is installed."
else
    msg_fail "Racket $RACKET_VERSION is installed, but we need at least 6.9."
    echo "Please install a more recent version of Racket."
    exit 1;
fi


echo "Checking installation of Racket components : rosette, c-utils ..."
declare -a REQUIRED_PACKAGES=("rosette")

# Function to query the source of a package. If empty, it means the package
# is not installed in raco.
raco_install_src () {
    eval "raco pkg show $1 | grep $1"
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
PKG_NAME='synthools'
PKG_SRC='src/synthools'
PKG_INSTL_SRC=$(raco_install_src $PKG_NAME)
if [[ -z $PKG_INSTL_SRC ]]
then
    echo "Installing local package synthools."
    cd $PKG_SRC;
    # Errors printed come from the fact that the generator uses racket
    # skeletons for the sketches. Probably should think about a better
    # solution ...
    raco pkg install &> /dev/null
    cd ..;
    #Check if the package has been successfully installed
    if [[ -z $(raco_install_src $PKG_NAME) ]]
    then
        msg_fail "Couldn't install package synthools."
        contact
    else
        msg_success "Package $PKG_NAME successfully installed!"
    fi
else
    msg_success "Package $PKG_NAME already present."
fi

msg_success "All Racket components present."



# 2 - Ocaml componenets
sep "Checking Ocaml components."

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
    opam config setup -a
    if [ $? -eq 0 ]; then
	msg_success "Opam installed"
	msg_success "If the script fails, check Opam is configured : opam config setup -a"
    msg_success "and check that opam's binaries are in the PATH."
    fi
else
    msg_success "opam $OPAM_VERSION is installed."
fi

eval $(opam config env)

sep "Installing packages via opam ..."
opam update
opam install core
opam install . --deps-only


sep "Installed all requirements."

# Configuration for absolute paths in Ocaml source
rm $PWD/src/utils/project_dir.ml
touch $PWD/src/utils/project_dir.ml
echo "let base = \"$PWD\"" >> $PWD/src/utils/project_dir.ml
echo "let src = \"$PWD/src\"" >> $PWD/src/utils/project_dir.ml
echo "let templates = \"$PWD/src/templates/\"" >> $PWD/src/utils/project_dir.ml

make


if [ $? -eq 0 ]; then
    msg_success "Successfully compiled sources! Let us finish with a small test..."
else
    msg_fail "Try reloading .profile or restarting the computer"
    echo "If it fails again, contact victorn@cs.toronto.edu."
    exit
fi

sep "Testing with some simple examples (should take a few minutes)..."
./scripts/table7a.py
cat table7a.txt
