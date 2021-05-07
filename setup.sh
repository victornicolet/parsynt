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
    echo -e "\033[46m Please report error to victor.nicolet@polytechnique.edu\033[0m";
    exit 0
}
sep () {
    echo ""
    echo -e "\033[44m $1 \033[0m"
}


# 1 - Check for Racket installation

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
        msg_fail "Couldn't install package consynth."
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
    fi
else
    msg_success "opam $OPAM_VERSION is installed."
fi

eval $(opam config env)

# Install oasis
oasis version
if [ $? -eq 0 ]; then
    OASIS_VERSION=$(oasis version)
    msg_success "Oasis $OASIS_VERSION is already installed!"
else
    echo "Installing Oasis"
    sudo apt-get install m4
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
declare -a OCAML_PACKAGES=("extlib" "getopt" "core")

for OCAML_REQ_PACKAGE in "${OCAML_PACKAGES[@]}"
do
    PKG_SRC=$(ocamlfind query $OCAML_REQ_PACKAGE)
    if [[ -z $PKG_SRC ]]
    then
       	msg_fail "Couldn't find $OCAML_REQ_PACKAGE (ocamlfind)."
	opam_install $OCAML_REQ_PACKAGE
    else
	msg_success "Found OCaml package $OCAML_REQ_PACKAGE in $PKG_SRC (ocamlfind)"

    fi
done

sep "Installing modified version of Cil."

CIL_SOURCE_DIR="src"

# Retrieve and install our modified version
if [[ -d "$CIL_SOURCE_DIR/alt-cil" ]]; then
    echo "Modified Cil implementation already downloaded."
else
    echo "Cloning Git repository for modified version of Cil ..."
    cd $CIL_SOURCE_DIR
    eval "git clone https://github.com/victornicolet/alt-cil.git"
    cd ..
fi

CIL_PINNED=$(opam show cil | sed -n -e 's/^.*pinned: //p')

if [[ -z $CIL_PINNED ]]
then
    cd $CIL_SOURCE_DIR/alt-cil
    echo "Creating local cil package and installing it with opam .."
    opam pin add cil . -n
    opam install cil
    cd ../..
else
    msg_success "Cil version pinned to local repository."
fi

CIL_INSTALLED_VERSION=$(opam show cil | sed -n -e 's/^.*installed-version: //p')
CIL_DEV_REPO=$(opam show cil | sed -n -e 's/^.*dev-repo: //p')


if [[ -z $CIL_INSTALLED_VERSION ]]
then
    opam install cil --verbose
else
    if [[ "$CIL_DEV_REPO" == "https://github.com/victornicolet/alt-cil.git" ]];
    then
	msg_success "dev-repo of cil is $CIL_DEV_REPO."
	msg_success "Custom Cil version $CIL_INSTALLED_VERSION installed, good."
	echo "---> To uninstall Cil run \$opam remove cil"
    else
	msg_fail "Cil is installed, but we require alt-cil."
	msg_fail "Please uninstall Cil and run this script again."

	exit
    fi
fi


sep "Installed all requirements."

# Configuration for absolute paths in Ocaml source
rm $PWD/src/conf/project_dir.ml
touch $PWD/src/conf/project_dir.ml
echo "let base = \"$PWD\"" >> $PWD/src/conf/project_dir.ml
echo "let src = \"$PWD/src\"" >> $PWD/src/conf/project_dir.ml
echo "let templates = \"$PWD/src/templates/\"" >> $PWD/src/conf/project_dir.ml


sep "Creating Makefiles for Ocaml sources ..."
oasis setup -setup-update dynamic
msg_success "Makefiles created, trying make."
make


if [ $? -eq 0 ]; then
    msg_success "Successfully compiled sources! Let us finish with a small test..."
else
    msg_fail "Try reloading .profile or restarting the computer"
    echo "If it fails again, contact victorn@cs.toronto.edu."
    exit
fi

sep "Testing with some simple examples..."
cd test
./check_solved.sh
cd ..
