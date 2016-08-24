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
    msg_fail "Racket not installed ! Please install Racket."
    exit 0
else
    if [[ $(bc <<< "$RACKET_VERSION > 6.0") ]]
    then
        msg_success "Racket $RACKET_VERSION is installed."
    else
        msg_fail "Racket $RACKET_VERSION is installed, we need at least 6.0."
        echo "Please install a more recent version of Racket."
        exit 0
    fi
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
PKG_CONSYNTH='consynth'
CONSYNTH_INSTL_SRC=$(raco_install_src $PKG_CONSYNTH)
if [[ -z $CONSYNTH_INSTL_SRC ]]
then
    echo "Installing local package consynth ..."
    cd consynth;
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

msg_success "All Racket componenents present."
sep
echo "Checking Ocaml components."
sep
# Ocaml version (and if Ocaml is present)
OCAML_VERSION=$(ocaml -vnum)
if [ -z $OCAML_VERSION ]
then
    msg_fail "Ocaml not installed ! Please install Racket."
    exit 0
else
    msg_success "Ocaml $OCAML_VERSION is installed."
fi
