#!/bin/bash

# only for gcc, without dependencies

status_update() {
    printf "\n%s...\n\n" "$*"
    tty >/dev/null && printf "\033]0;%s\a" "$*"
}

# number of processor units
NCPU="$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)"
MAKE="make -j${NCPU} -s"

export GCC_HOST="${GCC_HOST:-/usr/bin/gcc}"

cd code-listener

status_update "Trying to build JSON dumper"
$MAKE -C json

status_update "Checking whether JSON dumper works"
$MAKE -C json check \
     || true
#    || die "JSON dumper does not work"

status_update "Copying ATD"
$MAKE -C json atd
mkdir -p ../src/CL
cp json_build/*.ml* ../src/CL

cd ..
