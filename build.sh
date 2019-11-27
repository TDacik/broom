#!/bin/bash

# only for gcc, without dependencies

status_update() {
    printf "\n%s...\n\n" "$*"
    tty >/dev/null && printf "\033]0;%s\a" "$*"
}

# number of processor units
NCPU="$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)"

export GCC_HOST="${GCC_HOST:-/usr/bin/gcc}"

cd code-listener

status_update "Trying to build JSON dumper"
make -C json

status_update "Checking whether JSON dumper works"
make -C json check CTEST="ctest -j${NCPU}" \
     || true
#    || die "JSON dumper does not work"

status_update "Copying ATD"
make -C json atd
mkdir -p ../src/CL
cp json_build/*.ml* ../src/CL

cd ..
