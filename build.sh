#!/bin/bash
export SELF="$0"

# only for gcc, without dependencies

die() {
    printf "%s: %s\n" "$SELF" "$*" >&2
    exit 1
}

status_update() {
    printf "\n%s...\n\n" "$*"
    tty >/dev/null && printf "\033]0;%s\a" "$*"
}

# number of processor units
NCPU="$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)"
MAKE="make -j${NCPU} -s"

export GCC_HOST="${GCC_HOST:-/usr/bin/gcc}"

# check GCC_HOST
test -x "$GCC_HOST" || die "GCC_HOST is not an executable file: $GCC_HOST"

# check code-listener source code
[ "$(ls -A code-listener)" ] \
    || die "Missing code-listener source code"

cd code-listener

status_update "Nuking working directory"
$MAKE distclean \
    || die "'$MAKE distclean' has failed"

status_update "Trying to build JSON dumper"
$MAKE -C json

status_update "Checking whether JSON dumper works"
$MAKE -C json check \
    || die "JSON dumper does not work"

status_update "Copying ATD"
$MAKE -C json atd
mkdir -p ../src/CL
cp json_build/*.ml* ../src/CL

cd ..
