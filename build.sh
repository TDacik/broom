#!/bin/bash

# Copyright (C) Broom team
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.

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
if test "/" != "${GCC_HOST:0:1}"; then
    if echo "$GCC_HOST" | grep / >/dev/null; then
        # assume a relative path to GCC_HOST
        GCC_HOST="$(realpath "$GCC_HOST")"
    else
        # assume an executable in $PATH
        GCC_HOST="$(command -v "$GCC_HOST")"
    fi
fi
# check GCC_HOST
test -x "$GCC_HOST" || die "GCC_HOST is not an executable file: $GCC_HOST"

# try to run GCC_HOST
"$GCC_HOST" --version || die "unable to run gcc: $GCC_HOST --version"

CHANGE=false
if [ `uname` = Darwin ] && [ -z "$CXX" ]; then
	# no CXX compiler on macos, try substitue gcc for g++
	base_gcc="${GCC_HOST##*/}"
	gxx="${GCC_HOST%/*}/${base_gcc/gcc/g++}"
	if [ "$GCC_HOST" != "$gxx" ] && [ -x "$gxx" ]; then
		export CC="$GCC_HOST"
		export CXX="$gxx"
		CHANGE=true
	fi
fi

# check code-listener source code
[ "$(ls -A code-listener)" ] \
    || die "Missing code-listener source code"

cd code-listener

status_update "Nuking working directory"
$MAKE distclean \
    || die "'$MAKE distclean' has failed"

status_update "Trying to build JSON dumper"
$MAKE -C json

if $CHANGE; then
	export CC=""
	export CXX=""
fi

status_update "Checking whether JSON dumper works"
$MAKE -C json check \
    || die "JSON dumper does not work"

status_update "Copying ATD"
$MAKE -C json atd
mkdir -p ../src/CL
cp json_build/*.ml* ../src/CL

cd ..
