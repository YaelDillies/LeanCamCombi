#!/usr/bin/env bash
# Usage: mk_all.sh [subdirectory]
#
# Examples:
#   ./scripts/mk_all.sh
#   ./scripts/mk_all.sh data/real
#   ./scripts/mk_all.sh ../archive
#
# Makes a mathlib/src/$directory/all.lean importing all files inside $directory.
# If $directory is omitted, creates `mathlib/src/all.lean`.

cd "$( dirname "${BASH_SOURCE[0]}" )"/../LeanCamCombi
if [[ $# = 1 ]]; then
  dir="${1%/}"  # remove trailing slash if present
else
  dir="."
fi

# remove an initial `./`
# replace an initial `../test/` with just `.` (similarly for `roadmap`/`archive`/...)
# replace all `/` with `».«`
# replace the `.lean` suffix with `»`
# prepend `import «`
find "$dir" -name \*.lean -not -name LeanCamCombi.lean \
  | sed 's,^\./,,;s,^\.\./[^/]*,,;s,/,.,g;s,\.lean$,,;s,^,import LeanCamCombi.,' \
  | sort >"$dir"/../LeanCamCombi.lean
