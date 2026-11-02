#!/bin/bash
# LOCK-DATA write guard: before writing into KAM/SpinOrbit/Data/LockN65, make every target a regular file.
#   lock_guard.sh FILE [FILE ...]
# A target that is a symlink (generated data on the volume) is replaced by a regular copy of its content, so a
# write never goes through the link into a source tree on the volume. Prints what it changed.
for f in "$@"; do
  if [ -L "$f" ]; then
    t=$(readlink -f "$f")
    cp --remove-destination "$t" "$f" && echo "guard: $f was a symlink to $t; now a regular copy"
  fi
done
