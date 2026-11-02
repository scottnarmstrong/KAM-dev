#!/bin/bash
# V2-PACKED-CONS-PERF (untrusted tooling): reproduce run_packed.py's resume misattribution on a toy package, and
# check a patched driver. Tiny Lean processes only (a few MB each).
# Usage: cons_perf_drvtest.sh ORIG_run_packed.py PATCHED_run_packed.py WORKDIR
# Layout as V2-PACKED-GEN's: WORKDIR is a core package (lib Core0) holding the driver in scripts/packed/ (its CORE
# is ../..); WORKDIR/.lake/tpkg is the scratch package (lib LG00P: A <- B <- C <- D, E, F) requiring the core.
set -eu
orig=$(realpath "$1"); patched=$(realpath "$2"); T=$3
rm -rf "$T"; mkdir -p "$T/scripts/packed" "$T/.lake/tpkg/LG00P"; T=$(realpath "$T"); P=$T/.lake/tpkg
cd "$T"
echo "leanprover/lean4:v4.35.0" > lean-toolchain
printf 'import Lake\nopen Lake DSL\npackage core0\n@[default_target] lean_lib Core0\n' > lakefile.lean
printf 'module\n\npublic section\n\ndef core0 : Nat := 0\n' > Core0.lean
cp lean-toolchain "$P/"
printf 'import Lake\nopen Lake DSL\npackage tpkg\nrequire core0 from "../.."\nlean_lib LG00P\n' > "$P/lakefile.lean"
mk() { printf 'module\n\n%s\n\npublic section\n\n-- %s\ndef %s : Nat := 1\n' "$2" "$3" "$1" > "$P/LG00P/$4.lean"; }
mk a "public import Core0" v1 A; mk b "public import LG00P.A" v1 B; mk c "public import LG00P.B" v1 C
mk d "public import LG00P.C" v1 D; mk e "public import LG00P.C" v1 E
cp "$orig" scripts/packed/run_packed_orig.py; cp "$patched" scripts/packed/run_packed.py
lake build Core0 > /dev/null; (cd "$P" && lake update > /dev/null 2>&1)
built() { echo "  $1's process built: $(grep -o "Built [^ ]*" "$2/LG00P.$1.log" | sed 's/Built //' | tr '\n' ' ')"; }
echo "1. unpatched driver, target C"
python3 -I scripts/packed/run_packed_orig.py "$T/logO" 4G LG00P.C --pkg "$P" | grep -v "^LG00P"
echo "2. A's source re-emitted (a comment); unpatched driver resumes, target D"
sed -i 's/-- v1/-- v2/' "$P/LG00P/A.lean"
python3 -I scripts/packed/run_packed_orig.py "$T/logO" 4G LG00P.D --pkg "$P" | grep -v "^LG00P"
built D "$T/logO"
echo "3. A re-emitted again; patched driver resumes from the same ledger, target E"
mkdir -p "$T/logP"; cp "$T/logO/ledger.tsv" "$T/logP/"
sed -i 's/-- v2/-- v3/' "$P/LG00P/A.lean"
python3 -I scripts/packed/run_packed.py "$T/logP" 4G LG00P.E --pkg "$P" | grep -v "^LG00P"
built A "$T/logP"; built E "$T/logP"
echo "ledger (module, user s, exit, kind):"; cut -f1,2,7,8 "$T/logP/ledger.tsv" | sed 's/^/  /'
