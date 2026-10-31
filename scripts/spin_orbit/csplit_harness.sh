#!/bin/bash
# SO-CSEG-GEN typecheck harness (no kernel work): emit a SKELETON tree (every literal cut to one term; the types
# unchanged), replace every `decide +kernel` by `sorry` in that scratch copy, place it in the worktree, elaborate it
# through the compile gate, then remove it and its build outputs.  `sorry` never leaves the scratch copy.
#   csplit_harness.sh lower|upper SCRATCH [MODULES...]   (default: every emitted module)
set -u
w=$1; S=$2; shift 2
T=$(python3 -c "print('$w'.capitalize())")
WT=/root/code/KAM-inp-sodata3
D=/mnt/HC_Volume_106379410/kam-data
rm -rf $S; mkdir -p $S
python3 -B $WT/scripts/spin_orbit/csplit_emit.py $w $D/so-data3/g2 $D/so-cseg/plan_$w.json $D/so-cseg/ledger_$w.pkl $S --skeleton || exit 1
find $S -name "*.lean" -exec sed -i 's/decide +kernel/sorry/g' {} +
rm -rf $WT/KAM/SpinOrbit/Data/$T/Seg
cp -r $S/KAM/SpinOrbit/Data/$T/Seg $WT/KAM/SpinOrbit/Data/$T/Seg
cp $S/KAM/SpinOrbit/Data/CsegJet.lean $S/KAM/SpinOrbit/Data/CsegJetEq.lean $WT/KAM/SpinOrbit/Data/
mods=("$@")
if [ ${#mods[@]} -eq 0 ]; then
  mods=($(cd $WT && find KAM/SpinOrbit/Data/$T/Seg -name "*.lean" | sed 's/\.lean$//; s#/#.#g'))
fi
df -h / | tail -1
/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh $WT "${mods[@]}" > $S/harness.log 2>&1
echo "rc=$?"
grep -E "^error|error:" $S/harness.log | grep -v "declaration uses 'sorry'" | sort | uniq | head -40
[ -n "${KEEP:-}" ] || rm -rf $WT/KAM/SpinOrbit/Data/$T/Seg $WT/KAM/SpinOrbit/Data/CsegJet.lean $WT/KAM/SpinOrbit/Data/CsegJetEq.lean
[ -n "${KEEP:-}" ] || rm -rf $WT/.lake/build/lib/lean/KAM/SpinOrbit/Data/$T/Seg $WT/.lake/build/ir/KAM/SpinOrbit/Data/$T/Seg \
  $WT/.lake/build/lib/lean/KAM/SpinOrbit/Data/CsegJet* $WT/.lake/build/ir/KAM/SpinOrbit/Data/CsegJet*
df -h / | tail -1
