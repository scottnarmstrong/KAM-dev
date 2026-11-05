#!/bin/bash
# V2-PACKED-PROD-TPP (untrusted tooling): T''s preparation (run before prod_tpp_pipe.sh): extract both chains from
# LG00's T'' generator state (saved in ~/kam-data), then both bit-exact mirrors concurrently, each under 8 GiB.
# Waits while the user's anonymous memory is above 20 GB before each Python process.
cd /home/scott/KAM-dev-worktrees/v2-packed
T=.lake/v2-packed-prod/tpp; S=$HOME/kam-data/v2-packed-prod/gen_tpp_L18; APP=/home/scott/KAM-dev-worktrees/lg00-app
mkdir -p $T
st=/sys/fs/cgroup/user.slice/user-$(id -u).slice/memory.stat
gate() { while [ "$(awk '$1 == "anon" {print $2}' "$st")" -gt 20000000000 ]; do sleep 30; done; }
for s in Low Full; do
  lc=$(echo $s | tr A-Z a-z); gate
  ( time bash scripts/packed/py_capped.sh scripts/packed/jet_extract_low.py $S/state.pkl $T/$lc.json $APP \
      --stage=$s ) > $T/${lc}_extract.log 2>&1 || exit 1
done
for s in Low Full; do
  lc=$(echo $s | tr A-Z a-z); gate
  ( time bash scripts/packed/py_capped.sh scripts/packed/jet_low_gen.py $T/$lc.json --stage=$s --mirror-only \
      --cache=$T/${lc}_mirror.pkl ) > $T/${lc}_mirror.log 2>&1 &
done
wait
echo PREP DONE
