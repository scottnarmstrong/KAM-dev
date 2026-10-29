#!/bin/bash
# Land a local branch (e.g. the sub-orchestrator's `inp`) into main, in the main checkout.
# usage: scripts/land-branch.sh BRANCH
# Runs under the HQ lock. Refuses if the main checkout has uncommitted changes to tracked files (retry later).
# Merges BRANCH with --no-ff, regenerates the root import file, runs the full source lint and `lake build`;
# on any failure the merge is undone (the checkout was clean before it) and the reason is printed.
# On success the merge commit is pushed. Never force-pushes.
set -euo pipefail
branch=${1:?usage: land-branch.sh BRANCH}
main=/root/code/KAM
cd "$main"
exec 8>"$(git rev-parse --git-common-dir)/hq-update.lock"
flock -w 600 8 || { echo "LAND-SKIPPED: lock busy"; exit 2; }
[ "$(git rev-parse --abbrev-ref HEAD)" = main ] || { echo "LAND-SKIPPED: main checkout not on main"; exit 2; }
if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
  echo "LAND-SKIPPED: main checkout has uncommitted changes; retry later"; exit 2
fi
git fetch -q origin main || true
if ! git merge-base --is-ancestor origin/main HEAD; then
  HQ_UPDATING=1 git merge -q --no-edit origin/main || { git merge --abort; echo "LAND-FAILED: cannot merge origin/main"; exit 1; }
fi
before=$(git rev-parse HEAD)
if git merge-base --is-ancestor "$branch" HEAD; then echo "LAND-NOOP: $branch already in main"; exit 0; fi
if ! HQ_UPDATING=1 git merge -q --no-ff --no-edit "$branch" -m "Land $branch into main"; then
  git merge --abort; echo "LAND-FAILED: merge conflict between $branch and main; merge main into $branch first"; exit 1
fi
fail() { git reset -q --hard "$before"; echo "LAND-FAILED: $1"; exit 1; }
python3 -I scripts/gen_root_imports.py
if ! git diff --quiet -- KAM.lean; then git add KAM.lean && HQ_UPDATING=1 git commit -q -m "Regenerate root imports after landing $branch"; fi
nice -n 5 lake build >/tmp/land-build.log 2>&1 || fail "lake build (see /tmp/land-build.log)"
sh scripts/lint_sources.sh >/tmp/land-lint.log 2>&1 || fail "source lint (see /tmp/land-lint.log)"
git push -q origin main || fail "push"
echo "LANDED: $branch at $(git rev-parse --short HEAD)"
# The merges above run with HQ_UPDATING=1, which the git hooks skip, so refresh the campaign HQ README here
# (2026-10-29: landings left the README up to 20 minutes stale). Runs in the background.
mkdir -p .hq; nohup sh scripts/hq-update.sh >> .hq/hq-update.log 2>&1 &
