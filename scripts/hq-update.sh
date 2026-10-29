#!/bin/bash
# Regenerate the live README sections, commit them, and push main.
# Called by cron (every 20 minutes) and by the post-commit hook (after every commit on main).
# Commits only README.md and docs/campaign/history.csv (plus merges of origin/main, see below).
#
# Collaborators also push to main. Before regenerating, new commits on origin/main are merged
# when the checkout has no uncommitted changes to tracked files. Conflicts confined to generated
# files are settled automatically: KAM.lean is regenerated, the README's live sections are
# regenerated (the local side of each conflict hunk is kept first), history.csv is a union. Any
# other conflict aborts the merge and is logged for the orchestrator; nothing is pushed then.
set -euo pipefail
cd "$(dirname "$0")/.."
root=$(pwd)
exec 8>"$(git rev-parse --git-common-dir)/hq-update.lock"
flock -w 120 8 || { echo "$(date -u '+%F %T') lock busy; skipped"; exit 0; }
# Only the main checkout on branch main updates the HQ (worktrees share the hooks).
[ "$(git rev-parse --abbrev-ref HEAD)" = main ] || { echo "not on main; skipped"; exit 0; }
[ "$(git rev-parse --show-toplevel)" = "$root" ] || exit 0
gitdir=$(git rev-parse --git-dir)
if [ -e "$gitdir/rebase-merge" ] || [ -e "$gitdir/rebase-apply" ] || [ -e "$gitdir/MERGE_HEAD" ]; then
  echo "rebase or merge in progress; skipped"; exit 0
fi
stamp() { date -u '+%F %T'; }

remote=0
if git remote get-url origin >/dev/null 2>&1; then
  remote=1
  git fetch -q origin main || { echo "$(stamp) fetch failed"; remote=0; }
fi
if [ "$remote" = 1 ] && ! git merge-base --is-ancestor origin/main HEAD; then
  if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
    echo "$(stamp) origin/main has new commits but the checkout has uncommitted changes; merge left to the orchestrator"
    remote=0
  elif ! HQ_UPDATING=1 git merge -q --no-edit origin/main >/dev/null 2>&1; then
    others=$(git diff --name-only --diff-filter=U | grep -v -x -e README.md -e KAM.lean -e docs/campaign/history.csv || true)
    if [ -n "$others" ]; then
      git merge --abort
      echo "$(stamp) merge of origin/main needs the orchestrator (conflicts: $others)"
      remote=0
    else
      python3 -I - <<'EOF'
import re
from pathlib import Path
p = Path("README.md")
t = p.read_text()
p.write_text(re.sub(r"<<<<<<< [^\n]*\n(.*?)=======\n.*?>>>>>>> [^\n]*\n", lambda m: m.group(1), t, flags=re.S))
h = Path("docs/campaign/history.csv")
lines = [l for l in h.read_text().splitlines() if l and not l.startswith(("<<<<<<<", "=======", ">>>>>>>"))]
head = [l for l in lines if l.startswith("utc,")][:1]
h.write_text("\n".join(head + sorted({l for l in lines if not l.startswith("utc,")})) + "\n")
EOF
      python3 -I scripts/gen_root_imports.py
      python3 -I scripts/hq-status.py >/dev/null
      git add README.md KAM.lean docs/campaign/history.csv docs/PAPERS.md docs/STATEMENTS.md
      HQ_UPDATING=1 git commit -q --no-edit
      echo "$(stamp) merged origin/main (generated-file conflicts settled) $(git rev-parse --short HEAD)"
    fi
  else
    echo "$(stamp) merged origin/main $(git rev-parse --short HEAD)"
  fi
fi

python3 -I scripts/hq-status.py >/dev/null
git add -- README.md docs/campaign/history.csv docs/PAPERS.md docs/STATEMENTS.md
if ! git diff --cached --quiet -- README.md docs/campaign/history.csv docs/PAPERS.md docs/STATEMENTS.md; then
  HQ_UPDATING=1 git commit -q -m "HQ status ($(date -u '+%Y-%m-%d %H:%M UTC'))" -- README.md docs/campaign/history.csv docs/PAPERS.md docs/STATEMENTS.md
  echo "$(stamp) committed $(git rev-parse --short HEAD)"
fi
if [ "$remote" = 1 ]; then
  git push -q origin main && echo "$(stamp) pushed" || echo "$(stamp) push failed"
fi
