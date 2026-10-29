#!/bin/sh
# Check project Lean sources for forbidden proof escapes, resource overrides and size limits,
# plus the module-system, root-import and frozen-anchor invariants.
# Run from anywhere; `lake lint` runs it too.

set -eu

project_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
status=0

lean_files() {
  find "$project_root" -type f -name '*.lean' ! -path '*/.lake/*' ! -path '*/.drafts/*' ! -name 'lakefile.lean'
}

check_pattern() {
  pattern=$1
  label=$2
  matches=$(lean_files | xargs -r grep -nE "$pattern" || true)
  if [ -n "$matches" ]; then
    printf '%s\n%s\n' "forbidden $label:" "$matches" >&2
    status=1
  fi
}

# `sorry` is allowed only as the exact manifest-bound body of a DRAFT_SORRY frozen anchor;
# check_frozen_anchors.py enforces that, so plain `sorry` is checked outside KAM/Frozen only.
sorries=$(lean_files | grep -v '/KAM/Frozen/' | xargs -r grep -nE '(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)' || true)
if [ -n "$sorries" ]; then
  printf '%s\n%s\n' 'forbidden sorry outside KAM/Frozen:' "$sorries" >&2
  status=1
fi
check_pattern '(^|[^[:alnum:]_])admit([^[:alnum:]_]|$)' 'admit'
check_pattern '(^|[^[:alnum:]_])axiom([^[:alnum:]_]|$)' 'axiom'
check_pattern '(^|[^[:alnum:]_])unsafe([^[:alnum:]_]|$)' 'unsafe'
check_pattern '(^|[^[:alnum:]_])opaque([^[:alnum:]_]|$)' 'opaque'
check_pattern 'set_option[[:space:]]+(maxHeartbeats|maxRecDepth|synthInstance\.maxHeartbeats)' \
  'resource-limit override'
# EuclideanSpace is banned in code (comments and strings may mention it).
euclid=$(lean_files | python3 -I -c '
import sys, re, importlib.util
spec = importlib.util.spec_from_file_location("m", sys.argv[1]); m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
for f in sys.stdin.read().split():
    code = m.code_mask(open(f, encoding="utf-8").read())
    for i, line in enumerate(code.splitlines(), 1):
        if re.search(r"\bEuclideanSpace\b", line):
            print(f"{f}:{i}")
' "$project_root/scripts/check_lean_modules.py")
if [ -n "$euclid" ]; then
  printf '%s\n%s\n' 'forbidden EuclideanSpace in code (use `Fin n → ℝ`; see AGENTS.md):' "$euclid" >&2
  status=1
fi

# Proof escapes past the kernel and metaprogramming that can add declarations, in code only (comments and strings
# may mention them). Found missing by the guard mutation suite (I-GUARDS, 2026-10-29: 18 accepted mutations).
# Providers may be imported only by a frozen anchor and the generated root KAM.lean (ruling 2026-10-29 15:35).
escapes=$(lean_files | python3 -I -c '
import sys, re, importlib.util
spec = importlib.util.spec_from_file_location("m", sys.argv[1]); m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
root = sys.argv[2]
bad = [
    (r"\bnative_decide\b", "native_decide"),
    (r"\bdecide\s*\+\s*native\b|\bnative\s*:=\s*true\b", "decide +native"),
    (r"\bofReduce(Bool|Nat)\b", "Lean.ofReduceBool / ofReduceNat"),
    (r"\bskipKernelTC\b", "debug.skipKernelTC"),
    (r"#eval\b|\brun_cmd\b|\brun_elab\b|\brun_meta\b|\bby_elab\b", "code execution (#eval, run_cmd, run_elab, run_meta, by_elab)"),
    (r"\baddDecl\b|\baddDeclCore\b", "addDecl"),
    (r"^\s*(@\[[^\]]*\]\s*)*((private|protected|local|scoped)\s+)*(elab|elab_rules|declare_syntax_cat)\b",
     "elaborator definition (runs arbitrary meta code)"),
    # File-local tactic macros only expand syntax to ordinary tactics, so they are allowed; global ones are not.
    (r"^\s*(@\[[^\]]*\]\s*)*((private|protected|scoped)\s+)*(macro|macro_rules|syntax)\b",
     "non-local macro or syntax definition (use `local macro`)"),
    (r"\b(command_elab|term_elab|tactic_elab|tactic)\s*\]|@\[\s*(command_elab|term_elab|tactic)\b", "elaborator attribute"),
    (r"\bsorryAx\b", "sorryAx"),
    (r"\bimplemented_by\b|@\[\s*extern\b", "implemented_by / extern"),
]
for f in sys.stdin.read().split():
    code = m.code_mask(open(f, encoding="utf-8").read())
    rel = f[len(root) + 1:]
    for i, line in enumerate(code.splitlines(), 1):
        for pat, label in bad:
            if re.search(pat, line):
                print(f"{rel}:{i}: {label}")
        if re.match(r"\s*(public\s+)?(meta\s+)?import\s+KAM\.Provider\.", line) and not (
                rel.startswith("KAM/Frozen/") or rel == "KAM.lean"):
            print(f"{rel}:{i}: provider imported outside its frozen anchor and the generated root")
' "$project_root/scripts/check_lean_modules.py" "$project_root")
if [ -n "$escapes" ]; then
  printf '%s\n%s\n' 'forbidden proof escapes or provider imports in code:' "$escapes" >&2
  status=1
fi

# Count Unicode characters consistently: some awk versions count UTF-8 bytes.
overlong_lines=$(python3 -I - "$project_root" <<'PY'
import re
import sys
from pathlib import Path

root = Path(sys.argv[1])
for path in sorted(root.rglob('*.lean')):
    if path.name == 'lakefile.lean' or {'.lake', '.drafts'} & set(path.relative_to(root).parts):
        continue
    for line_number, line in enumerate(path.read_text(encoding='utf-8').splitlines(), 1):
        if len(line) > 100 and not re.search(r'https?://|^(public\s+)?(meta\s+)?import\s', line):
            print(f'{path}:{line_number}:{len(line)}')
PY
)
if [ -n "$overlong_lines" ]; then
  printf '%s\n%s\n' 'Lean lines over 100 characters:' "$overlong_lines" >&2
  status=1
fi

oversize_files=$(lean_files | xargs -r awk 'FNR == 1501 { print FILENAME }')
if [ -n "$oversize_files" ]; then
  printf '%s\n%s\n' 'Lean files over 1500 lines:' "$oversize_files" >&2
  status=1
fi

python3 -I "$project_root/scripts/gen_root_imports.py" --check || status=1
python3 -I "$project_root/scripts/render_errata.py" --check || status=1
python3 -I "$project_root/scripts/check_lean_modules.py" --root "$project_root" || status=1
# The anchor guard rejects an empty manifest; until the first anchor is frozen, instead require
# that KAM/Frozen holds no Lean file at all.
manifest="$project_root/manifest/frozen-anchors.json"
if python3 -I -c 'import json, sys; sys.exit(0 if json.load(open(sys.argv[1]))["anchors"] else 1)' \
    "$manifest"; then
  python3 -I "$project_root/scripts/check_frozen_anchors.py" --root "$project_root" \
    --manifest "$manifest" || status=1
  # Elaborated statement hashes (needs the frozen modules built: `lake build`).
  python3 -I "$project_root/scripts/abi_hashes.py" "$project_root" "$manifest" --check || status=1
else
  frozen=$(find "$project_root/KAM/Frozen" -type f -name '*.lean' 2>/dev/null || true)
  if [ -n "$frozen" ]; then
    printf '%s\n%s\n' 'Lean files under KAM/Frozen without any manifest anchor:' "$frozen" >&2
    status=1
  fi
fi

exit "$status"
