#!/usr/bin/env python3
"""S3 (RUNBOOK §7): add the approved LP entries to manifest/frozen-anchors.json, hashes from the guard's own code.

usage: lp_manifest_add.py --root <tree> --approved <sha>:<draft dir> --approval approval-D62.json
                          [--abi abi.json] [--manifest <path>] [--emit-new-only] [--list-provider-paths]
                          [--repo <git repo holding the approved commit>]

From each approved manifest-entry draft: `author_approval` and `split_policy.ruling_ref` from the approval record;
`state` from the approval record (D62: froze and sealed in one pass, as track R); `full_file_sha256` (definitions),
`prefix_sha256`/`suffix_sha256` (theorems, split by `Guard.check_theorem_region`) and every
`definition_closure[].sha256` computed with `Guard.digest` over the files of --root. Each drafted closure is
cross-checked against the import closure of frozen definition files (regex of docs/tracks/W/freeze/add_track.py,
extended to all `KAM/Frozen/**/Defs/*`); a difference stops. `abi_sha256` is 64 zeros (phase 1) or the value
from --abi (phase 2). Every other field is the approved draft's. The existing entries must stay JSON-equal; the
new entry key sets must equal the guard schema. Writes the manifest in place (or --manifest), or with
--emit-new-only prints a manifest holding only the new entries (for scripts/abi_hashes.py).
"""
from __future__ import annotations

import argparse
import copy
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lp_freeze_lib as L  # noqa: E402

ZERO = "0" * 64
IMPORT = re.compile(r"(?m)^(?:public )?import (KAM\.Frozen\.(?:[\w.]+\.)?Defs\.\w+)$")
COMMON = {"id", "kind", "author_approval", "source", "contract", "path", "export", "abi_sha256",
          "definition_closure", "state", "split_policy"}


def closure(root: Path, rel: str) -> list[str]:
    def mp(m):
        return m.replace(".", "/") + ".lean"
    seen, todo = set(), IMPORT.findall((root / rel).read_text())
    while todo:
        m = todo.pop()
        if m not in seen:
            seen.add(m)
            todo += IMPORT.findall((root / mp(m)).read_text())
    return sorted(mp(m) for m in seen)


def build(root: Path, repo: Path, spec: str, approval: dict, abi: dict) -> list[dict]:
    guard = L.load_guard(repo)
    out = []
    for d in L.approved_entries(repo, spec):
        e = copy.deepcopy(d)
        e["author_approval"] = dict(approval["author_approval"])
        e["split_policy"]["ruling_ref"] = approval["ruling_ref"]
        e["state"] = approval["state"]
        text = (root / e["path"]).read_bytes().decode("utf-8")
        if e["kind"] == "definition":
            e["full_file_sha256"] = L.digest(guard, text)
        else:
            pre, _body, suf = L.split_theorem(guard, repo, text)
            e["prefix_sha256"] = L.digest(guard, pre)
            e["suffix_sha256"] = L.digest(guard, suf)
        drafted = [c["path"] for c in e["definition_closure"]]
        computed = closure(root, e["path"])
        if sorted(drafted) != computed:
            raise SystemExit(f"{e['id']}: drafted definition_closure differs from the import closure: "
                             f"only drafted {sorted(set(drafted) - set(computed))}, "
                             f"only computed {sorted(set(computed) - set(drafted))}")
        e["definition_closure"] = [{"path": p, "sha256": L.digest(guard, (root / p).read_bytes())} for p in drafted]
        e["abi_sha256"] = abi.get(e["export"], ZERO)
        expect = (COMMON | {"implementation", "prefix_sha256", "suffix_sha256", "draft_allowlist"}
                  if e["kind"] == "theorem" else COMMON | {"full_file_sha256"})
        assert set(e) == expect, (e["id"], set(e) ^ expect)
        out.append(e)
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--repo")
    ap.add_argument("--approved", required=True, action="append")
    ap.add_argument("--approval", required=True)
    ap.add_argument("--abi")
    ap.add_argument("--manifest")
    ap.add_argument("--base-manifest", help="manifest to extend (default: the --manifest file itself)")
    ap.add_argument("--emit-new-only", action="store_true")
    ap.add_argument("--list-provider-paths", action="store_true")
    a = ap.parse_args()
    root = Path(a.root).resolve()
    repo = Path(a.repo).resolve() if a.repo else root
    approval = json.loads(Path(a.approval).read_text())
    abi = json.loads(Path(a.abi).read_text()) if a.abi else {}
    new = [x for spec in a.approved for x in build(root, repo, spec, approval, abi)]
    if a.list_provider_paths:
        for e in new:
            if e["kind"] == "theorem":
                print(e["implementation"]["module"].replace(".", "/") + ".lean")
        return 0
    mpath = Path(a.manifest) if a.manifest else root / "manifest/frozen-anchors.json"
    base = json.loads(Path(a.base_manifest or mpath).read_text())
    if a.emit_new_only:
        doc = {k: v for k, v in base.items() if k != "anchors"}
        doc["anchors"] = new
        print(json.dumps(doc, indent=1, ensure_ascii=False))
        return 0
    newids = {e["id"] for e in new}
    old = [x for x in base["anchors"] if x["id"] not in newids]
    before = json.loads(Path(a.base_manifest or mpath).read_text())["anchors"]
    assert [x for x in before if x["id"] not in newids] == old
    clash = {x["path"] for x in old} & {e["path"] for e in new} | {x["export"] for x in old} & {e["export"] for e in new}
    assert not clash, clash
    base["anchors"] = old + new
    mpath.parent.mkdir(parents=True, exist_ok=True)
    mpath.write_text(json.dumps(base, indent=1, ensure_ascii=False) + "\n")
    print(f"{len(new)} LP entries ({sum(e['kind'] == 'definition' for e in new)} definitions, "
          f"{sum(e['kind'] == 'theorem' for e in new)} theorems; state {approval['state']}; ABI "
          f"{'filled' if abi else 'zero placeholders'}); {len(old)} existing entries unchanged; "
          f"manifest now {len(base['anchors'])} -> {mpath}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
