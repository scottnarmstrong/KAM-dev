#!/usr/bin/env python3
"""Add (or refresh) the manifest entries of a frozen track, preserving all other entries.

usage: kam_manifest_add_track.py <repo root> <freeze.json> <track-config.json> [abi.json]
freeze.json: name -> [kind, path, namespace] (from kam_freeze_track.py).
track-config.json: {"approval": {...}, "revision": str, "default_range": str, "ranges": {name: str},
                    "track": "Iso", "id_prefix": "iso"}
Without abi.json the new ABI hashes are zero placeholders (phase 1); with it they are filled (phase 2).
"""
import hashlib
import json
import re
import sys
from pathlib import Path

root = Path(sys.argv[1]).resolve()
freeze = json.loads(Path(sys.argv[2]).read_text())
cfg = json.loads(Path(sys.argv[3]).read_text())
abi = json.loads(Path(sys.argv[4]).read_text()) if len(sys.argv) > 4 else {}
mpath = root / "manifest/frozen-anchors.json"
manifest = json.loads(mpath.read_text())
ZERO = "0" * 64


def digest(b):
    return hashlib.sha256(b).hexdigest()


IMPORT = re.compile(r"^(?:public )?import (KAM\.Frozen\.(?:[\w.]+\.)?Defs\.\w+)$", re.M)


def mod_path(mod):
    return root / (mod.replace(".", "/") + ".lean")


def closure(path):
    seen, todo = set(), list(IMPORT.findall(path.read_text()))
    while todo:
        m = todo.pop()
        if m not in seen:
            seen.add(m)
            todo += IMPORT.findall(mod_path(m).read_text())
    return sorted(seen)


new_paths = {v[1] for v in freeze.values()}
anchors = [a for a in manifest["anchors"] if a["path"] not in new_paths]
for name, (kind, rel, ns) in freeze.items():
    p = root / rel
    export = f"{ns}.{name}"
    stem = Path(rel).stem
    e = {
        "id": f"{cfg['id_prefix']}.{name}.v1",
        "kind": "theorem" if kind == "theorem" else "definition",
        "author_approval": cfg["approval"],
        "source": {"revision": cfg["revision"], "range": cfg["ranges"].get(name, cfg["default_range"])},
        "contract": {"id": f"{cfg['id_prefix']}.{name}", "version": "1"},
        "path": rel,
        "export": export,
        "split_policy": {"source_group": f"{cfg['id_prefix']}.{name}", "mode": "NOT_SPLIT",
                         "ruling_ref": cfg["approval"]["approval_ref"].split(";")[-1].strip()},
        "abi_sha256": abi.get(export, ZERO),
        "definition_closure": [{"path": str(mod_path(m).relative_to(root)), "sha256": digest(mod_path(m).read_bytes())}
                               for m in closure(p)],
    }
    if kind == "theorem":
        text = p.read_text()
        e["implementation"] = {"module": f"KAM.Provider.{cfg['track']}.{stem}",
                               "export": f"KAM.Provider.{cfg['track']}.{name}"}
        e["state"] = "DRAFT_SORRY"
        pb = text.index("FROZEN_ANCHOR_PROOF_BEGIN")
        body_start = text.index("\n", pb) + 1
        body_end = text.rfind("\n", 0, text.index("FROZEN_ANCHOR_PROOF_END")) + 1
        e["prefix_sha256"] = digest(text[:body_start].encode())
        e["suffix_sha256"] = digest(text[body_end:].encode())
        e["draft_allowlist"] = {"frozen_paths": [], "audit_paths": []}
    else:
        e["state"] = "SEALED"
        e["full_file_sha256"] = digest(p.read_bytes())
    anchors.append(e)
manifest["anchors"] = anchors
mpath.write_text(json.dumps(manifest, indent=1, ensure_ascii=False) + "\n")
print(f"{len(freeze)} entries for track {cfg['track']}; manifest now {len(anchors)} anchors")
