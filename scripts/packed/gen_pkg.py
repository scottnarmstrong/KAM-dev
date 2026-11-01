#!/usr/bin/env python3
"""V2-PACKED-GEN: the opt-in Lake package of LG00's packed modules (untrusted tooling; nothing here is trusted).

The packed modules of a torus prove facts about the torus's own certificate (`LG00.TP.lg00Cert`), so they import
LG00's generated data. LG00's package (`applications/lg00` on branch `lg00-app`) is read only for this work, and the
core's default build must never contain an application module (D51). So the packed modules live in a SCRATCH Lake
package (default `<core worktree>/.lake/lg00-packed`, never committed, never in the core's build):

  - its `lakefile.lean` is LG00's, byte for byte, except the path of the core: the package keeps LG00's name
    `kam-lg00` and its library `LG00` with LG00's Lean options, so a module's Lake trace is the one LG00's run
    computed whenever its sources and the core modules it imports are identical;
  - `lake-manifest.json` is LG00's with the core's path; `.lake/packages` is a symlink to the core's packages;
  - the LG00 modules the packed proof imports (`--roots`, closed under `public import LG00.*`) are COPIED from
    LG00's tree (sources) and their built artifacts are reused: `.olean*` and `.ir` hardlinked (Lake replaces
    them, never rewrites them in place), every other artifact (`.trace`, `.hash`, `.ilean`, `.ir.sig`, `.c`) copied,
    so nothing this package's Lake does can change LG00's files;
  - the generated packed modules (`gen_packed.py`) form a second library `LG00Packed` (modules `LG00Packed.**`,
    LG00's options plus the profiler, so the run harness reads each module's kernel time).

Then `lake build --no-build <roots>` (from the package directory) lists the reused modules that are stale against
this core: LG00's run built them against `lg00-app`'s core, which differs from `main` only in files no data module
imports (`V2/SiteSign.lean`, `V2/SiteShard.lean`: the `Final` and `Main` modules of each torus are stale).

`--like PKG [--core DIR]`: mirror another scratch package's configuration (kamx-packed's `kam-lg00p`) on the core at
DIR instead of LG00's, and `--lg00 PKG` reuses that package's modules: the jet route's integration package.
`--keep-config` reuses modules from another source into an existing package (no configuration written);
`--add-lg00-lib` appends LG00's library with LG00's options (LG00's own modules imported read only);
`--require-lg00 DIR` requires the package at DIR (named `kam-lg00`, holding LG00's built modules) instead: the
package name enters every Lake trace, so LG00's artifacts are reused only under LG00's package name.
Usage: python3 -I scripts/packed/gen_pkg.py [--pkg DIR] [--lg00 DIR] [--like PKG] [--core DIR] [--keep-config]
       [--add-lg00-lib] [--check] ROOT_MODULE...
"""
import json
import os
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CORE = os.path.abspath(os.path.join(HERE, "..", ".."))
LG00 = "/home/scott/KAM-dev-worktrees/lg00-app/applications/lg00"
PKG = os.path.join(CORE, ".lake", "lg00-packed")
IMP = re.compile(r"^public import (\S+)", re.M)
LINK_EXT = (".olean", ".olean.server", ".olean.private", ".ir")
# Workarounds for defects in LG00's generated sources, applied to the COPIES only (reported to the orchestrator;
# LG00's files are never written). `LG00.<T>.Final.Freq` opens `KAM.CertificateSharp.V2` but its import closure has
# no V2 module, so the `open` fails ("unknown namespace") and every name after it with it.
_FREQ = ("public import LG00.Confinement.Main\n",
         "public import LG00.Confinement.Main\npublic import KAM.CertificateSharp.V2.RouteARefinedS\n")
PATCHES = {"LG00.TP.Final.Freq": _FREQ, "LG00.TPP.Final.Freq": _FREQ}
PACKED_LIB = """
/-- The packed modules of V2-PACKED-GEN (`scripts/packed/gen_packed.py`): LG00's Lean options plus the profiler,
so the run harness reads each module's kernel time (`type checking took`). -/
lean_lib «LG00Packed» where
  leanOptions := lg00LeanOptions ++ #[⟨`profiler, true⟩, ⟨`profiler.threshold, (50 : Nat)⟩]

"""


def src_path(root, m):
    return os.path.join(root, *m.split(".")) + ".lean"


LOCAL = ("LG00", "LG00P")              # the package-local module roots (everything else is the core or Mathlib)


def closure(lg00, roots):
    """The package-local modules imported (transitively) by the roots, and the core modules they import."""
    seen, core, stack = set(), set(), list(roots)
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        for d in IMP.findall(open(src_path(lg00, m), encoding="utf-8").read()):
            if d.split(".")[0] in LOCAL and os.path.exists(src_path(lg00, d)):
                stack.append(d)
            elif d.split(".")[0] not in LOCAL:
                core.add(d)
    return seen, core


def add_lg00_lib(pkg, lg00_app):
    """Append LG00's library (LG00's own Lean options, from its lakefile) to a package's lakefile, so LG00's built
    modules can be imported read only with their traces intact (orchestrator, 2026-11-01: the packed copy imports
    LG00's own Hamiltonian results instead of re-proving them)."""
    lf_path = os.path.join(pkg, "lakefile.lean")
    lf = open(lf_path, encoding="utf-8").read()
    if "lean_lib «LG00» where" in lf:
        return
    src = open(os.path.join(lg00_app, "lakefile.lean"), encoding="utf-8").read()
    opts = re.search(r"def lg00LeanOptions : Array LeanOption := #\[.*?\n\]", src, re.S).group(0)
    lf += ("\n/-- LG00's modules, imported read only (V2-PACKED-GEN): LG00's own Lean options. -/\n%s\n\n"
           "lean_lib «LG00» where\n  leanOptions := lg00LeanOptions\n" % opts)
    open(lf_path, "w", encoding="utf-8").write(lf)


def require_lg00(pkg, dep):
    """`require «kam-lg00» from DEP` (a package holding LG00's built modules under LG00's own package name, so their
    traces hold: the package name enters every trace), with its manifest entry."""
    lf_path = os.path.join(pkg, "lakefile.lean")
    lf = open(lf_path, encoding="utf-8").read()
    rel = os.path.relpath(os.path.abspath(dep), pkg)
    if "require «kam-lg00»" not in lf:
        lf = re.sub(r'(require kam from "[^"]*")', r'\1\n\n/-- LG00\'s own modules, read only (V2-PACKED-GEN). -/\n'
                    r'require «kam-lg00» from "%s"' % rel, lf, count=1)
        open(lf_path, "w", encoding="utf-8").write(lf)
    man = json.load(open(os.path.join(pkg, "lake-manifest.json")))
    if not any(p["name"] in ("«kam-lg00»", "kam-lg00") for p in man["packages"]):
        man["packages"].insert(1, {"type": "path", "scope": "", "name": "«kam-lg00»",
                                   "manifestFile": "lake-manifest.json", "inherited": False, "dir": rel,
                                   "configFile": "lakefile.lean"})
        json.dump(man, open(os.path.join(pkg, "lake-manifest.json"), "w"), indent=1)


def write_config_like(pkg, like, core):
    """The configuration of another scratch package (kamx-packed's `kam-lg00p`, V2-PACKED-PROD), its core path
    replaced: same package name, libraries and options, so that package's built modules keep their Lake traces."""
    os.makedirs(os.path.join(pkg, ".lake"), exist_ok=True)
    rel = os.path.relpath(core, pkg)
    lf = open(os.path.join(like, "lakefile.lean"), encoding="utf-8").read()
    lf = re.sub(r'require kam from "[^"]*"', 'require kam from "%s"' % rel, lf, count=1)
    open(os.path.join(pkg, "lakefile.lean"), "w", encoding="utf-8").write(lf)
    shutil.copyfile(os.path.join(core, "lean-toolchain"), os.path.join(pkg, "lean-toolchain"))
    man = json.load(open(os.path.join(like, "lake-manifest.json")))
    for p in man["packages"]:
        if p["name"] == "kam":
            p["dir"] = rel
    json.dump(man, open(os.path.join(pkg, "lake-manifest.json"), "w"), indent=1)
    link = os.path.join(pkg, ".lake", "packages")
    if not os.path.islink(link):
        os.symlink(os.path.relpath(os.path.join(core, ".lake", "packages"), os.path.join(pkg, ".lake")), link)


def write_config(pkg, lg00):
    os.makedirs(os.path.join(pkg, ".lake"), exist_ok=True)
    rel = os.path.relpath(CORE, pkg)
    lf = open(os.path.join(lg00, "lakefile.lean"), encoding="utf-8").read()
    assert lf.count('require kam from "../.."') == 1
    lf = lf.replace('require kam from "../.."', 'require kam from "%s"' % rel)
    lf = lf.replace("/-- LG00 (decision D51)", "/-- SCRATCH COPY (V2-PACKED-GEN, scripts/packed/gen_pkg.py) of LG00's package;"
                    " LG00 (decision D51)", 1)
    lf += PACKED_LIB
    open(os.path.join(pkg, "lakefile.lean"), "w", encoding="utf-8").write(lf)
    shutil.copyfile(os.path.join(CORE, "lean-toolchain"), os.path.join(pkg, "lean-toolchain"))
    man = json.load(open(os.path.join(lg00, "lake-manifest.json")))
    for p in man["packages"]:
        if p["name"] == "kam":
            p["dir"] = rel
    json.dump(man, open(os.path.join(pkg, "lake-manifest.json"), "w"), indent=1)
    link = os.path.join(pkg, ".lake", "packages")
    target = os.path.relpath(os.path.join(CORE, ".lake", "packages"), os.path.join(pkg, ".lake"))
    if not os.path.islink(link):
        os.symlink(target, link)


def reuse(pkg, lg00, mods):
    """Copy the sources; reuse the built artifacts (hardlink the big immutable ones, copy the rest)."""
    nsrc = nlink = ncopy = 0
    for m in sorted(mods):
        rel = os.path.join(*m.split("."))
        dst = src_path(pkg, m)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        text = open(src_path(lg00, m), encoding="utf-8").read()
        if m in PATCHES:
            old, new = PATCHES[m]
            if old in text and new not in text:
                text = text.replace(old, new, 1)
        changed = not os.path.exists(dst) or open(dst, encoding="utf-8").read() != text
        if changed:
            open(dst, "w", encoding="utf-8").write(text)
            nsrc += 1
            for sub in (os.path.join("lib", "lean"), "ir"):     # the old artifacts belong to the old source
                ddir = os.path.join(pkg, ".lake", "build", sub, os.path.dirname(rel))
                base = os.path.basename(rel)
                if os.path.isdir(ddir):
                    for fn in os.listdir(ddir):
                        if fn.split(".")[0] == base:
                            os.remove(os.path.join(ddir, fn))
        if m in PATCHES:
            continue                      # a patched copy is rebuilt here: never reuse LG00's artifacts for it
        for sub in (os.path.join("lib", "lean"), "ir"):
            sdir = os.path.join(lg00, ".lake", "build", sub, os.path.dirname(rel))
            ddir = os.path.join(pkg, ".lake", "build", sub, os.path.dirname(rel))
            base = os.path.basename(rel)
            if not os.path.isdir(sdir):
                continue
            os.makedirs(ddir, exist_ok=True)
            for fn in os.listdir(sdir):
                if not (fn.startswith(base + ".") and fn[len(base):].count(".") >= 1):
                    continue
                if fn.split(".")[0] != base:
                    continue
                s, d = os.path.join(sdir, fn), os.path.join(ddir, fn)
                if fn.endswith(LINK_EXT):
                    if os.path.exists(d) and os.stat(d).st_ino == os.stat(s).st_ino:
                        continue              # the same file: up to date
                    if os.path.exists(d):
                        os.remove(d)          # the source package rebuilt it (Lake writes a new file)
                    os.link(s, d)
                    nlink += 1
                else:
                    if os.path.exists(d) and open(d, "rb").read() == open(s, "rb").read():
                        continue
                    shutil.copy2(s, d)
                    ncopy += 1
    return nsrc, nlink, ncopy


def check(pkg, mods):
    """`lake build --no-build` per module: the reused modules that are stale against this core."""
    stale = []
    for m in mods:
        r = subprocess.run(["lake", "build", "--no-build", m], cwd=pkg, capture_output=True, text=True)
        if r.returncode != 0:
            stale.append(m)
    return stale


def main():
    args = sys.argv[1:]
    pkg, lg00 = PKG, LG00
    if "--pkg" in args:
        i = args.index("--pkg")
        pkg = os.path.abspath(args[i + 1])
        del args[i:i + 2]
    if "--lg00" in args:
        i = args.index("--lg00")
        lg00 = os.path.abspath(args[i + 1])
        del args[i:i + 2]
    like = core = None
    if "--like" in args:                         # mirror another scratch package's configuration
        i = args.index("--like")
        like = os.path.abspath(args[i + 1])
        del args[i:i + 2]
    if "--core" in args:
        i = args.index("--core")
        core = os.path.abspath(args[i + 1])
        del args[i:i + 2]
    keep = "--keep-config" in args              # another source of modules into an existing package
    add_lib = "--add-lg00-lib" in args
    do_check = "--check" in args
    roots = [a for a in args if not a.startswith("--")]
    if keep:
        pass
    elif like:
        write_config_like(pkg, like, core or CORE)
    else:
        write_config(pkg, lg00)
    if add_lib:
        add_lg00_lib(pkg, LG00)
    if "--require-lg00" in args:
        i = args.index("--require-lg00")
        require_lg00(pkg, args[i + 1])
        roots = [r for r in roots if r != args[i + 1]]
    mods, core = closure(lg00, roots)
    print("roots %s: %d LG00 modules, %d core imports" % (roots, len(mods), len(core)))
    print("sources copied %d, artifacts hardlinked %d, copied %d" % reuse(pkg, lg00, mods))
    json.dump(dict(roots=roots, lg00=lg00, modules=sorted(mods), core_imports=sorted(core)),
              open(os.path.join(pkg, "reused.json"), "w"), indent=1)
    if do_check:
        st = check(pkg, roots)
        print("stale roots:", st)


if __name__ == "__main__":
    main()
