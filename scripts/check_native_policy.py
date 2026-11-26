#!/usr/bin/env python3
"""Exact native_decide opt-ins; source guard and separate, real Lean endpoint audits."""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.(?:[A-Za-z_][A-Za-z0-9_']*|[0-9]+))*")
NATIVE = re.compile(r"\bnative_decide\b")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def fields(value, keys):
    require(isinstance(value, dict) and set(value) == set(keys), f"expected fields: {keys}")


def name(value):
    require(isinstance(value, str) and NAME.fullmatch(value), f"invalid Lean name: {value!r}")
    return value


def sources(root, include_imports):
    spec = importlib.util.spec_from_file_location("lean_modules", root / "scripts/check_lean_modules.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    def relevant_code(path):
        text = path.read_text(encoding="utf-8")
        # With no exceptions there is no import boundary to audit; only candidate native tokens need lexing.
        return module.code_mask(text) if include_imports or "native_decide" in text else ""
    return {p.relative_to(root).as_posix(): relevant_code(p)
            for p in root.rglob("*.lean")
            if not {".lake", ".drafts"}.intersection(p.relative_to(root).parts)
            and p.name != "lakefile.lean"}


def module_path(module):
    return module.replace(".", "/") + ".lean"


def closure(starts, code):
    seen, todo = set(), [starts] if isinstance(starts, str) else list(starts)
    # Lean import lists consume whitespace, including newlines. Quoted name components are identifiers too.
    component = r"(?:«[^»]+»|[^\W\d][\w']*)"
    token = re.compile(component + r"(?:\." + component + r")*")
    commands = set("module prelude public meta import namespace section end open export attribute local "
                   "scoped set_option variable universe noncomputable def theorem lemma abbrev instance "
                   "inductive structure class example syntax macro macro_rules elab elab_rules "
                   "declare_syntax_cat initialize builtin_initialize private protected axiom opaque "
                   "unsafe mutual include omit notation infix infixl infixr prefix postfix".split())
    while todo:
        module = todo.pop()
        if module in seen:
            continue
        seen.add(module)
        text = code.get(module_path(module), "")
        for directive in re.finditer(r"(?<![\w.])import(?![\w.])", text):
            tail = text[directive.end():].lstrip()
            if re.match(r"all\b", tail):
                tail = tail[3:].lstrip()
            found = False
            while match := token.match(tail):
                raw = match.group()
                if raw in commands:
                    break
                require(all(re.fullmatch(r"[\w']+", part) for part in re.findall(r"«([^»]+)»", raw)),
                        f"unsupported quoted import component in {module}: {raw}")
                todo.append(re.sub(r"«([^»]+)»", r"\1", raw))
                found = True
                tail = tail[match.end():].lstrip()
            require(found, f"unsupported or empty import in {module}")
    return seen


def load(root, code):
    policy = json.loads((root / "scripts/native-ci-exceptions.json").read_text())
    fields(policy, ["version", "exceptions", "audits"])
    require(type(policy["version"]) is int and policy["version"] == 1, "unsupported policy version")
    require(isinstance(policy["exceptions"], list) and isinstance(policy["audits"], list), "expected lists")
    exceptions, audits = {}, {}
    for entry in policy["exceptions"]:
        fields(entry, ["file", "feature", "justification", "audit"])
        path = entry["file"]
        require(isinstance(path, str) and path in code, f"missing or excluded exception file: {path!r}")
        require(path == module_path(name(path[:-5].replace("/", "."))), f"noncanonical path: {path}")
        require(not (root / path).is_symlink() and (root / path).resolve().is_relative_to(root.resolve()),
                f"exception must be an in-tree regular file: {path}")
        require(path not in exceptions, f"duplicate exception: {path}")
        require(entry["feature"] == "native_decide", "only native_decide can be exempted")
        require(isinstance(entry["justification"], str) and entry["justification"].strip(), "empty justification")
        require(NATIVE.search(code[path]), f"stale native_decide exception: {path}")
        name(entry["audit"])
        exceptions[path] = entry
    for audit in policy["audits"]:
        fields(audit, ["id", "kernel", "native", "native_axioms"])
        ident = name(audit["id"])
        require(ident not in audits, f"duplicate audit: {ident}")
        for mode in ("kernel", "native"):
            fields(audit[mode], ["module", "theorem"])
            endpoint = audit[mode]
            name(endpoint["module"])
            name(endpoint["theorem"])
            require(module_path(endpoint["module"]) in code, f"missing {mode} endpoint module")
        roots = audit["native_axioms"]
        require(isinstance(roots, list) and roots and all(isinstance(x, str) for x in roots),
                "native_axioms must list exact generated roots")
        require(len(roots) == len(set(roots)), "duplicate native axiom")
        allowed_modules = [p[:-5].replace("/", ".") for p, e in exceptions.items() if e["audit"] == ident]
        require(allowed_modules, f"audit without exception: {ident}")
        for ax in roots:
            name(ax)
            require(re.fullmatch(r".+\._native\.native_decide\.ax_[1-9][0-9]*(?:_[0-9]+)*", ax),
                    f"not an exact generated native root: {ax}")
        kernel = closure(audit["kernel"]["module"], code)
        native = closure(audit["native"]["module"], code)
        for path, entry in exceptions.items():
            module = path[:-5].replace("/", ".")
            require(module not in kernel, f"kernel endpoint imports exception: {path}")
            if entry["audit"] == ident:
                require(module in native, f"stale exception not reached by native endpoint: {path}")
        audits[ident] = audit
    for path, entry in exceptions.items():
        require(entry["audit"] in audits, f"missing endpoint audit for {path}")
    config = json.loads((root / "scripts/build_roots.json").read_text())
    prefixes = [p for app in config["applications"] for p in [app["lib"], *app["prefixes"]]]
    def protected(module):
        return (module.startswith(("KAM.Frozen.", "KAM.Provider."))
                or not any(module == p or module.startswith(p + ".") for p in prefixes))
    # Default Lake builds also include core .one globs outside the generated root. Protect every core
    # source, plus every frozen/provider module (including applications), rather than parsing Lake DSL.
    roots = [p[:-5].replace("/", ".") for p in code if protected(p[:-5].replace("/", "."))]
    kernel = closure(roots + [config["core"]["root"]], code) if exceptions else set()
    for path in exceptions:
        require(path[:-5].replace("/", ".") not in kernel,
                f"default kernel closure or frozen/provider closure imports exception: {path}")
    return exceptions, audits


def check_sources(root):
    raw = json.loads((root / "scripts/native-ci-exceptions.json").read_text())
    code = sources(root, include_imports=bool(raw.get("exceptions")))
    exceptions, audits = load(root, code)
    for path, text in code.items():
        require(path in exceptions or not NATIVE.search(text), f"unlisted native_decide: {path}")
    return exceptions, audits


def check_axioms(text, theorem, permitted, required=()):
    pattern = re.escape("'" + theorem + "'")
    reports = re.findall(pattern + r" depends on axioms:\s*\[([^]]*)\]", text, re.S)
    empty = re.findall(pattern + r" does not depend on any axioms", text)
    require(len(reports) + len(empty) == 1, f"missing or duplicate axiom report: {theorem}")
    actual = {x.strip() for x in reports[0].split(",") if x.strip()} if reports else set()
    require(actual <= permitted, f"unexpected axioms for {theorem}: {sorted(actual - permitted)}")
    require(set(required) <= actual, f"stale native roots for {theorem}: {sorted(set(required) - actual)}")


def run(args, root):
    result = subprocess.run(args, cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(result.stdout, end="", flush=True)
    require(result.returncode == 0, f"command failed: {' '.join(args)}")
    return result.stdout


def audit_endpoints(root, audits, mode):
    require(audits, "NO ENDPOINTS CONFIGURED: source policy is not proof verification")
    for ident, audit in audits.items():
        endpoint = audit[mode]
        modules = [endpoint["module"]]
        if mode == "native":
            modules.append(audit["kernel"]["module"])
        for module in dict.fromkeys(modules):
            run(["nice", "-n", "5", "lake", "build", module], root)
        if mode == "kernel":
            run(["lake", "env", "leanchecker", "--fresh", endpoint["module"]], root)
        probe = "\n".join("import " + m for m in dict.fromkeys(modules)) + "\n"
        probe += "#print axioms " + endpoint["theorem"] + "\n"
        if mode == "native":
            # Homogeneous equality checks identical endpoint types; proof irrelevance proves the equality.
            probe += ("example : @" + audit["kernel"]["theorem"] + " = @"
                      + endpoint["theorem"] + " := rfl\n")
        with tempfile.TemporaryDirectory(prefix="kam-native-policy-") as scratch:
            path = Path(scratch) / "EndpointAudit.lean"
            path.write_text(probe)
            output = run(["lake", "env", "lean", str(path)], root)
        roots = audit["native_axioms"] if mode == "native" else []
        check_axioms(output, endpoint["theorem"], STANDARD | set(roots), roots)
        print(f"PASS {mode} endpoint {ident}: {endpoint['theorem']}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--mode", choices=["source", "kernel", "native"], default="source")
    parser.add_argument("--count", action="store_true", help="print configured audit count for CI scheduling")
    args = parser.parse_args()
    try:
        exceptions, audits = check_sources(args.root)
        if args.count:
            print(len(audits))
        elif args.mode == "source":
            print(f"PASS source policy: {len(exceptions)} exceptions, {len(audits)} endpoint audits configured")
            if not audits:
                print("NO ENDPOINTS CONFIGURED: no kernel/native endpoint proof verification performed")
        else:
            audit_endpoints(args.root, audits, args.mode)
    except (ValueError, OSError, KeyError, TypeError) as error:
        sys.exit(f"native policy: {error}")


if __name__ == "__main__":
    main()
