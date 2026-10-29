#!/usr/bin/env python3
"""SO-DATA-PY step 3: emit the advice book of ONE torus as option-A Lean data modules (design §7.2: lint-clean,
at most 100 columns, well under 1500 lines per file; generated, never hand-edited).

usage: sodata_lean.py ADVICE.json OUTDIR [--torus Lower] [--chunk 512] [--lines 1400]

Format (proposed; the SO-DEFS / SO-DATA glue provides the decoder `KAM.SpinOrbit.Data.unzero`):
  * every advice window `rounded[s]` (2·blockLen - 1 slots) is run-length coded as a flat token list: a nonzero
    slot is itself, a run of n zero slots is the PAIR `0, n` (so every zero is followed by its count);
        unzero : List ℤ → List ℤ
          | [] => []
          | 0 :: n :: t => List.replicate n.toNat 0 ++ unzero t
          | v :: t => v :: unzero t
    the token list is cut into chunk definitions `p<i>.<part>W<s>C<c> : List Int` of at most CHUNK tokens (the
    elaborator measured failures at about 4096 literal elements, SO-REPLAY2), and the window is
    `unzero (c0 ++ c1 ++ …)`; an all-zero window is `List.replicate (2L - 1) 0`;
  * each literal is written in decimal or hexadecimal, whichever is shorter (`-0x…` for negatives);
  * modules (paths under OUTDIR):
      KAM/SpinOrbit/Data/<Torus>/Adv/Chunk<nnn>.lean   chunk definitions, packed greedily up to LINES lines
      KAM/SpinOrbit/Data/<Torus>/Adv/Part<nnn>.lean    the `PackedAdvice` of every real product
                                                       (`p<i>.rr`, `.ii`, `.ri`, `.ir`), importing its chunks
      KAM/SpinOrbit/Data/<Torus>/Adv/Book.lean         the advice books `fullBook`, `lowBook`, `graphBook`
                                                       (`AdviceBook`, entries `(key, .packed P rr ii ri ir)` or
                                                       `(key, .direct)`), joined from blocks of 16 entries
    all in namespace `KAM.SpinOrbit.Data.<Torus>`, `@[expose] public noncomputable section` (the kernel must
    unfold the data in `decide +kernel`).
The emitted bytes depend only on the advice JSON and the options (deterministic).  Untrusted tooling.
"""
import argparse
import hashlib
import json
import os

HEADER = """/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module
"""
COLS = 100
FORMAT_MODULE = "KAM.SpinOrbit.Data.Format"            # proposed glue: `unzero` (and the §B' types via imports)
PACKED_MODULE = "KAM.Certificate.Poly.Packed"          # SO-POLY-B: PackLayout, PackedAdvice
BOOK_MODULE = "KAM.Certificate.Model.Ops"              # SO-MALG: ProductAdvice, AdviceBook (A-E §B', §C)


def lit(v):
    d = str(v)
    h = ("-0x%x" % -v) if v < 0 else ("0x%x" % v)
    return h if len(h) < len(d) else d


def decode_rle(win, n):
    out = [0] * n
    for start, vals in win:
        out[start:start + len(vals)] = vals
    return out


def tokens(win, n):
    """the `unzero` token list of a window."""
    full = decode_rle(win, n)
    toks = []
    i = 0
    while i < n:
        if full[i] == 0:
            j = i
            while j < n and full[j] == 0:
                j += 1
            toks += [0, j - i]
            i = j
        else:
            toks.append(full[i])
            i += 1
    return toks


def unzero(toks):
    """Python mirror of the Lean decoder (tests the encoding)."""
    out, i = [], 0
    while i < len(toks):
        if toks[i] == 0 and i + 1 < len(toks):
            out += [0] * max(toks[i + 1], 0)
            i += 2
        else:
            out.append(toks[i])
            i += 1
    return out


def wrap_words(text):
    """a paragraph wrapped at COLS columns."""
    lines, cur = [], ""
    for wd in text.split(" "):
        if cur and len(cur) + 1 + len(wd) > COLS:
            lines.append(cur)
            cur = wd
        else:
            cur = (cur + " " + wd) if cur else wd
    return lines + [cur]


def wrap_items(items, indent, sep=","):
    """lines of separated items, each line at most COLS columns."""
    lines, cur = [], indent
    for k, it in enumerate(items):
        piece = it + (sep if k + 1 < len(items) else "")
        if len(cur) + len(piece) + 1 > COLS and cur.strip():
            lines.append(cur.rstrip())
            cur = indent
        cur += piece + " "
    if cur.strip():
        lines.append(cur.rstrip())
    return lines


def list_lines(name, typ, items):
    if not items:
        return ["def %s : %s := []" % (name, typ)]
    head = "def %s : %s := [" % (name, typ)
    body = wrap_items(items, "  ")
    body[-1] += "]"
    return [head] + body


def layout_term(L):
    lo, dims, stride, w, br = L
    return "⟨[%s], [%s], [%s], %d, %d⟩" % (", ".join(map(str, lo)), ", ".join(map(str, dims)),
                                          ", ".join(map(str, stride)), w, br)


def module_text(modname, imports, doc, ns, body_lines, opens=False):
    out = [HEADER]
    for im in imports:
        out.append("public import %s" % im)
    if imports:
        out.append("")
    out += wrap_words("/-! " + doc + " -/")
    out.append("")
    out.append("@[expose] public noncomputable section")
    out.append("")
    out.append("namespace %s" % ns)
    out.append("")
    if opens:
        out.append("open KAM.Certificate")
        out.append("")
    out += body_lines
    out.append("")
    out.append("end %s" % ns)
    out.append("")
    out.append("end")
    out.append("")
    return "\n".join(out)


def emit(adv, outdir, torus, chunk, max_lines):
    ns = "KAM.SpinOrbit.Data.%s" % torus
    base = os.path.join(outdir, "KAM", "SpinOrbit", "Data", torus, "Adv")
    os.makedirs(base, exist_ok=True)
    mod = "KAM.SpinOrbit.Data.%s.Adv" % torus
    # ---- products in book order, with a global index
    prods = []
    for book in ("full", "low", "graph"):
        for e in adv["books"].get(book, []):
            prods.append((book, e))
    # ---- chunk definitions and window terms
    chunk_defs = []                  # (product idx, lines)
    part_defs = []                   # (product idx, lines, [chunk names])
    largest = (0, "")
    for idx, (book, e) in enumerate(prods):
        if e["kind"] != "packed":
            continue
        for part in ("rr", "ii", "ri", "ir"):
            a = e["parts"][part]
            n = a["windowLen"]
            wterms = []
            names = []
            for s, win in enumerate(a["windows"]):
                if not win:
                    wterms.append("List.replicate %d 0" % n)
                    continue
                toks = tokens(win, n)
                assert unzero(toks) == decode_rle(win, n)
                cs = []
                for c in range(0, len(toks), chunk):
                    nm = "p%d.%sW%dC%d" % (idx, part, s, c // chunk)
                    items = [lit(v) for v in toks[c:c + chunk]]
                    for it in items:
                        if len(it) > largest[0]:
                            largest = (len(it), it)
                    chunk_defs.append((idx, list_lines(nm, "List Int", items)))
                    cs.append(nm)
                    names.append(nm)
                wterms.append("unzero (%s)" % " ++ ".join(cs) if len(cs) > 1 else "unzero %s" % cs[0])
            lines = ["/-- Advice of the `%s` real product of product %d (key %s). -/" % (part, idx, e["key"]),
                     "def p%d.%s : PackedAdvice where" % (idx, part),
                     "  la := %s" % layout_term(a["la"]),
                     "  lb := %s" % layout_term(a["lb"]),
                     "  target := %s" % layout_term(a["target"]),
                     "  scale := %d" % a["scale"],
                     "  outLog := %d" % a["outLog"]]
            # rounded: one window term per line (wrapped if long)
            rl = ["  rounded := ["]
            for k, t in enumerate(wterms):
                sep = "," if k + 1 < len(wterms) else "]"
                piece = "    " + t + sep
                if len(piece) <= COLS:
                    rl.append(piece)
                else:   # long `unzero (c0 ++ c1 ++ …)`: break at ++
                    parts_ = t[len("unzero ("):-1].split(" ++ ")
                    cur = "    unzero ("
                    for q, pp in enumerate(parts_):
                        add = pp + (" ++ " if q + 1 < len(parts_) else ")" + sep)
                        if len(cur) + len(add) > COLS:
                            rl.append(cur.rstrip())
                            cur = "      "
                        cur += add
                    rl.append(cur)
            if not wterms:
                rl = ["  rounded := []"]
            part_defs.append((idx, lines + rl, names))
    # ---- pack chunk defs into files
    files = {}
    chunk_file = {}
    cur, cur_lines, nfile = [], 0, 0
    overhead = 20

    def flush_chunks():
        nonlocal cur, cur_lines, nfile
        if not cur:
            return
        name = "Chunk%03d" % nfile
        body = []
        for lines in cur:
            body += lines + [""]
        files[name] = module_text("%s.%s" % (mod, name), [], "Generated advice data (run-length coded windows of "
                                  "packed products; see `Part*`). Do not edit.", ns, body[:-1])
        nfile += 1
        cur, cur_lines = [], 0

    for idx, lines in chunk_defs:
        if cur_lines + len(lines) + 1 + overhead > max_lines:
            flush_chunks()
        cur.append(lines)
        cur_lines += len(lines) + 1
        chunk_file[lines[0].split()[1]] = "Chunk%03d" % nfile
    flush_chunks()
    # ---- part files
    cur, cur_lines, nfile, cur_imps = [], 0, 0, set()

    def flush_parts():
        nonlocal cur, cur_lines, nfile, cur_imps
        if not cur:
            return
        name = "Part%03d" % nfile
        body = []
        for lines in cur:
            body += lines + [""]
        imps = sorted({PACKED_MODULE, FORMAT_MODULE}) + ["%s.%s" % (mod, c) for c in sorted(cur_imps)]
        files[name] = module_text("%s.%s" % (mod, name), imps, "Generated `PackedAdvice` data of the packed "
                                  "products (layouts, scale, outLog, windows). Do not edit.", ns, body[:-1], opens=True)
        nfile += 1
        cur, cur_lines, cur_imps = [], 0, set()

    part_file = {}
    for idx, lines, names in part_defs:
        imps = {chunk_file[n] for n in names}
        if cur and (cur_lines + len(lines) + 1 + overhead + len(cur_imps | imps) > max_lines):
            flush_parts()
        cur.append(lines)
        cur_lines += len(lines) + 1
        cur_imps |= imps
        part_file[idx] = "Part%03d" % nfile
    flush_parts()
    # ---- book
    body = []
    book_imps = sorted(set(part_file.values()))
    for book in ("full", "low", "graph"):
        ents = [(idx, e) for idx, (b, e) in enumerate(prods) if b == book]
        blocks = []
        for j in range(0, len(ents), 16):
            nm = "%sBook%d" % (book, j // 16)
            items = []
            for idx, e in ents[j:j + 16]:
                key = "[%s]" % ", ".join(map(str, e["key"]))
                if e["kind"] == "packed":
                    items.append("(%s, .packed %d p%d.rr p%d.ii p%d.ri p%d.ir)" % (key, e["P"], idx, idx, idx, idx))
                else:
                    items.append("(%s, .direct)" % key)
            body += ["def %s : AdviceBook := [" % nm] + ["  " + it + "," for it in items[:-1]] + \
                ["  " + items[-1] + "]", ""]
            blocks.append(nm)
        doc = {"full": "cfgFull", "low": "cfgLow", "graph": "checkSoGraph"}[book]
        body += ["/-- The advice book of the `%s` products. -/" % doc]
        if blocks:
            body += ["def %sBook : AdviceBook :=" % book] + wrap_items(blocks, "  ", sep=" ++")
        else:
            body += ["def %sBook : AdviceBook := []" % book]
        body.append("")
    files["Book"] = module_text("%s.Book" % mod, [BOOK_MODULE] + ["%s.%s" % (mod, p) for p in book_imps],
                                "Generated advice books of the %s torus. Do not edit." % torus.lower(), ns, body[:-1],
                                opens=True)
    # ---- write
    report = dict(files=[], largest_literal_chars=largest[0], largest_literal=largest[1][:24] + "…")
    for name in sorted(files):
        txt = files[name]
        p = os.path.join(base, name + ".lean")
        with open(p, "w") as fh:
            fh.write(txt)
        lines = txt.split("\n")
        report["files"].append(dict(name=name, lines=len(lines) - 1, bytes=len(txt.encode()),
                                    max_cols=max(len(x) for x in lines),
                                    sha256=hashlib.sha256(txt.encode()).hexdigest()))
    return report


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("advice")
    ap.add_argument("outdir")
    ap.add_argument("--torus", default=None)
    ap.add_argument("--chunk", type=int, default=512)
    ap.add_argument("--lines", type=int, default=1400)
    ap.add_argument("--standin", default=None, help="import this module instead of the three planned ones "
                    "(scratch elaboration tests against a stand-in of the §B' types and `unzero`)")
    args = ap.parse_args()
    global FORMAT_MODULE, PACKED_MODULE, BOOK_MODULE
    if args.standin:
        FORMAT_MODULE = PACKED_MODULE = BOOK_MODULE = args.standin
    adv = json.load(open(args.advice))
    torus = args.torus or adv["which"].capitalize()
    rep = emit(adv, args.outdir, torus, args.chunk, args.lines)
    fs = rep["files"]
    tot = sum(f["bytes"] for f in fs)
    print("%d files, %.2f MB, max %d lines, max %d columns, largest literal %d chars" % (
        len(fs), tot / 1e6, max(f["lines"] for f in fs), max(f["max_cols"] for f in fs), rep["largest_literal_chars"]))
    rep.update(total_bytes=tot, advice_sha256=hashlib.sha256(open(args.advice, "rb").read()).hexdigest(),
               chunk=args.chunk, max_lines=args.lines)
    combined = hashlib.sha256("".join(f["name"] + f["sha256"] for f in fs).encode()).hexdigest()
    rep["tree_sha256"] = combined
    with open(os.path.join(args.outdir, "emit_report_%s.json" % torus.lower()), "w") as fh:
        json.dump(rep, fh, indent=1, sort_keys=True)
    print("tree sha256 %s" % combined)


if __name__ == "__main__":
    main()
