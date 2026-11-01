#!/usr/bin/env python3
"""V2-PACKED-PROD (untrusted tooling; the kernel re-checks): one packed jet chain as production modules, in the
shared-data format of `docs/campaign/design/V2-PACKED-PROD-API.md`.

Reads `jet_extract_low.py`'s JSON and the mirror cache of `jet_low_gen.py --mirror-only --cache=…` (the exact nodes,
steps, characters and witness candidates), cuts the chain into blocks as `jet_low_gen.py` does (segments of at most
`--heavy` heavy steps and `--seg-io` imports + exports, the action slots by `--act`, the staged exponentials by
`--taylor`, the powers by `--pows`, the characters by `--char-keys`/`--char-io`), and writes under OUT/<P>/<T>/Jet/<C>/:
  - `Book`:     `jb<C> : JBook`, `b<C> : ℕ` (the largest load of a wanted node);
  - `Led<k>`:   the ledger nodes `n<C>_<key> : JLed` (each node once) and `led<C>_<k> : JLedger`, and the `inv`/`sqrt`
                candidates `cand<C>_<j> : PC`;
  - `Data`:     the key-only blocks `kb<C>_<i> : KBlock`, `blocks<C>`, the order certificate `cert<C>`, `jd<C>`;
  - `B<i>`:     `blk<C>_<i> : (kb<C>_<i>.toT (jd<C>.L.look (α := LGF))).ok 2 … = true` (`decide +kernel`);
  - `Chain`:    `jet<C>_check : jetCheck 2 lg00Cert.weight lg00Cert.piEnc lg00Cert.cfg<C> lg00Cert.emb lg00Jet.prog
                jd<C> b<C> wanted<C> = true` (`jetCheck_of`), and `jet<C>_check_cert`, the same at
                `lg00Cert.ham.jet` (the jet bridge `lg00Ham_jet`).
The order certificate names, for every import, the block that exports its key; every import is checked to have an
earlier exporter and every ledger node to be the exporter's exact node (by construction from the mirror).
Writes the module list in dependency order (OUT/`modules_<C>.txt`) and the plan (OUT/`<C>Plan.json`); for a tree
other than `TP` these are OUT/`modules_<T>_<C>.txt` and OUT/`<T><C>Plan.json` (one package holds several tori).
Usage: python3 -I scripts/packed/jet_prod_gen.py CHAIN.json MIRROR.pkl OUT --stage=Low|Full [--prefix=LG00P]
       [--tree=TP] [--heavy=8] [--seg-io=13] [--char-keys=2] [--char-io=12] [--act=4] [--taylor=3] [--pows=2]
       [--led-nodes=12]
"""
import json
import os
import pickle
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import jet_low_gen as JL      # noqa: E402  (reads --stage: the box of the chain)
JG = JL.JG
P, H = JG.P, JG.H


def opt(name, default):
    return next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--%s=" % name)), default)


STAGE = JL.STAGE
PRE, TREE = opt("prefix", "LG00P"), opt("tree", "TP")
NS = "%s.%s" % (PRE, TREE)
CFG = "cfg" + STAGE


def tf(b):
    return "true" if b else "false"


# keys: ('slot', j) | ('fac', j, neg, m) | ('w', j, neg) | ('term', j, neg, m) | ('sum', j, neg, m)
def key_lit(k):
    if k[0] == "slot":
        return "slotK %d" % k[1]
    if k[0] == "fac":
        return "facK %d %s %d" % (k[1], tf(k[2]), k[3])
    if k[0] == "w":
        return ".inr (.w %d %s)" % (k[1], tf(k[2]))
    return ".inr (.%s %d %s %d)" % (k[0], k[1], tf(k[2]), k[3])


def canon(k):
    return ("term",) + k[1:] if k[0] == "sum" and k[3] == 0 else k


def key_name(k):
    if k[0] == "slot":
        return "s%d" % k[1]
    return "%s%d%s%s" % (k[0], k[1], "n" if k[2] else "p", "" if k[0] == "w" else "_%d" % k[3])


class KB:
    """A key-only block: its Lean literal, its import and export keys (as `KBlock.imports`/`exports`)."""

    def __init__(self, kind, lit, imports, exports, heavy=0):
        self.kind, self.lit, self.imports, self.exports, self.heavy = kind, lit, imports, exports, heavy


def pc_text(C, name, x, defs):
    parts = []
    for pi, z in enumerate(x):
        if z == 0:
            parts.append("0")
            continue
        wn, Y, L1, L2 = JG.narrow(C, z)
        body, _ = JG.nat_tree(Y)
        defs.append("def %s_%d : ℕ :=\n%s\n" % (name, pi, body))
        parts.append("jSpread %d %d %d %d %d %d %d %s_%d" % (C.Lb.dims[0], C.Lb.dims[1], C.Lb.S, C.Lb.w, wn, L1,
                                                            L2, name, pi))
    return "⟨%s,\n    %s⟩" % tuple(parts)


def led_text(C, name, nd, defs):
    x = "⟨(%d), (%d)⟩" % nd.x if nd.u else pc_text(C, name + "x", nd.x, defs)
    al = ("2 ^ %d" % (nd.A.bit_length() - 1)) if nd.A == 2 ** (nd.A.bit_length() - 1) else "%d" % nd.A
    q = lambda m: "0" if m == 0 else "(%d / 2 ^ %d : ℚ)" % (m, P)
    defs.append("def %s : JLed :=\n  ⟨%s, %s, %d, %s, %s, %s⟩\n" % (name, tf(nd.u), al, nd.e, x, q(nd.r), q(nd.nb)))


def plan_blocks(C, D, S, steps, CH, wits):
    """The blocks in order (`jet_low_gen.plan_and_emit`'s cut) and the exported node of every ledger key."""
    ops, leaves, wanted = D["ops"], D["leaves"], set(D["wanted"])
    heavy_max = int(opt("heavy", "8" if STAGE == "Full" else "34"))
    seg_io = int(opt("seg-io", "13" if STAGE == "Full" else "0"))
    actions = sorted(int(j) for j, v in leaves.items() if v["kind"] == "action")
    assert not [j for j, v in leaves.items() if v["kind"] == "exp"]
    step_of = {t[0]: t for t in steps}
    last_use = {}
    for i in D["live"]:
        op = ops[i]
        rd = op[1:3] if op[0] in ("add", "mul") else op[1:2] if op[0] in ("inv", "sqrt", "exp") else []
        for x in rd:
            last_use[x] = max(last_use.get(x, -1), i)
    rdf = lambda u: ops[u[0]][1:3] if ops[u[0]][0] in ("add", "mul") else []

    def io_with(ch, t):
        dfn = {u[0] for u in ch} | {t[0]}
        imps = {x for u in ch + [t] for x in rdf(u)} - dfn
        return len(imps) + len([x for x in dfn if x in wanted or last_use.get(x, -1) > t[0]])
    chunks, seq, cur, hv = [], [], [], 0

    def flush():
        nonlocal cur, hv
        if cur:
            seq.append(("seg", len(chunks)))
            chunks.append(cur)
            cur, hv = [], 0
    for j in D["live"]:
        if j in step_of:
            t = step_of[j]
            h = (1 if t[1] else 0) + (1 if t[2] else 0)
            if cur and (hv + h > heavy_max or (seg_io and io_with(cur, t) > seg_io)):
                flush()
            cur.append(t)
            hv += h
        elif ops[j][0] in ("inv", "sqrt"):
            flush()
            seq.append(("wit", j))
    flush()
    pos = {}
    for q, (kind, v) in enumerate(seq):
        for j in ([t[0] for t in chunks[v]] if kind == "seg" else [v]):
            pos[j] = q
    seg_of = {t[0]: c for c, ch in enumerate(chunks) for t in ch}
    later = {}
    for q, (kind, v) in enumerate(seq):
        rd = [x for t in chunks[v] for x in rdf(t)] if kind == "seg" else [ops[v][1]]
        for x in rd:
            if x in seg_of and pos[x] != q:
                later.setdefault(x, set()).add(q)
    blocks, node_of, cands = [], {}, {}

    def put(k, nd):
        k = canon(k)
        if k in node_of:
            assert node_of[k] is nd or (node_of[k].x == nd.x and node_of[k].r == nd.r), ("ledger clash", k)
        node_of[k] = nd
    slot = lambda j: ("slot", j)
    # the action blocks
    act_k = int(opt("act", "4" if STAGE == "Full" else "0")) or len(actions)
    for g in range(0, len(actions), act_k):
        acts = actions[g:g + act_k]
        for j in acts:
            put(slot(j), S[j])
        blocks.append(KB("actions", ".actions [%s]" % ", ".join(map(str, acts)), [], [slot(j) for j in acts]))
    E_, pows_, _, Ns, _, _, TS = CH
    tay_k = int(opt("taylor", "3" if STAGE == "Full" else "0"))
    pow_k = int(opt("pows", "2" if STAGE == "Full" else "0"))
    for (j, neg), e in sorted(E_.items()):
        N = Ns[(j, neg)]
        fac = lambda m: ("fac", j, neg, m)
        if tay_k:
            T = TS[(j, neg)]
            put(("w", j, neg), T["w"])
            put(("term", j, neg, 0), T["ts"][0][0])
            assert T["ts"][0][1] is T["ts"][0][0]
            blocks.append(KB("tstart", ".tstart %d %s" % (j, tf(neg)), [],
                             [("w", j, neg), ("term", j, neg, 0), ("sum", j, neg, 0)], 1))
            for m0 in range(0, N, tay_k):
                k = min(tay_k, N - m0)
                put(("term", j, neg, m0 + k), T["ts"][m0 + k][0])
                put(("sum", j, neg, m0 + k), T["ts"][m0 + k][1])
                blocks.append(KB("tstep", ".tstep %d %s %d %d" % (j, tf(neg), m0, k),
                                 [("w", j, neg), ("term", j, neg, m0), ("sum", j, neg, m0)],
                                 [("term", j, neg, m0 + k), ("sum", j, neg, m0 + k)], 2 * k))
            put(fac(1), e)
            blocks.append(KB("texp", ".texp %d %s %d" % (j, tf(neg), N), [("w", j, neg), ("sum", j, neg, N)],
                             [fac(1)]))
        else:
            put(fac(1), e)
            blocks.append(KB("expo", ".expo %d %s %d" % (j, tf(neg), N), [], [fac(1)], 2 * N + 1))
        outs = pows_[(j, neg)]
        for m, o in enumerate(outs, 2):
            put(fac(m), o)
        if outs and not pow_k:
            blocks.append(KB("powsX", ".powsX %d %s %d" % (j, tf(neg), len(outs)), [fac(1)],
                             [fac(m) for m in range(2, len(outs) + 2)], len(outs)))
        elif outs:
            for g in range(0, len(outs), pow_k):
                m0 = 1 + g
                cnt = min(pow_k, len(outs) + 1 - m0)
                blocks.append(KB("pows", ".pows %d %s %d %d" % (j, tf(neg), m0, cnt), [fac(1), fac(m0)],
                                 [fac(m0 + 1 + i) for i in range(cnt)], cnt))
    # the character blocks
    char_slots = {}
    for j in D["live"]:
        if ops[j][0] == "char":
            char_slots.setdefault(tuple(ops[j][1]), []).append(j)
    ck = int(opt("char-keys", "2" if STAGE == "Full" else "8"))
    cio = int(opt("char-io", "12" if STAGE == "Full" else "48"))
    kfacs = lambda ks: {(i, ki < 0, abs(ki)) for k in ks for i, ki in enumerate(k) if ki}
    groups, cur = [], []
    for k in sorted(char_slots):
        nxt = cur + [k]
        if cur and (len(nxt) > ck or len(kfacs(nxt)) + sum(len(char_slots[x]) for x in nxt) > cio):
            groups.append(cur)
            nxt = [k]
        cur = nxt
    if cur:
        groups.append(cur)
    for ks in groups:
        facs = sorted(kfacs(ks))
        ents = sorted(j for k in ks for j in char_slots[k])
        for j in ents:
            put(slot(j), S[j])
        blocks.append(KB("chars", ".chars [%s] [%s]" % (", ".join("Sum.inr (%d, %s, %d)" % (i, tf(ng), m)
                                                                   for (i, ng, m) in facs),
                                                         ", ".join(map(str, ents))),
                         [("fac",) + f for f in facs], [slot(j) for j in ents], 2 * len(ks)))
    # the segments and the witnesses, in order
    for q, (kind, v) in enumerate(seq):
        if kind == "wit":
            j, a = v, ops[v][1]
            put(slot(j), S[j])
            cands[j] = wits[j]
            if ops[j][0] == "inv":
                lit = ".inv %d %d cand%s_%d" % (a, j, STAGE, j)
            else:
                lit = ".sqrt %d %d cand%s_%d 1 1 (1 / 2 : ℚ)" % (a, j, STAGE, j)
            blocks.append(KB(ops[j][0], lit, [slot(a)], [slot(j)], 2))
            continue
        ch = chunks[v]
        defined = {t[0] for t in ch}
        imp = sorted({x for t in ch for x in rdf(t)} - defined)
        exp = sorted(j for j in defined if any(qq > q for qq in later.get(j, ())) or j in wanted)
        for j in exp:
            put(slot(j), S[j])
        blocks.append(KB("seg", ".seg %d [%s]\n    [%s]\n    [%s]" % (
            ch[0][0], ", ".join(map(str, imp)), ", ".join("(%d, %d, %d)" % t for t in ch), ", ".join(map(str, exp))),
            [slot(j) for j in imp], [slot(j) for j in exp], sum((1 if t[1] else 0) + (1 if t[2] else 0) for t in ch)))
    for j in wanted:
        assert canon(slot(j)) in node_of, ("wanted slot not exported", j)
    return blocks, node_of, cands


def order_cert(blocks):
    """For every import (raw key, as `KBlock.imports`), the index of an earlier block exporting it."""
    first, cert = {}, []
    for i, b in enumerate(blocks):
        row = []
        for k in b.imports:
            assert k in first, ("import before its export", i, k)
            row.append(first[k])
        cert.append(row)
        for k in b.exports:
            assert k not in first, ("key exported twice", k)
            first[k] = i
    return cert


CH = 32                                                 # blocks per chunk of the block list


HEAD = """/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

%s

/-!
# %s (generated)

%s

LG00's %s jet chain on the packed box of half-width %d (`scripts/packed/jet_prod_gen.py`, V2-PACKED-PROD; data of
`%s`).
-/

@[expose] public noncomputable section

namespace %s

open KAM KAM.Certificate KAM.CertificateSharp.Packed

%s
end %s
"""


def write(out, mod, imports, title, doc, body, src):
    path = os.path.join(out, *mod.split(".")) + ".lean"
    os.makedirs(os.path.dirname(path), exist_ok=True)
    imp = "\n".join("public import %s" % m for m in imports)
    with open(path, "w") as f:
        f.write(HEAD % (imp, title, doc, "cfg" + STAGE, H, src, NS, body, NS))


def main():
    D = json.load(open(sys.argv[1]))
    ck = pickle.load(open(sys.argv[2], "rb"))
    out = sys.argv[3]
    assert ck["stage"] == STAGE and ck["H"] == H
    bk, S, steps, CH, wits = ck["bk"], ck["S"], ck["steps"], ck["chars"], ck["wits"]
    W = JL.F(D["weight"]["w"][0], D["weight"]["w"][1])
    C = JG.Ctx(W, bk.w)
    src = "lg00-app %s" % D["lg00_cert_commit"][:8]
    blocks, node_of, cands = plan_blocks(C, D, S, steps, CH, wits)
    cert = order_cert(blocks)
    C_ = STAGE
    base = "%s.Jet.%s" % (NS, C_)
    mods = []
    # the book
    wanted = sorted(D["wanted"])
    bmax = max(node_of[("slot", j)].A for j in wanted)
    book = ("def jb%s : JBook where\n  Lb := %s\n  LU0 := %s\n  Lw := %s\n  q := %d\n  lb := %d\n  lr := %d\n"
            "  lrb := %d\n  ln := %d\n  aW := %d\n  aB := %d\n  smax := %d\n  ls := %d\n  lsb := %d\n  off := %d\n"
            "  P := %d\n  aC := %d\n  lc := %d\n  lrc := %d\n  lnc := %d\n\n"
            "/-- The largest load of a wanted node. -/\ndef b%s : ℕ := %d\n"
            % (C_, JG.lay_lit(C.Lb), JG.lay_lit(C.LU0), JG.lay_lit(C.Lw), JG.Q, bk.lb, bk.lr, bk.lrb, bk.ln, bk.aW,
               bk.aB, bk.smax, bk.ls, bk.lsb, bk.off, bk.P, bk.aC, bk.lc, bk.lrc, bk.lnc, C_, bmax))
    write(out, base + ".Book", ["KAM.CertificateSharp.Packed.JetCheck"], "The book of the %s chain" % C_,
          "The packed box, its window, the one-slot layout, the scale and the guards.", book, src)
    mods.append(base + ".Book")
    # the ledger, in parts of at most `--led-nodes` nodes (in key order of first export)
    per = int(opt("led-nodes", "12"))
    # the wanted slots first: a consumer's read of a wanted slot then stops at the head of the ledger
    # (V2-PACKED-CONS-LOOKUP); every other key in order of first export
    wk = [("slot", j) for j in wanted]
    keys = wk + [k for k in node_of if k not in set(wk)]
    parts = [keys[i:i + per] for i in range(0, len(keys), per)]
    cand_items = sorted(cands.items())
    led_names = []
    for p_, ks in enumerate(parts):
        defs = []
        for k in ks:
            led_text(C, "n%s_%s" % (C_, key_name(k)), node_of[k], defs)
        if p_ == len(parts) - 1:
            for j, cd in cand_items:
                defs.append("def cand%s_%d : PC :=\n  %s\n" % (C_, j, pc_text(C, "cand%s_%dx" % (C_, j), cd.x, defs)))
        defs.append("def led%s_%d : JLedger :=\n  [%s]\n" % (C_, p_, ",\n   ".join(
            "(%s, n%s_%s)" % (key_lit(k), C_, key_name(k)) for k in ks)))
        write(out, "%s.Led%d" % (base, p_), ["KAM.CertificateSharp.Packed.JetCheck"],
              "Ledger part %d of the %s chain" % (p_, C_), "%d nodes, each once." % len(ks), "\n".join(defs), src)
        mods.append("%s.Led%d" % (base, p_))
        led_names.append("led%s_%d" % (C_, p_))
    # the blocks, the order certificate and the chain data
    body = []
    for i, b in enumerate(blocks):
        body.append("def kb%s_%d : KBlock :=\n  %s\n" % (C_, i, b.lit))
    # the block list in chunks of at most CH blocks (every list and proof of the chain stays shallow)
    nch = (len(blocks) + CH - 1) // CH
    for c in range(nch):
        body.append("def blocks%s_%d : List KBlock :=\n  [%s]\n" % (C_, c, ", ".join(
            "kb%s_%d" % (C_, i) for i in range(c * CH, min(len(blocks), (c + 1) * CH)))))
    body.append("def blocks%s : List KBlock :=\n  %s\n" % (C_, " ++ ".join("blocks%s_%d" % (C_, c)
                                                                           for c in range(nch))))
    body.append("def cert%s : List (List ℕ) :=\n  [%s]\n" % (C_, ", ".join("[%s]" % ", ".join(map(str, r))
                                                                         for r in cert)))
    body.append("def led%s : JLedger :=\n  %s\n" % (C_, " ++\n    ".join(led_names)))
    body.append("def jd%s : JetData := ⟨jb%s, led%s, blocks%s, cert%s⟩\n" % (C_, C_, C_, C_, C_))
    write(out, base + ".Data", [base + ".Book"] + ["%s.Led%d" % (base, p_) for p_ in range(len(parts))],
          "The blocks of the %s chain" % C_, "%d key-only blocks, the order certificate and the chain data."
          % len(blocks), "\n".join(body), src)
    mods.append(base + ".Data")
    stmt = lambda i: ("(kb%s_%d.toT (jd%s.L.look (α := LGF))).ok 2 lg00Cert.weight lg00Cert.piEnc\n"
                      "      lg00Cert.%s jb%s lg00Cert.emb lg00Jet.prog = true" % (C_, i, C_, CFG, C_))
    for i, b in enumerate(blocks):
        write(out, "%s.B%d" % (base, i), [base + ".Data", "%s.%s.Data.Cert" % (PRE, TREE), PRE + ".Jet"],
              "Block %d of the %s chain" % (i, C_), "A `%s` block, %d heavy steps, %d imports, %d exports."
              % (b.kind, b.heavy, len(b.imports), len(b.exports)),
              "theorem blk%s_%d :\n    %s := by\n  decide +kernel\n" % (C_, i, stmt(i)), src)
        mods.append("%s.B%d" % (base, i))
    wl = "torsionSlots 2 lg00Jet" if STAGE == "Low" else "lg00Jet.v0 :: d1Slots 2 lg00Jet"
    wlc = "torsionSlots 2 lg00Cert.ham.jet" if STAGE == "Low" else \
        "lg00Cert.ham.jet.v0 :: d1Slots 2 lg00Cert.ham.jet"
    P_ = ("(kb.toT (jd%s.L.look (α := LGF))).ok 2 lg00Cert.weight lg00Cert.piEnc\n      lg00Cert.%s jb%s "
          "lg00Cert.emb lg00Jet.prog = true" % (C_, CFG, C_))
    chunks_txt = []
    for c in range(nch):
        ids = range(c * CH, min(len(blocks), (c + 1) * CH))
        chunks_txt.append("/-- The blocks of chunk %d. -/\ntheorem chunk%s_%d :\n    ∀ kb ∈ blocks%s_%d, %s := by\n"
                          "  simp only [blocks%s_%d, List.forall_mem_cons]\n  exact ⟨%s,\n    List.forall_mem_nil _⟩\n"
                          % (c, C_, c, C_, c, P_, C_, c, ",\n    ".join("blk%s_%d" % (C_, i) for i in ids)))
    chain = ("/-- The wanted slots of the %s chain. -/\ndef wanted%s : List ℕ := %s\n\n%s\n"
             "/-- **The %s chain, one theorem**: the keyed chain at LG00's program and embedding. -/\n"
             "theorem jet%s_check :\n    jetCheck 2 lg00Cert.weight lg00Cert.piEnc lg00Cert.%s lg00Cert.emb "
             "lg00Jet.prog\n      jd%s b%s wanted%s = true := by\n"
             "  refine jetCheck_of (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)\n"
             "    (by decide +kernel)\n"
             "  show ∀ kb ∈ blocks%s, %s\n"
             "  simp only [blocks%s, List.forall_mem_append, and_assoc]\n"
             "  exact ⟨%s⟩\n"
             % (C_, C_, wl, "\n".join(chunks_txt), C_, C_, CFG, C_, C_, C_, C_, P_, C_,
                ", ".join("chunk%s_%d" % (C_, c) for c in range(nch))))
    write(out, base + ".Chain", ["%s.B%d" % (base, i) for i in range(len(blocks))],
          "The %s chain as one theorem" % C_, "`jetCheck_of` over the %d block theorems, the order certificate "
          "(decided on keys) and the wanted slots." % len(blocks), chain, src)
    mods.append(base + ".Chain")
    cert_chain = ("/-- The %s chain at the certificate's own jet (the jet bridge `lg00Ham_jet`). -/\n"
                  "theorem jet%s_check_cert :\n    jetCheck 2 lg00Cert.weight lg00Cert.piEnc lg00Cert.%s "
                  "lg00Cert.emb\n      lg00Cert.ham.jet.prog jd%s b%s (%s) = true := by\n"
                  "  show jetCheck 2 lg00Cert.weight lg00Cert.piEnc lg00Cert.%s lg00Cert.emb lg00Ham.jet.prog "
                  "jd%s\n    b%s (%s) = true\n"
                  "  rw [lg00Ham_jet]\n  exact jet%s_check\n"
                  % (C_, C_, CFG, C_, C_, wlc, CFG, C_, C_, wlc.replace("lg00Cert.ham", "lg00Ham"), C_))
    write(out, base + ".ChainCert", [base + ".Chain", PRE + ".JetBridge"],
          "The %s chain at the certificate's jet" % C_, "`jet%s_check` moved to `lg00Cert.ham.jet` by the jet "
          "bridge (LG00's shared `lg00Ham_jet`; built once, above 4 GiB)." % C_, cert_chain, src)
    tag = "" if TREE == "TP" else TREE
    with open(os.path.join(out, "modules_%s%s.txt" % (tag + "_" if tag else "", C_)), "w") as f:
        f.write("\n".join(mods) + "\n")
    plan = dict(stage=STAGE, source=src, blocks=[dict(i=i, kind=b.kind, heavy=b.heavy, imports=len(b.imports),
                                                      exports=len(b.exports)) for i, b in enumerate(blocks)],
                ledger_nodes=len(node_of), ledger_parts=len(parts), wanted=wanted, b=bmax,
                wanted_radii={str(j): [float(JL.F(node_of[("slot", j)].r, 2 ** P)),
                                       float(JL.F(node_of[("slot", j)].nb, 2 ** P))] for j in wanted})
    json.dump(plan, open(os.path.join(out, "%s%sPlan.json" % (tag, C_)), "w"), indent=1)
    kinds = {}
    for b in blocks:
        kinds[b.kind] = kinds.get(b.kind, 0) + 1
    print(json.dumps(dict(blocks=len(blocks), kinds=kinds, ledger_nodes=len(node_of), parts=len(parts),
                          max_seg_io=max([len(b.imports) + len(b.exports) for b in blocks if b.kind == "seg"] + [0]),
                          b=bmax.bit_length())))


if __name__ == "__main__":
    main()
