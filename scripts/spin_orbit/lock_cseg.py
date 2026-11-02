#!/usr/bin/env python3
"""LOCK-DATA (B1): SO-CSEG-GEN's emitter on the N = 65 lock, with the exp / inv / sqrt arms (untrusted tooling).

`csplit_emit.Emitter` (unchanged; this shim only subclasses it) emits the segmented proof of a lunar torus; its
forced one-op segments cover `.mul` and the character slot.  The lock's program also has fallible `exp`, `inv` and
`sqrt` slots carrying packed products (4 of each per chain), so this shim

* renames the lunar data (`SoBackendV2` -> `LockBackend`, precision 112, `soJetLit` -> `lockJetLit`, the modules
  under `KAM.SpinOrbit.Data.LockN65.Seg`), and takes the advice books and the character witnesses from the lock's
  own generation (`gen.pkl`) instead of the lunar JSON files;
* adds the forced exp / inv / sqrt segments, proved through the lock-owned routes
  (`KAM/SpinOrbit/Data/LockN65/SegRoutes.lean`) from their memoized products and the values of
  `lock_fallible.py`;
* gives every packed product of those slots its operands (`operands`), so `emit_products` memoizes them like
  the lunar ones;
* writes every term list compactly (`terms_defs_z`: `tmsOf (zdecs …)`, ZRows.lean; B3 lever (a)), unless
  LOCK_ZROWS=0.

    SO_LOCK_DATA=... SO_LOCK_SIZE=... python3 lock_cseg.py GENDIR PLAN.json LEDGER.pkl FALLIBLE.pkl OUTROOT \
        [--slots S1,S2,...]      # only the forced segments at these slots (and their products): small probes
"""
import os
from fractions import Fraction
import pickle
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.set_int_max_str_digits(0)
import csplit_emit as CE     # noqa: E402
import sofx_packed as SP     # noqa: E402

import lock_zadv as LZ      # noqa: E402

CE.TY = "LockBackend"
CE.P = 112
TY = CE.TY
wrap, fixed, nat_list = CE.wrap, CE.fixed, CE.nat_list
PLAN_CHUNK = 150         # entries per plan-list chunk
TERMS_PER_DEF = 900       # about one hex line per term: a definition stays under the file's line cap


def terms_defs_z(name, terms, named=False):
    """`csplit_emit.terms_defs` in the compact form: each chunk `name.cK` is `tmsOf (zdecs [...])` (ZRows.lean) of
    the flat list `k0, k1, re, im, ...`; the same names and the same returned expression."""
    if not terms:
        if named:
            return ["def %s : List (CertKey × CC %s) := []" % (name, TY), ""], name
        return [], "[]"
    chunks = [terms[i:i + TERMS_PER_DEF] for i in range(0, len(terms), TERMS_PER_DEF)]
    out = []
    for k, ch in enumerate(chunks):
        flat = [int(x) for (k0, k1), (re, im) in ch for x in (k0, k1, re, im)]
        assert LZ.decode_check(flat) == flat
        cs = LZ.chunks(flat)
        out.append("def %s.c%d : List (CertKey × CC %s) := tmsOf (zdecs [" % (name, k, TY))
        for i, (n, b) in enumerate(cs):
            out.append("  (%d, 0x%x)" % (n, int.from_bytes(b, "little")) + ("," if i + 1 < len(cs) else "])"))
        out.append("")
    if len(chunks) == 1 and not named:
        return out, "%s.c0" % name
    nm = ["%s.c%d" % (name, k) for k in range(len(chunks))]
    out += wrap(["def %s : List (CertKey × CC %s) := List.flatten [" % (name, TY)] +
                [x + "," for x in nm[:-1]] + [nm[-1] + "]"], "") + [""]
    return out, name


if os.environ.get("LOCK_ZROWS", "1") != "0":
    CE.terms_defs = terms_defs_z

EXPD = "(⟨⟨[]⟩, 0, 0⟩ : ExpWitness %s)" % TY
INVD = "(⟨[]⟩ : CertPoly %s)" % TY
SQD = "((0, ⟨⟨[]⟩, 0, 0⟩) : ℕ × SqrtWitness %s)" % TY
CHD = "(([], ⟨⟨[]⟩, 0, 0⟩) : CertKey × ExpWitness %s)" % TY


SH_GROUP = 4             # shards per kernel theorem for heavy products (D55, 10 GB lane; one shard 3.2–4.7 GB on literals)
HEAVY_PAIRS = 10 ** 7    # a product part is heavy from this operand pair count on (M0 2.4e7, M1 3.2e7)
LED_HEAVY = os.environ.get("LOCK_LED_HEAVY", "1") == "1"   # ledger-routed heavy products get operand literals
REM_LIGHT_MIN = 256      # a light product part with this many slots also gets the RemSplit literal: the inline
                         # remainder bound of M1900 (cfgLow) hit the elaborator's maximum recursion depth (measured)
REMLIT = {}              # `adv.remainderBound W (2 * P)` -> its literal (the product statements carry it)
REMCLASS = set()         # (product, part) pairs given the literal (reported)
SPLIT_AUX = True         # heavy products: side checks one module each (D55 joined form measured 5-7x slower:
                         # M203 1231 s CPU joined vs 172 s for its 20 side-check modules; light products joined)
EXP_SPLIT = False        # D55: one module per exp residual (<= 6.0 GiB, measured)
HEAVYADV = set()         # advice names of heavy product parts
NSHARDS = {}             # advice name (`advFull.p0.rr`) -> number of shards, filled by LockEmitter
_GRP = re.compile(r"^( *)checkPackedSp_of_groups (\S+) (.*?)\s+\[(\S+)\.shardRange\]\s+(\(by decide \+kernel\)|\S+)\s+\(fun s hs => "
                  r"⟨\S+\.shardRange, List\.mem_singleton_self _, hs⟩\)\s+\(fun g hg => by rw "
                  r"\[List\.mem_singleton\.1 hg\]; exact (\S+)\)", re.M | re.S)
DECSPLIT = "KAM.SpinOrbit.Data.LockN65.DecSplit"
REMSPLIT = "KAM.SpinOrbit.Data.LockN65.RemSplit"
PAIRCODE = "KAM.SpinOrbit.Data.LockN65.PairCode"
EXPSPLIT = "KAM.SpinOrbit.Data.LockN65.ExpSplit"
REM_CHUNK = 4000         # slots per remainder-bound range (D55; 2000-slot ranges < 1 GB, measured)


def _hang(text):
    """a tactic line: two-space first line, six-space continuation"""
    ls = wrap(text.split(" "), "      ")
    ls[0] = "  " + ls[0].lstrip()
    return ls


def natlit(n):
    """a natural-number literal: plain when short, else `natOfChunks [0x…, …]` (256-bit digits)"""
    if n < 1 << 256:
        return "%d" % n
    ds = []
    while n:
        ds.append(n & ((1 << 256) - 1))
        n >>= 256
    return "(natOfChunks [%s])" % ", ".join("0x%x" % d for d in reversed(ds))


def _weight_w():
    """`base.weight.w` of the lock (Params.lean literal)."""
    t = open(os.path.join(HERE, "../../KAM/SpinOrbit/Data/LockN65/Params.lean")).read()
    m = re.search(r"def weight : CertWeight :=\s*⟨\(([^)]*)\),\s*\(([^)]*)\)", t)
    a, b = m.group(2).split("/")
    return Fraction(int(a), int(b))


WEIGHT_W = _weight_w()
PRODSTMT = {}            # product module -> (theorem, [(operand term, name)])
ADVOBJ = {}              # advice name -> the part object (sofx_packed mirror)
_DEC = re.compile(r"^theorem (\S+)_dec : dyadicTerms \(2 \* (\d+)\) (\S+)\.scale (\(fun v => ⟨[^⟩]*⟩\)) "
                  r"(\(\(\S+\.targetTerms, .*\)\.1\)) = some (\S+) := eq_some_of_termsBeq_cseg "
                  r"\(by decide \+kernel\)$")
_SH = re.compile(r"^theorem (\S+) : (\S+)\.shardRange\.all (.*) = true := by$")


def _split2(t):
    """the two top-level parenthesised arguments `(ea) (eb)` of a string"""
    d, cut = 0, None
    for i, ch in enumerate(t):
        d += ch == "("
        d -= ch == ")"
        if d == 0 and ch == ")":
            cut = i + 1
            break
    return t[:cut].strip(), t[cut:].strip()


LIGHT_GROUP = 4          # light products too: the single all-shard group (M7, 14 shards) was OOM-killed at 10 GB


def _groups(n, adv=None):
    g = SH_GROUP if (adv is None or adv in HEAVYADV) else LIGHT_GROUP
    return [list(range(i, min(i + g, n))) for i in range(0, n, g)]


def _group_lit(n, adv=None):
    return "[" + ", ".join("[" + ", ".join(map(str, g)) + "]" for g in _groups(n, adv)) + "]"


def _lock_jet_names(body, imports):
    """the landed stage templates name the band's jet (`soJetLit`, `CsegJetEq`): the lock's are `lockJetLit` and
    `JetEq.lock_jet`; the stage-side jet theorem becomes `lock_jetB` (no clash with `JetEq.lock_jet`)"""
    t = "\n".join(body)
    if "soJetLit" not in t and "CsegJetEq" not in " ".join(imports):
        return body, imports
    t = re.sub(r"\block_jet\b", "lock_jetB", t)
    t = t.replace("soJetLit_eq", "lock_jet").replace("soJetLit", "lockJetLit")
    imports = ["KAM.SpinOrbit.Data.LockN65.JetEq" if i == "KAM.SpinOrbit.Data.CsegJetEq" else i for i in imports]
    return t.split("\n"), imports


DKNS = "KAM.SpinOrbit.Data.LockN65.DK"
_DKOP = re.compile(r"^\((dkAngleModel|dkActionModel) 2 base\.emb base\.weight base\.piEnc (\d) (\d)\)\.poly$")
_DKREF = re.compile(r"\block_dk([ap])(\d)(\d)\b")


def _tac(text):
    """a wrapped tactic line: first line at column 2, continuations at column 4"""
    ls = wrap(text.strip().split(" "), "    ")
    ls[0] = "  " + ls[0].lstrip()
    return ls


def _tors_base(self, body, imports, ns):
    """`Tors/Base`: `dkModels` from the DK literals (`DK/Mat`), and `dkwModels` entry by entry (`Tors/DKW{i}{j}`,
    one kernel run each); the whole module (8 DK + 16 second-derivative models) cannot run under 10 GB."""
    t = "\n".join(body)
    old_dk = "theorem lock_dk : dkModels 2 base.emb base.weight base.piEnc = lockTL :=\n  eq_of_matBeqCseg (by decide +kernel)"
    assert old_dk in t, "Tors/Base: dk theorem form changed"
    # the Boolean comparisons as named theorems (an inline `exact eq_of_matBeqCseg (by decide +kernel)` timed out at
    # isDefEq with the default heartbeats, measured on Tors.Base)
    lits = ("[[lockDKa00, lockDKa01], [lockDKa10, lockDKa11], [lockDKp00, lockDKp01], [lockDKp10, lockDKp11]]")
    t = t.replace(old_dk, "\n".join(["theorem lock_dk_beq :"] + wrap(("matBeqCseg %s lockTL = true := by" % lits)
                                                                    .split(" "), "    ") +
                                     ["  decide +kernel", "",
                                      "theorem lock_dk : dkModels 2 base.emb base.weight base.piEnc = lockTL := by",
                                      "  rw [lock_dkMat]", "  exact eq_of_matBeqCseg lock_dk_beq"]))
    old_w = ("theorem lock_dkw :\n    dkwModels 2 base.emb base.freqBox base.params.s base.weight base.cfgLow base.piEnc = "
             "lockTDL :=\n  eq_of_matBeqCseg (by decide +kernel)")
    assert old_w in t, "Tors/Base: dkw theorem form changed"
    ent = lambda i, j: ("CertModel.toDeg base.weight base.piEnc 0 (modelSum base.weight base.piEnc (List.ofFn fun l : "
                        "Fin 2 => CertModel.mul base.weight base.cfgLow [4, 10, %d, %d, l.val] (freqModel 2 base.freqBox "
                        "base.params.s l.val) (d2kModel 2 base.emb base.weight base.piEnc %d %d l.val)))" % (i, j, i, j))
    mods = []
    for i in range(4):
        for j in range(2):
            st = "%s = modelMatrixEntry lockTDL %d %d :=" % (ent(i, j), i, j)
            mods.append(_tree_write(self, "Tors/DKW%d%d" % (i, j), imports, "Torsion input: dkw entry (%d, %d)" % (i, j),
                                    "One kernel run: one entry of `dkwModels` equals the literal's entry.",
                                    ["theorem lock_dkw%d%d :" % (i, j)] + wrap(st.split(" "), "    ") +
                                    ["  CertModel.eq_of_segBeq (by decide +kernel)"], heavy=True, ns=ns))
    explicit = "[" + ", ".join("[" + ", ".join(ent(i, j) for j in range(2)) + "]" for i in range(4)) + "]"
    new_w = ["theorem lock_dkw :",
             "    dkwModels 2 base.emb base.freqBox base.params.s base.weight base.cfgLow base.piEnc = lockTDL := by"]
    new_w += _tac("rw [show dkwModels 2 base.emb base.freqBox base.params.s base.weight base.cfgLow base.piEnc = %s"
                  " from rfl]" % explicit)
    new_w += _tac("rw [" + ", ".join("lock_dkw%d%d" % (i, j) for i in range(4) for j in range(2)) + "]")
    new_w += ["  exact eq_of_matBeqCseg lock_dkw_beq"]
    ents = "[" + ", ".join("[" + ", ".join("modelMatrixEntry lockTDL %d %d" % (i, j) for j in range(2)) + "]"
                           for i in range(4)) + "]"
    beq_w = ["theorem lock_dkw_beq :"] + wrap(("matBeqCseg %s lockTDL = true := by" % ents).split(" "), "    ") + \
        ["  decide +kernel", ""]
    t = t.replace(old_w, "\n".join(beq_w + new_w))
    return t.split("\n"), list(imports) + mods + [DKNS + ".Mat"]


ADVLOOKUP = "KAM.SpinOrbit.Data.LockN65.AdvLookup"
FALLBACKMUL = "KAM.SpinOrbit.Data.LockN65.FallbackMul"
ADV_BLOCK = 200          # entries per chunk of the advice books (advFull.b*, advLow.b*)
LOW_B6 = 1082            # first index of advLow.b6 (chunks b0-b4 of 200, b5 of 82 entries)
HK_MIN = 150             # from this book index on, `hk` goes by chunks (entry 966 hit the recursion limit; 203 passed)
HKFIXED = []


def _arg_spans(t, i, n):
    """the spans of the next n arguments of an application starting at t[i] (balanced brackets)"""
    out, opens, closes = [], "([⟨{", ")]⟩}"
    while len(out) < n:
        while t[i].isspace():
            i += 1
        j, depth = i, 0
        while True:
            c = t[j]
            if c in opens:
                depth += 1
            elif c in closes:
                if depth == 0:
                    break
                depth -= 1
            elif c.isspace() and depth == 0:
                break
            j += 1
        out.append((i, j))
        i = j
    return out


def _fix_hk(text):
    """`polyProduct_eq_of_mulPacked … hk …` with `hk := rfl` at a deep book index: the lookup by chunks
    (AdvLookup.lean)"""
    pos, changed = 0, False
    while True:
        i = text.find("polyProduct_eq_of_mulPacked", pos)
        if i < 0:
            break
        spans = _arg_spans(text, i + len("polyProduct_eq_of_mulPacked"), 14)
        arg = lambda q: text[spans[q][0]:spans[q][1]]
        pos = spans[-1][1]
        m = re.match(r"^(adv(Full|Low))\.p(\d+)\.rr$", arg(6))
        if arg(13) != "rfl" or not m:
            continue
        book, idx = m.group(1), int(m.group(3))
        if idx < HK_MIN:
            continue
        key, adv = arg(2), m.group(1) + ".p%d" % idx
        lit = "[" + ", ".join(str(x) for x in ADVKEY[adv + ".rr"][1]) + "]"
        blk, loc = idx // ADV_BLOCK, idx % ADV_BLOCK
        if book == "advLow" and idx >= LOW_B6:
            blk, loc = 6, idx - LOW_B6          # advLow.b6: the SOS-square advice (AdvLowSOS.lean)
        a = "(.packed 112 %s.rr %s.ii %s.ri %s.ir)" % (adv, adv, adv, adv)
        term = ("(adviceLookup_at_cseg %s.b%d _ %s %d %s %s (by decide +kernel) rfl (by decide +kernel))"
                % (book, blk, key, loc, lit, a))
        for b_ in reversed(range(blk)):
            term = "((adviceLookup_skip_cseg %s.b%d _ %s (by decide +kernel)).trans %s)" % (book, b_, key, term)
        term = "((congrArg (fun b => adviceLookup b %s) lock_%s_blocks).trans %s)" % (key, book, term)
        text = text[:spans[13][0]] + term + text[spans[13][1]:]
        pos = spans[13][0] + len(term)
        changed = True
        HKFIXED.append(adv)
    return text, changed


def _write_sharded(self, rel, imports, title, doc, body, heavy=False, ns=None):
    """`Tree.write` with the one-theorem shard modules cut into SH_GROUP-shard theorems (each its own module; `rel`
    becomes a facade), and the products' `checkPackedSp_of_groups` calls given the matching groups."""
    body, imports = _lock_jet_names(body, imports)
    if rel.startswith("Prod/M"):
        t_, ch_ = _fix_hk("\n".join(body))
        if ch_:
            body, imports = t_.split("\n"), list(imports) + [ADVLOOKUP]
    if rel == "Tors/Base":
        body, imports = _tors_base(self, body, imports, ns)
    if rel.startswith("Gram/"):
        refs = sorted(set(_DKREF.findall("\n".join(body))))
        imports = list(imports) + ["%s.%s%s%s" % (DKNS, k.upper(), i, j) for k, i, j in refs]
        if re.match(r"^Gram/E\d\d$", rel):
            xs = sorted(set(re.findall(r"\block_GE(\d\d)X(\d)\b", "\n".join(body))))
            imports = list(imports) + [self.mod("Gram/E%sX%s" % x) for x in xs]
    joined = " ".join(l.strip() for l in body if l.strip() and l.strip() != "decide +kernel")
    m = _SH.match(joined)
    if m and rel.endswith("Sh") and body[-1].strip() == "decide +kernel":
        nm, adv, rest = m.groups()
        ops = _ops_module(self, rel, nm, adv, rest, imports, ns) if adv in HEAVYADV else None
        if ops is not None:
            ea_t, eb_t, nea, neb, omod = ops
            rest = "(checkShardAt %s %s %s)" % (adv, nea, neb)
            imports = list(imports) + [omod]
        mods = []
        for gi, g in enumerate(_groups(NSHARDS[adv], adv)):
            st = "[%s].all %s = true := by" % (", ".join(map(str, g)), rest)
            gb = ["theorem %sG%d :" % (nm, gi)] + wrap(st.split(" "), "    ") + ["  decide +kernel"]
            gt = "%s, shards %s" % (title, g)
            if len(gt) > 84:          # a light product's single group lists every shard: name the range instead
                gt = "%s, shards %d to %d" % (title, g[0], g[-1]) if g == list(range(g[0], g[-1] + 1)) else \
                    "%s, %d shards" % (title, len(g))
            mods.append(_tree_write(self, "%sG%d" % (rel, gi), imports, gt, doc, gb,
                                    heavy=heavy, ns=ns))
        return _tree_write(self, rel, mods, title, doc + " (facade over the shard-group modules)", [], ns=ns)
    if rel.startswith("Full/") or rel.startswith("Low/"):
        body, imports = _seg_lookups(body, imports)
    if self.mod(rel) in PRODSTMT:
        body = _orig_stmt(body, *PRODSTMT[self.mod(rel)])
        # the side checks `…A<n>` (each a `decide` over the operands, ~4 GB each on M1) one module each, so the
        # product module itself only assembles (the whole M1 module was OOM-killed at 6 GB, measured)
        ops = [OPSNAMES[a][4] for a in OPSNAMES if OPSNAMES[a][2].startswith(PRODSTMT[self.mod(rel)][0] + "_")]
        split = SPLIT_AUX                        # every product: side checks one module each (M1900 joined: 952 s CPU)
        body, amods = _split_aux(self, rel, body, imports, ns, split)
        imports = list(imports) + amods
        if not split:
            imports += ops
    if rel.endswith("Dec"):
        md = _DEC.match(" ".join(" ".join(body).split()))
        if md and md.group(3) in HEAVYADV:
            return _write_dec(self, rel, imports, title, doc, md, heavy, ns)
    text = "\n".join(body)

    pre = []

    def sub(mm):
        ind, adv, eaeb, hpre, nm = mm.group(1), mm.group(2), " ".join(mm.group(3).split()), mm.group(5), mm.group(6)
        n = NSHARDS[adv]
        hg = "(fun _ h => nomatch h)"
        for gi in reversed(range(len(_groups(n, adv)))):
            hg = "(List.forall_mem_cons.2 ⟨%sG%d, %s⟩)" % (nm, gi, hg)
        # the coverage and the group facts as theorems of their own (inline, the elaborator unfolds the shard
        # check: maximum recursion depth, measured)
        G = _group_lit(n, adv)
        pre.extend(["theorem %s_cover :" % nm] + wrap(("∀ s ∈ %s.shardRange, ∃ g ∈ %s, s ∈ g := by" % (adv, G)
                                                        ).split(" "), "    ") + ["  decide +kernel", ""])
        ea, eb = _split2(eaeb)
        if adv in OPSNAMES:
            _, _, nea, neb, _ = OPSNAMES[adv]
            pre.extend(["theorem %s_groups :" % nm] + wrap(("∀ g ∈ %s, g.all (checkShardAt %s %s %s) = true :="
                                                             % (G, adv, nea, neb)).split(" "), "    ")
                       + wrap(hg.split(" "), "  ") + [""])
            # the prefix and the goal rewritten from the operand terms to their literals (computed once, in the
            # operand module), then the grouped check against the literals
            # term mode (no `rw`): rewriting `la.slotTerms X` let the pattern search try it against
            # `lb.slotTerms Y` and unfold the operands (heartbeat timeout at isDefEq, M725MP part ri)
            t = ("(congrArg₂ (checkPackedSp %s) %s_eq %s_eq).trans (checkPackedSp_of_groups %s %s %s %s %s"
                 " %s_cover %s_groups)" % (adv, nea, neb, adv, nea, neb, G, hpre, nm, nm))
            ls = wrap(t.split(" "), ind + "    ")
            ls[0] = ind + ls[0].lstrip()
            return "\n".join(ls)
        pre.extend(["theorem %s_groups :" % nm] + wrap(("∀ g ∈ %s, g.all (checkShardAt %s %s %s) = true :="
                                                         % (G, adv, ea, eb)).split(" "), "    ")
                   + wrap(hg.split(" "), "  ") + [""])
        ls = wrap(("checkPackedSp_of_groups %s %s %s %s %s_cover %s_groups"
                   % (adv, eaeb, G, hpre, nm, nm)).split(" "), ind + "    ")
        ls[0] = ind + ls[0].lstrip()
        return "\n".join(ls)
    text, nsub = _GRP.subn(sub, text)
    if nsub:
        out = text.split("\n")
        # the new theorems go before the theorem that uses them
        c = next(i for i, l in enumerate(out) if "checkPackedSp_of_groups" in l)
        k = max(i for i in range(c) if out[i].startswith("theorem "))
        out = out[:k] + pre + out[k:]
    else:
        out = body
    return _tree_write(self, rel, imports, title, doc, out, heavy=heavy, ns=ns)


OPSNAMES = {}             # advice name -> (ea text, eb text, ea name, eb name, operand module)
EAEB = {}                 # (chain, full key) -> {part: (ea, eb)}  (lock_eaeb.py)
ADVKEY = {}               # advice name -> (chain, full key, part)


def _load_eaeb(path):
    if not os.path.exists(path):
        return
    with open(path, "rb") as f:
        while True:
            try:
                k, rec = pickle.load(f)
            except EOFError:
                return
            EAEB[(k[0], tuple(k[1]))] = rec


PAIR_LINES = 1000          # hex lines per literal chunk definition


def _pairs_items(name, xs):
    """`name := name.c0 ++ …`, each chunk `pairsOf (zdecs […])` of whole pairs (data items for `Tree.data`)"""
    cs = LZ.chunks([int(v) for s_, v_ in xs for v in (s_, v_)])
    groups, cur, cnt = [], [], 0
    for n, b in cs:
        cur.append((n, b))
        cnt += n
        if len(cur) >= PAIR_LINES and cnt % 2 == 0:
            groups.append(cur)
            cur, cnt = [], 0
    if cur:
        groups.append(cur)
    items, names = [], []
    for gi, g in enumerate(groups):
        cn = "%s.c%d" % (name, gi)
        ls = ["def %s : List (ℕ × ℤ) := pairsOf (zdecs [" % cn]
        for i, (n, b) in enumerate(g):
            ls.append("  (%d, 0x%x)" % (n, int.from_bytes(b, "little")) + ("," if i + 1 < len(g) else "])"))
        items.append((cn, ls + [""]))
        names.append(cn)
    if not names:
        names = ["([] : List (ℕ × ℤ))"]
    items.append((name, ["def %s : List (ℕ × ℤ) :=" % name] + wrap(" ++ ".join(names).split(" "), "  ") + [""]))
    return items


def _ops_module(self, rel, nm, adv, rest, imports, ns):
    """the operand slot terms `ea`, `eb` of one product part as literals, each proved equal to its expression
    (one kernel run each, computed once); None when the data are missing"""
    key = ADVKEY.get(adv)
    rec = EAEB.get(key[:2]) if key else None
    if not rec or key[2] not in rec:
        return None
    ea_l, eb_l = rec[key[2]]
    inner = rest[len("(checkShardAt %s " % adv):-1]
    ea_t, eb_t = _split2(inner)
    nea = "%sEA" % nm
    neb = nea if (eb_t == ea_t.replace(".la.", ".lb.") and False) else "%sEB" % nm
    data = self.data(rel + "OpsD", "Operand slot terms of %s (data)" % adv,
                     "Literals (`pairsOf` over `zdecs`).", _pairs_items(nea, ea_l) + _pairs_items(neb, eb_l),
                     list(imports) + [PAIRCODE])
    body = []
    for n_, t_ in ((nea, ea_t), (neb, eb_t)):
        body += ["theorem %s_eq :" % n_] + wrap(("%s = %s := by" % (t_, n_)).split(" "), "    ") + \
            ["  decide +kernel", ""]
    omod = _tree_write(self, rel + "Ops", list(imports) + [PAIRCODE] + data[-1:], "Operand slot terms of %s" % adv,
                       "Computed once (`decide`); the shard checks use the literals.", body, heavy=True, ns=ns)
    OPSNAMES[adv] = (ea_t, eb_t, nea, neb, omod)
    return OPSNAMES[adv]


SEGDECIDE = "KAM.SpinOrbit.Data.LockN65.SegDecide"
_RFL3 = re.compile(r"rfl\s+rfl\s+rfl\s+\(by\s+decide\s+\+kernel\)")


def _seg_lookups(body, imports):
    """segment proofs: the spec and metadata as `C.segs[j]?.getD d`, `C.metas[j]?.getD d`, with `hs`/`hm` from
    `eq_some_getD_cseg` and `hone` by kernel evaluation (the elaborator `rfl`s recurse once per list cell and
    exceed the default depth past index ~80 of the chunked plan lists, measured on Full.S88)"""
    t = "\n".join(body)
    if not _RFL3.search(t):
        return body, imports
    t = re.sub(r"\((\w+)Segs\.getD(\s+)(\d+) ", r"(\1.segs[\3]?.getD\2", t)
    t = re.sub(r"\((\w+)Metas\.getD(\s+)(\d+) ", r"(\1.metas[\3]?.getD\2", t)
    t = _RFL3.sub("(eq_some_getD_cseg _ (by decide +kernel)) (eq_some_getD_cseg _ (by decide +kernel))\n"
                  "      (by decide +kernel) (by decide +kernel)", t)
    return t.split("\n"), list(imports) + [SEGDECIDE]


def _split_aux(self, rel, body, imports, ns, split):
    lines = "\n".join(body).split("\n")
    blocks, cur = [], []
    for l in lines:
        if l.startswith("theorem ") and cur:
            blocks.append(cur)
            cur = []
        cur.append(l)
    blocks.append(cur)
    keep, mods = [], []
    for b in blocks:
        m = re.match(r"^theorem (\S+A\d+) :", b[0])
        if m and not split:
            # D55: kept in the product module; the prefix check stated on the operand literals (0.6 GB, measured)
            pm = re.search(r"checkPackedSpPrefix (\S+) ", " ".join(b))
            if pm and pm.group(1) in OPSNAMES:
                ea_t, eb_t, nea, neb, _ = OPSNAMES[pm.group(1)]
                tail = []
                while b and (b[-1].strip() == "" or b[-1].lstrip().startswith("/--")):
                    tail.insert(0, b[-1])
                    b = b[:-1]
                st = " ".join(" ".join(b[1:-1]).split()).replace(ea_t, nea).replace(eb_t, neb)
                b = [b[0]] + wrap(st.split(" "), "    ") + [b[-1]] + tail
            keep.extend(b)
            continue
        if m and b[0].startswith("theorem "):
            tail = []
            while b and (b[-1].strip() == "" or b[-1].lstrip().startswith("/--")):
                tail.insert(0, b[-1])
                b = b[:-1]
            pm = re.search(r"checkPackedSpPrefix (\S+) ", " ".join(b))
            if pm and pm.group(1) in OPSNAMES:
                adv = pm.group(1)
                ea_t, eb_t, nea, neb, omod = OPSNAMES[adv]
                st = " ".join(" ".join(b[1:-1]).split()).replace(ea_t, nea).replace(eb_t, neb)
                # the eight conjuncts one module each (together 6.20 GB on M1, measured), assembled by `simp only`
                cj = ["%s.shapeOK" % adv, "decide (0 < %s.la.denseLen)" % adv, "decide (0 < %s.lb.denseLen)" % adv,
                      "packStrictAsc %s" % nea, "packStrictAsc %s" % neb,
                      "(%s.all fun e => decide (e.1 < %s.la.denseLen))" % (nea, adv),
                      "(%s.all fun e => decide (e.1 < %s.lb.denseLen))" % (neb, adv),
                      "(%s.rounded.length == %s.spCount %s.la.denseLen + %s.spCount %s.lb.denseLen - 1)"
                      % (adv, adv, adv, adv, adv)]
                base_nm = m.group(1)
                cmods = []
                for ci, c in enumerate(cj):
                    cb = ["theorem %s_c%d :" % (base_nm, ci)] + wrap(("%s = true := by" % c).split(" "), "    ") + \
                        ["  decide +kernel"]
                    cmods.append(_tree_write(self, "%sAux%sC%d" % (rel, base_nm.rsplit("A", 1)[1], ci),
                                             list(imports) + [omod], "Prefix conjunct %d of %s" % (ci, adv),
                                             "One kernel run.", cb, heavy=True, ns=ns))
                b = [b[0]] + wrap(st.replace(" := by", " := by").split(" "), "    ")
                b += _hang("simp only [checkPackedSpPrefix, %s, Bool.and_self, Bool.and_true]"
                           % ", ".join("%s_c%d" % (base_nm, ci) for ci in range(len(cj))))
                imports_b = list(imports) + [omod] + cmods
            else:
                imports_b = imports
            mods.append(_tree_write(self, "%sAux%s" % (rel, m.group(1).rsplit("A", 1)[1]), imports_b,
                                    "Side check %s" % m.group(1), "One kernel run.", b, heavy=True, ns=ns))
            keep.extend([""] + tail)
        else:
            keep.extend(b)
    return keep, mods


def _orig_stmt(body, nm, ops, rems=()):
    """the product theorem `nm` stated with the original operand terms (what its consumers state), proved by
    rewriting them to the named operands (`…_eq`, syntactic) and the proof against the names."""
    lines = "\n".join(body).split("\n")
    i = lines.index("theorem %s :" % nm)
    j = next(t for t in range(i, len(lines)) if lines[t].rstrip().endswith(":="))
    stmt = " ".join(" ".join(lines[i + 1:j + 1]).split())[:-2].strip()
    for t, n in ops:
        stmt = re.sub(r"(?<![\w.])%s(?![\w.])" % re.escape(n), "(%s)" % t, stmt)
    for _, _, lit, term in rems:
        stmt = stmt.replace(term, "(%s)" % lit)
    proof = lines[j + 1:]
    end = next((t for t, l in enumerate(proof) if l.strip() == ""), len(proof))
    # the operand bridges longest operand first: an operand inside another (sosLoPoly in sosLoPoly.conjSorted) is
    # rewritten after it (the other order leaves `lockM{k}a.conjSorted`, M2016)
    rw = "rw [%s]" % ", ".join(["← %s" % r[1] for r in rems] +
                               ["%s_eq" % n for _, n in sorted(ops, key=lambda tn: -len(tn[0]))])
    new = (["theorem %s :" % nm] + wrap((stmt + " := by").split(" "), "    ") + ["  " + rw]
           + ["  exact" + proof[0][1:]] + ["  " + l for l in proof[1:end]] + proof[end:])
    return lines[:i] + new


def _write_dec(self, rel, imports, title, doc, md, heavy, ns):
    """a decode `dyadicTerms … targetTerms = some T` cut at the slots where the chunks `T.cK` of the memo begin
    (one kernel theorem per piece, DecSplit.lean)."""
    nm, P, adv, place, src, T = md.groups()
    po = ADVOBJ[adv]
    nz = [i for i, c in enumerate(SP.combined(po)) if c != 0]
    n = SP.prodLen(po)
    nch = max(1, -(-len(nz) // TERMS_PER_DEF))
    cuts = [0] + [nz[TERMS_PER_DEF * j] for j in range(1, nch)] + [n]
    mods, hs = [], []
    for j in range(nch):
        st = ("dyadicTerms (2 * %s) %s.scale %s (pieceAt %s.targetEntry %s.combined %d %d) = some %s.c%d :="
              % (P, adv, place, adv, adv, cuts[j], cuts[j + 1], T, j))
        pb = ["theorem %s_decP%d :" % (nm, j)] + wrap(st.split(" "), "    ") + \
            ["  eq_some_of_termsBeq_cseg (by decide +kernel)"]
        mods.append(_tree_write(self, "%sP%d" % (rel, j), imports + [DECSPLIT], "%s, piece %d" % (title, j), doc, pb,
                                heavy=heavy, ns=ns))
        hs.append("%s_decP%d" % (nm, j))
    fa = ".nil"
    for h in reversed(hs):
        fa = "(.cons %s %s)" % (h, fa)

    def hang(text):
        """two-space first line, four-space continuation"""
        ls = wrap(text.split(" "), "    ")
        ls[0] = "  " + ls[0].lstrip()
        return ls
    Ts = ", ".join("%s.c%d" % (T, j) for j in range(nch))
    plc = "dyadicTerms (2 * %s) %s.scale %s" % (P, adv, place)
    # three steps, each a syntactic match for the elaborator (a direct `exact` against the pair form or against
    # `T` makes it unfold and evaluate `targetTerms`: maximum recursion depth, measured)
    body = ["theorem %s_decF :" % nm] + wrap(("List.Forall₂ (fun p X => %s (pieceAt %s.targetEntry %s.combined p.1 p.2) ="
                                              " some X) (cutPairs [%s]) [%s] :=" % (plc, adv, adv,
                                                                                    ", ".join(map(str, cuts)), Ts)
                                              ).split(" "), "    ") + hang(fa) + [""]
    body += ["theorem %s_decA :" % nm] + wrap(("%s %s.targetTerms = some (List.flatten [%s]) :=" % (plc, adv, Ts)
                                              ).split(" "), "    ")
    body += hang("dyadicTerms_targetTerms_of_pieces (2 * %s) %s.scale %s %s [%s] (by decide +kernel) (by decide"
                 " +kernel) %s_decF" % (P, adv, place, adv, ", ".join(map(str, cuts[1:])), nm))
    body += ["", "theorem %s_dec :" % nm] + wrap(("%s %s = some %s := by" % (plc, src, T)).split(" "), "    ")
    body += hang("rw [fst_targetPair, show %s = List.flatten [%s] from rfl]" % (T, Ts))
    body += ["  exact %s_decA" % nm]
    return _tree_write(self, rel, mods + [DECSPLIT], title, doc, body, heavy=False, ns=ns)


_tree_write = CE.Tree.write
CE.Tree.write = _write_sharded


def _split_items(items):
    """items whose lines exceed the file budget, cut at every blank line between definitions (`data` re-packs
    them) into pieces under the same name (the files chain-import, so the last piece's module brings every earlier piece)."""
    for nm, lines in items:
        if len(lines) <= CE.MAXLINES:
            yield nm, lines
            continue
        cur = []
        for l in lines:
            cur.append(l)
            if l == "":
                yield nm, cur
                cur = []
        if cur:
            yield nm, cur


_tree_data = CE.Tree.data
CE.Tree.data = lambda self, stem, title, doc, items, imports: _tree_data(self, stem, title, doc,
                                                                         list(_split_items(items)), imports)


def data_flat(tree, stem, title, doc, items, imports, needs=None):
    """`Tree.data` without the chain: file `stem NN` imports `imports`, the modules `needs(name)` of its items, and
    only those earlier files holding earlier pieces of one of its own split items (`_split_items`), so the parts
    elaborate in parallel; returns every part (a consumer imports all of them)."""
    files, cur, n, imp = [], [], 0, set()
    for nm, lines in _split_items(items):
        new = set(needs(nm)) if needs else set()
        # each import is one header line: the file stays under the line cap with its imports
        if cur and n + len(lines) + len(imp | new) > CE.MAXLINES:
            files.append(cur)
            cur, n, imp = [], 0, set()
        cur.append((nm, lines))
        n += len(lines)
        imp |= new
    if cur:
        files.append(cur)
    mods, where = [], {}
    for fi, f in enumerate(files):
        rel = "%s%02d" % (stem, fi)
        own = sorted({where[nm] for nm, _ in f if nm in where})
        extra = sorted({m for nm, _ in f for m in (needs(nm) if needs else [])})
        m = tree.write(rel, list(imports) + own + extra, "%s, part %d" % (title, fi), doc,
                       [l for _, ls in f for l in ls])
        for nm, _ in f:
            tree.defs[nm] = m
            where[nm] = m
        mods.append(m)
    return mods


class LockEmitter(CE.Emitter):
    def __init__(self, gdir, plan, led, fall, root, slots=None):
        import sofx_gen as G
        g = pickle.load(open(os.path.join(gdir, "gen.pkl"), "rb"))
        self.w, self.t, self.T = "lock", "lock", "LockN65"
        self.plan, self.led, self.fall = plan, led, fall
        self.adv = {bk: [(list(k), G.adv_json(a)) for k, a in g["books"][bk]] for bk in ("cfgFull", "cfgLow")}
        for bk, bn in (("cfgFull", "advFull"), ("cfgLow", "advLow")):
            for i, (_, a) in enumerate(self.adv[bk]):
                if a[0] != "direct":
                    for part, pa in zip(("rr", "ii", "ri", "ir"), a[2:]):
                        NSHARDS["%s.p%d.%s" % (bn, i, part)] = len(pa["rounded"])
                    for part, po in zip(("rr", "ii", "ri", "ir"), g["books"][bk][i][1][2:]):
                        ADVOBJ["%s.p%d.%s" % (bn, i, part)] = po
                        ADVKEY["%s.p%d.%s" % (bn, i, part)] = (bk, tuple(g["books"][bk][i][0]), part)
        self.cert = None
        self.tree = CE.Tree(root, self.T)
        self.base = ["KAM.SpinOrbit.Data.LockN65.Cert", "KAM.SpinOrbit.Data.LockN65.SegSupport",
                     "KAM.SpinOrbit.Data.LockN65.SegRoutes", "KAM.SpinOrbit.Data.LockN65.Jet",
                     "KAM.SpinOrbit.Data.LockN65.ZRows"]
        self.W = "base.weight"
        self.pe = "base.piEnc"
        self.slots = slots
        self.charWit = None

    # ------------------------------------------------------------------ names
    def seg_stmt(self, chain, j):
        return ("%s.segOk 2 lockJetLit.prog.ops base.emb base.wit %s %s %s %d = true"
                % (self.ck(chain), self.W, self.cfgOf(chain), self.pe, j))

    def book(self, cfg):
        return self.adv["cfgFull" if cfg == "cfgFull" else "cfgLow"]

    # ------------------------------------------------------------------ character witnesses (the lock has several)
    def set_char_wit(self, charWit):
        """the mirror's `c.wit.charWit`: [(key, (poly, halvings, order))]."""
        self.charWit = [(tuple(k), [((int(a[0]), int(a[1])), (int(z[0]), int(z[1]))) for a, z in P])
                        for k, (P, _h, _o) in charWit]

    def char_term(self, c):
        return "(base.wit.charWit.getD %d %s).2.poly" % (c, CHD)

    def meta_lit(self, chain, b):
        L, nE, nI, cache = self.led["chains"][chain]["metas"][b]
        ents = []
        for k, (poly, r) in cache:
            poly = [(tuple(a), tuple(z)) for a, z in poly]
            pt = None
            for c, (_k, E) in enumerate(self.charWit):
                if poly == E:
                    pt = self.char_term(c)
                elif poly == self.reflected(E):
                    pt = "%s.reflectSorted" % self.char_term(c)
                if pt:
                    break
            if pt is None:
                raise SystemExit("cache polynomial is no character witness nor its reflection")
            ents.append("(%s, %s, %s)" % (nat_list(k), pt, fixed(r)))
        return "⟨%d, %d, %d, [%s]⟩" % (L, nE, nI, ", ".join(ents))

    def charE(self):
        return self.charWit[self.led["char"]["cfgFull"]["cidx"]][1]

    # ------------------------------------------------------------------ the fallible slots' terms
    def slot_model(self, chain, a):
        return "(%s.slotPair %s %d).1" % (self.ck(chain), self.W, a)

    def g_exp(self, chain, a):
        return "(CertModel.toDeg %s %s 0 %s)" % (self.W, self.pe, self.slot_model(chain, a))

    def exp_wit(self, k):
        return "(base.wit.expWit[%d]?.getD %s)" % (k, EXPD)

    def inv_wit(self, k):
        return "(base.wit.invWit[%d]?.getD %s)" % (k, INVD)

    def sqrt_wit(self, slot):
        return "((base.wit.sqrtWit.find? fun e => e.1 == %d).getD %s).2" % (slot, SQD)

    def cfgw(self, chain, s, i):
        return "(%s.forWitness %d %d)" % (self.cfgOf(chain), s, i)

    # ------------------------------------------------------------------ operands of every memo
    def operands(self):
        out = {}
        for k, m in enumerate(self.led["memos"]):
            ctx, fk = m["ctx"], tuple(m["fullKey"])
            if not ctx.startswith("cfg") or fk[0] == 0 or (fk[0] == 1 and fk[1] >= len(self.exp_slots())):
                continue
            chain = ctx.split("/")[0]
            slot = int(ctx.split("slot")[1])
            if self.slots is not None and slot not in self.slots:
                continue
            v = self.fall[chain][slot]
            pm = [self.plan_mods[chain]]
            if fk[0] == 1:                            # exp residual [1, k, j]
                j = fk[2]
                g = self.g_exp(chain, v["a"])
                out[k] = (self.cfgw(chain, 1, v["k"]), "[1, %d]" % j,
                          "(itemsPoly (%s.poly.terms.filterMap (derivItem %d)))" % (g, j),
                          "%s.poly.negP" % self.exp_wit(v["k"]), pm)
            elif fk[0] == 2:                          # inverse product [2, k]
                out[k] = (self.cfgw(chain, 2, v["k"]), "[2]", self.inv_wit(v["k"]),
                          "%s.poly" % self.slot_model(chain, v["a"]), pm)
            elif fk[0] == 3:                          # square-root product [3, slot]
                S = self.sqrt_wit(v["slot"])
                out[k] = (self.cfgw(chain, 3, v["slot"]), "[3]", "%s.poly" % S, "%s.poly" % S, pm)
        if self.slots is None:
            # the lunar operands for the program products, the character residuals and the stages; the memos of
            # the fallible slots are hidden from it (an unevaluated slot: skipped there)
            nE = len(self.exp_slots())
            hide = {"ctx": "cfgFull/slot-1", "fullKey": [9]}
            led = self.led
            # only the chains' memos: the Gram memos [3, 0, a, b, r] / [3, 1, i, j, k] share the key head 3 with
            # the lock's square-root products and were hidden too (no Gram product was emitted; Gram.E00 OOM)
            self.led = dict(led, memos=[hide if (m["ctx"].startswith("cfg") and (
                tuple(m["fullKey"])[0] in (2, 3) or (tuple(m["fullKey"])[0] == 1 and m["fullKey"][1] < nE)))
                or m["ctx"].startswith("graph/") else m for m in led["memos"]])
            try:
                base = CE.Emitter.operands(self)
            finally:
                self.led = led
            for k, val in base.items():
                out.setdefault(k, val)
        # SOS option (a): the two SOS squares `g g*` under [7, 1] (pLo), [7, 2] (pHi) (memos from lock_sosk_memo.py)
        for k, m in enumerate(self.led["memos"]):
            if m["ctx"].startswith("graph/"):
                g_ = "sosLoPoly" if m["ctx"] == "graph/pLo" else "sosHiPoly"
                out[k] = ("base.cfgLow", "[%d, %d]" % tuple(m["fullKey"]), g_, "%s.conjSorted" % g_, [])
        # a memo with no output is a product whose packed advice fails its landed check: polyProduct is none and
        # mul takes the ball (the certificate was generated and checked so); no packed-route product proof for it
        # (MAG-FZ-2 cross-check: 11 such product modules were emitted before)
        return {k: v for k, v in out.items() if self.led["memos"][k].get("out") is not None}

    def exp_slots(self):
        return [i for i, o in enumerate(self.led_ops) if o[0] == "exp"]

    # ------------------------------------------------------------------ forced segments
    def op_lit(self, op):
        if op[0] in ("exp", "inv", "sqrt"):
            return "(.%s %d)" % (op[0], op[1])
        return CE.Emitter.op_lit(self, op)

    def forced_segment(self, chain, j, s, nm):
        i = s["start"]
        op = self.led_ops[i]
        if op[0] not in ("exp", "inv", "sqrt"):
            if self.slots is not None and i not in self.slots:
                return None
            if op[0] == "mul" and self.led["memos"][self.memo_index(chain, (0, i))].get("out") is None:
                return self.forced_mul_none(chain, j, s, nm)
            if op[0] == "mul":
                body = self.forced_mul(chain, j, s, nm)
                if body is not None:
                    return body
            return CE.Emitter.forced_segment(self, chain, j, s, nm)
        if self.slots is not None and i not in self.slots:
            return None
        C, W, cfg, pe = self.ck(chain), self.W, self.cfgOf(chain), self.pe
        spec = "(%sSegs.getD %d ⟨0, 0, [], [], []⟩)" % (C, j)
        meta = "(%sMetas.getD %d ⟨0, 0, 0, []⟩)" % (C, j)
        head = ["theorem %s :" % nm] + wrap(self.seg_stmt(chain, j).split(" "), "    ")
        head[-1] += " := by"
        common = ["  refine ComposeCkpt.segOk_one_of (s := %s)" % spec,
                  "    (m := %s)" % meta,
                  "    (op := %s) (st' := ?st) rfl rfl rfl (by decide +kernel) ?hop ?hres" % self.op_lit(op)]
        v = self.fall[chain][i]
        rad = self.emit_radius(chain, i, op, v)
        self.forced_imports[(chain, j)] = [rad]
        seed_rw = ("rw [seed_slot_of_mem %s %s %s (a := %d) (by decide +kernel) (by decide +kernel)]"
                   % (W, meta, C, op[1]))
        radn = "%s_%sRad%s%d" % (self.t, op[0], "F" if chain == "cfgFull" else "L", i)
        if op[0] == "exp":
            arm = ("composeStep_exp_eq 2 base.emb base.wit %s %s %s _ %d (E := %s) (r := %s)"
                   " (eq_some_getD_cseg %s (by decide +kernel))" % (W, cfg, pe, op[1], self.exp_wit(v["k"]),
                                                                    fixed(v["r"]), EXPD))
        elif op[0] == "inv":
            arm = ("composeStep_inv_eq 2 base.emb base.wit %s %s %s _ %d (Q := %s) (r := %s)"
                   " (eq_some_getD_cseg %s (by decide +kernel))" % (W, cfg, pe, op[1], self.inv_wit(v["k"]),
                                                                    fixed(v["r"]), INVD))
        else:
            arm = ("composeStep_sqrt_eq 2 base.emb base.wit %s %s %s _ %d (S := %s) (r := %s)"
                   " (eq_some_getD_cseg %s (by decide +kernel))" % (W, cfg, pe, op[1], self.sqrt_wit(v["slot"]).replace(
                       "fun e =>", "fun (e : ℕ × SqrtWitness %s) =>" % CE.TY),
                                                                    fixed(v["r"]), SQD))
        pf = ["  case hop =>",
              "    rw [shadowStep_of_live 2 base.emb base.wit %s %s %s (by decide +kernel)," % (W, cfg, pe)]
        # the radius goal: one tactic per line (an inline `(by …; exact …)` wraps left of its block's column)
        pf += wrap(arm.split(" "), "      ")
        sr = wrap(seed_rw.split(" "), "            ")
        sr[0] = "        " + sr[0].lstrip()
        pf += ["      (by"] + sr + ["        exact %s)]" % radn]
        pf += ["  case hres =>", "    decide +kernel"]
        return head + common + pf

    # ------------------------------------------------------------------ the radius theorems (one module per slot)
    def emit_radius(self, chain, i, op, v):
        W = self.W
        sub = "F" if chain == "cfgFull" else "L"
        t = self.t
        nm = "%s_%sRad%s%d" % (t, op[0], sub, i)
        memos = {tuple(m["fullKey"]): k for k, m in enumerate(self.led["memos"])
                 if m["ctx"] == "%s/slot%d" % (chain, i)}
        imps = [self.plan_mods[chain]] + [self.prod_done[k] for k in memos.values()]
        body = []
        if op[0] == "exp":
            k = v["k"]
            cw, g, E = self.cfgw(chain, 1, k), self.g_exp(chain, v["a"]), self.exp_wit(k)
            (cre, cim), crad = v["out"]
            out = "((⟨%s, %s⟩ : CC %s), %s)" % (fixed(cre), fixed(cim), TY, fixed(crad))
            # each residual its own module (one kernel run each; together 6.22 GB, measured)
            rmods = []
            for j in range(2):
                mk = memos[(1, k, j)]
                st = "expResidualUp %s %s %s.poly %s.poly (%s.poly.supNormUp %s) %d = %s" % (
                    W, cw, g, E, E, W, j, fixed(v["res"][j]))
                memo_rw = ("rw [expResidualProduct_eq_of_polyProduct %s %s %s.poly %s.poly %d %s]"
                           % (W, cw, g, E, j, self.memo_name(mk)))
                stem = "Rad/%s%s%dRes%d" % (op[0].capitalize(), sub, i, j)
                if not EXP_SPLIT:
                    rb = ["theorem %s_res%d :" % (nm, j)] + wrap(st.split(" "), "    ")
                    rb[-1] += " := by"
                    rb += ["  unfold expResidualUp"] + _hang(memo_rw) + ["  decide +kernel"]
                    rmods.append(self.tree.write(stem, self.base + imps, "The exp residual %d at slot %d (%s)"
                                                 % (j, i, chain), "One kernel run.",
                                                 [CE.Emitter.fix_long(l) for l in rb], heavy=True))
                    continue
                # the residual in two kernel runs (ExpSplit.lean): the weighted sum over the merged terms, and
                # the error radius of the derivative items of g (one run was 6.0 GiB, measured)
                ss = ("sumUp (fun t => weightTermUp %s t.1 (upAdd t.2.1.normUp t.2.2)) (mergeErrTerms (%s.poly.terms"
                      ".filterMap (derivItem %d)) (expResidualProduct %s %s %s.poly %s.poly %d).1) = %s := by"
                      % (W, E, j, W, cw, g, E, j, fixed(v["resS"][j])))
                sb = ["theorem %s_res%d_s :" % (nm, j)] + wrap(ss.split(" "), "    ") + _hang(memo_rw) + \
                    ["  decide +kernel"]
                sm = self.tree.write(stem + "S", self.base + imps, "The exp residual %d sum at slot %d (%s)" % (j, i, chain),
                                     "One kernel run.", [CE.Emitter.fix_long(l) for l in sb], heavy=True)
                rr = "errRadius %s (%s.poly.terms.filterMap (derivItem %d)) = %s := by" % (W, g, j, fixed(v["resErr"][j]))
                eb_ = ["theorem %s_res%d_r :" % (nm, j)] + wrap(rr.split(" "), "    ") + ["  decide +kernel"]
                em = self.tree.write(stem + "R", self.base + imps, "The exp residual %d error radius at slot %d (%s)"
                                     % (j, i, chain), "One kernel run.", [CE.Emitter.fix_long(l) for l in eb_],
                                     heavy=True)
                rb = ["theorem %s_res%d :" % (nm, j)] + wrap(st.split(" "), "    ")
                rb[-1] += " := by"
                rb += _hang("rw [expResidualUp_eq_of_parts %s %s %s.poly %s.poly _ %d %s_res%d_s %s_res%d_r]"
                            % (W, cw, g, E, j, nm, j, nm, j))
                rb += _hang(memo_rw) + ["  decide +kernel"]
                rmods.append(self.tree.write(stem, self.base + imps + [sm, em, EXPSPLIT],
                                             "The exp residual %d at slot %d (%s)" % (j, i, chain), "Assembly.",
                                             [CE.Emitter.fix_long(l) for l in rb], heavy=True))
            imps = list(imps) + rmods
            rs = "(fun j => if j = 0 then %s else %s)" % (fixed(v["res"][0]), fixed(v["res"][1]))
            st = "expWitnessRadius 2 %s %s %s %s = some %s" % (W, cw, g, E, fixed(v["r"]))
            body += ["theorem %s :" % nm] + wrap(st.split(" "), "    ")
            body[-1] += " := by"
            body += wrap(("rw [expWitnessRadius_eq_of_pin 2 %s %s %s %s (out := %s) "
                          "(eq_some_pair_cseg (by decide +kernel)),"
                          % (W, cw, g, E, out)).split(" "), "  ")
            body += wrap(("expWitnessRadiusOf_eq_of_residuals 2 %s %s %s %s.poly %s (mB := %s) (mη := %s) (rs := %s)"
                          " (by decide +kernel) (by decide +kernel)" % (W, cw, g, E, out, fixed(v["mB"]),
                                                                        fixed(v["mEta"]), rs)).split(" "), "    ")
            body += ["      (fun j => match j with",
                     "        | ⟨0, _⟩ => %s_res0" % nm, "        | ⟨1, _⟩ => %s_res1" % nm,
                     "        | ⟨j + 2, h⟩ => absurd h (by omega))]", "  decide +kernel", ""]
        elif op[0] == "inv":
            k = v["k"]
            cw, Q, b = self.cfgw(chain, 2, k), self.inv_wit(k), self.slot_model(chain, v["a"])
            mk = memos[(2, k)]
            st = "invWitnessRadius 2 %s %s %s %s = some %s" % (W, cw, b, Q, fixed(v["r"]))
            body += ["theorem %s :" % nm] + wrap(st.split(" "), "    ")
            body[-1] += " := by"
            body += wrap(("rw [invWitnessRadius_eq_of_delta 2 %s %s %s %s (δ := %s) (t := %s)"
                          % (W, cw, b, Q, fixed(v["delta"]), fixed(v["t"]))).split(" "), "  ")
            rw = wrap(("rw [mul_eq_of_polyProduct_cseg %s %s [2] ⟨0, %s, ofInt 0⟩ ⟨0, %s.poly, %s.rad⟩ %s]"
                       % (W, cw, Q, b, b, self.memo_name(mk))).split(" "), "          ")
            rw[0] = "      " + rw[0].lstrip()
            body += ["    (by"] + rw + ["      decide +kernel)"]
            body += ["    (by decide +kernel) (by decide +kernel)]", "  decide +kernel", ""]
        else:
            cw, g, S = self.cfgw(chain, 3, v["slot"]), self.g_exp(chain, v["a"]), self.sqrt_wit(v["slot"])
            mk = memos[(3, v["slot"])]
            St = S.replace("fun e =>", "fun (e : ℕ × SqrtWitness %s) =>" % CE.TY)
            # three kernel runs, each its own module (one run OOM-killed at 6 GB, measured): the side checks,
            # the residual bound, and the radius from both
            ok = ("(decide (0 ≤ %s.margin ∧ %s.margin < %s.anchor) && ble ((sqrtAnchorDiff 2 %s %s).supBound %s)"
                  " (ofRatDown %s.margin) && blt ((sqrtRadicandDiff 2 %s %s %s).supBound %s) (ofRatDown (%s.anchor *"
                  " %s.anchor))) = true" % (St, St, St, W, St, W, St, W, g, St, W, St, St))
            okb = ["theorem %s_ok :" % nm] + wrap((ok + " := by").split(" "), "    ") + ["  decide +kernel"]
            okm = self.tree.write("Rad/%s%s%dOk" % (op[0].capitalize(), sub, i), self.base + imps,
                                  "The sqrt witness side checks at slot %d (%s)" % (i, chain), "One kernel run.",
                                  [CE.Emitter.fix_long(l) for l in okb], heavy=True)
            rb = ["theorem %s_res :" % nm] + wrap(("(sqrtResidual 2 %s %s %s %s).supBound %s = %s := by"
                                                   % (W, cw, g, St, W, fixed(v["e"]))).split(" "), "    ")
            rb += ["  unfold sqrtResidual SqrtWitness.model"]
            # one tactic per line (a wrapped `…; decide` can put a tactic left of the block's column)
            rw = wrap(("rw [mul_eq_of_polyProduct_cseg %s %s [3] ⟨0, %s.poly, ofInt 0⟩ ⟨0, %s.poly, ofInt 0⟩ %s]"
                       % (W, cw, St, St, self.memo_name(mk))).split(" "), "      ")
            rw[0] = "  " + rw[0].lstrip()
            rb += rw + ["  decide +kernel"]
            resm = self.tree.write("Rad/%s%s%dRes" % (op[0].capitalize(), sub, i), self.base + imps,
                                   "The sqrt residual bound at slot %d (%s)" % (i, chain), "One kernel run.",
                                   [CE.Emitter.fix_long(l) for l in rb], heavy=True)
            imps = list(imps) + [okm, resm]
            st = "sqrtWitnessRadius 2 %s %s %s %s = some %s" % (W, cw, g, S, fixed(v["r"]))
            body += ["theorem %s :" % nm] + wrap(st.split(" "), "    ")
            body[-1] += " := by"
            body += _hang("rw [sqrtWitnessRadius_eq_of_residual 2 %s %s %s %s %s_ok %s_res]" % (W, cw, g, St, nm, nm))
            body += ["  decide +kernel", ""]
        return self.tree.write("Rad/%s%s%d" % (op[0].capitalize(), sub, i), self.base + imps,
                               "The %s witness radius at slot %d (%s)" % (op[0], i, chain),
                               "Memoized through the lock routes (`SegRoutes`); one kernel run.",
                               [CE.Emitter.fix_long(l) for l in body], heavy=True)

    # ------------------------------------------------------------------ B3 lever (c): products against the ledger
    def led_route(self, k):
        """(chain, slot, a, b) when memo k is a program product `[0, slot]` whose slot is in its chain's ledger (its
        output then needs no decoded literal), else None."""
        m = self.led["memos"][k]
        fk = tuple(m["fullKey"])
        if fk[0] != 0 or not m["ctx"].startswith("cfg") or os.environ.get("LOCK_LEDROUTE", "1") == "0":
            return None
        chain = m["ctx"].split("/")[0]
        slot = int(m["ctx"].split("slot")[1])
        if slot not in self.led["chains"][chain]["ledger"]:
            return None
        op = self.led_ops[slot]
        return chain, slot, op[1], op[2]

    def emit_product(self, k, m, cfg, key, a, b, imps):
        """the landed `emit_product` with its two operand polynomials named once (`Prod/M{k}Arg`): every statement of
        the product mentions two constants, so the elaborator never re-unfolds the operand lookups (a 7-fold inline
        operand made it hit the recursion and heartbeat limits, measured on M0)."""
        nm = self.memo_name(k)
        advname, P = self.advRef(m["cfg"], m["fullKey"])
        heavy = False
        for prt in m["parts"]:
            if not prt["empty"]:
                adv = "%s.%s" % (advname, prt["part"])
                rec = EAEB.get(ADVKEY[adv][:2], {}).get(prt["part"])
                if rec and len(rec[0]) * len(rec[1]) >= HEAVY_PAIRS:
                    HEAVYADV.add(adv)
                    heavy = True
        # every product names its operands once (Prod/M{k}Arg): the light products' landed inline form hit the
        # elaborator's maximum recursion depth (M1900, measured); light products keep the remainder bound inline
        ops = [("a", a)] + ([] if b == a else [("b", b)])
        body = []
        dkimps = []
        for s_, t in ops:
            # an operand that is a DK model is defined by its kernel-checked literal (DK/{A,P}ij): the shard checks
            # then never recompute the DK model (~3.9 GB each)
            mdk = _DKOP.match(t)
            tdef = t if not mdk else "lockDK%s%s%s.poly" % ("a" if mdk.group(1) == "dkAngleModel" else "p",
                                                             mdk.group(2), mdk.group(3))
            body += ["/-- Operand %s of the packed product %d. -/" % (s_, k), "def %s%s : CertPoly %s :=" % (nm, s_, CE.TY)]
            body += wrap(tdef.split(" "), "  ") + [""]
            if mdk:
                kk = ("a" if mdk.group(1) == "dkAngleModel" else "p", mdk.group(2), mdk.group(3))
                body += ["theorem %s%s_eq :" % (nm, s_)] + wrap(("%s = %s%s := by" % (t, nm, s_)).split(" "), "    ")
                body += ["  rw [lock_dk%s%s%s]" % kk, "  rfl", ""]
                dkimps.append("%s.%s%s%s" % (DKNS, kk[0].upper(), kk[1], kk[2]))
            else:
                body += ["theorem %s%s_eq :" % (nm, s_)] + wrap(("%s = %s%s := rfl" % (t, nm, s_)).split(" "),
                                                                  "    ") + [""]
        arg = self.tree.write("Prod/M%dArg" % k, self.base + list(imps) + dkimps, "Operands of the packed product %d" % k,
                              "The two operand polynomials, named once.", body)
        rems = []
        for prt in m["parts"]:
            adv_ = "%s.%s" % (advname, prt["part"])
            if not prt["empty"] and (heavy or len(SP.slotDegs(ADVOBJ[adv_])) >= REM_LIGHT_MIN):
                REMCLASS.add((k, adv_))
                rems.append(self.emit_rem(k, adv_, P, imps))
        PRODSTMT[self.tree.mod("Prod/M%d" % k)] = (nm, [(t, nm + s_) for s_, t in ops], rems)
        if self.part_terms(k, m) is not None:
            return self.emit_product_multi(k, m, cfg, key, nm + "a", nm + ("a" if b == a else "b"),
                                           list(imps) + [arg] + [r[0] for r in rems])
        return CE.Emitter.emit_product(self, k, m, cfg, key, nm + "a", nm + ("a" if b == a else "b"),
                                       list(imps) + [arg] + [r[0] for r in rems])

    def part_terms(self, k, m):
        """for a memo product with more than one nonempty part: its decoded output split by part (the mirror's
        mulPacked appends the parts' target terms in the order rr, ii, ri, ir); None for a single-part product"""
        ne = [p for p in CE.PART_ORDER if not {q["part"]: q for q in m["parts"]}[p]["empty"]]
        if len(ne) <= 1 or not m["out"]:
            return None
        advname, _ = self.advRef(m["cfg"], m["fullKey"])
        terms = list(m["out"][0])
        out, i = {}, 0
        for p in ne:
            n = len(SP.targetTerms(ADVOBJ["%s.%s" % (advname, p)]))
            out[p] = terms[i:i + n]
            i += n
        assert i == len(terms), (k, i, len(terms))
        return out

    def emit_product_multi(self, k, m, cfg, key, a, b, imps):
        """`csplit_emit.Emitter.emit_product` for a memo product with several nonempty parts (the SOS squares): per
        part its shards (`Prod/M{k}{P}Sh`), its decode (`Prod/M{k}{P}Dec`, against its own literal `…T{P}`), its
        sparse check and side checks; the product theorem takes the four literals (the landed form handles one)."""
        P, W = CE.P, self.W
        nm = self.memo_name(k)
        advname, Pm = self.advRef(m["cfg"], m["fullKey"])
        assert Pm == P
        parts = {q["part"]: q for q in m["parts"]}
        ne = [p for p in CE.PART_ORDER if not parts[p]["empty"]]
        imps = self.base + self.memo_data + list(imps)
        ma = "(%s.toMants %s.toMant %d)" % (a, cfg, P)
        mb = "(%s.toMants %s.toMant %d)" % (b, cfg, P)
        xy = dict(rr=(".1", ".1"), ii=(".2", ".2"), ri=(".1", ".2"), ir=(".2", ".1"))
        fpart = dict(rr="(fun v => ⟨v, ofInt 0⟩)", ii="(fun v => ⟨v, ofInt 0⟩)", ri="(fun v => ⟨ofInt 0, v⟩)",
                     ir="(fun v => ⟨ofInt 0, v⟩)")
        body, auxn, mods = [], [0], []

        def aux(stmt):
            nmA = "%sA%d" % (nm, auxn[0])
            auxn[0] += 1
            body.extend(["theorem %s :" % nmA] + wrap((stmt + " := by").split(" "), "    ") + ["  decide +kernel", ""])
            return nmA
        hparts, tparts, rems, tt = {}, {}, {}, {}
        for p in CE.PART_ORDER:
            advp = "%s.%s" % (advname, p)
            X = "((%s.getD ([], []))%s)" % (ma, xy[p][0])
            Y = "((%s.getD ([], []))%s)" % (mb, xy[p][1])
            if p in ne:
                tn = "%sT%s" % (nm, p.upper())
                ea = "(%s.la.slotTerms %s)" % (advp, X)
                eb = "(%s.lb.slotTerms %s)" % (advp, Y)
                sh = ["theorem %s_%s_shards :" % (nm, p)] + wrap(
                    ("%s.shardRange.all (checkShardAt %s %s %s) = true := by" % (advp, advp, ea, eb)).split(" "),
                    "    ") + ["  decide +kernel"]
                mods.append(self.tree.write("Prod/M%d%sSh" % (k, p.upper()), imps,
                                            "Packed product %d, part %s: shards" % (k, p),
                                            "The shard group of one packed real product (L1c (a)).", sh, heavy=True))
                pair = "(%s.targetTerms, %s.remainderBound %s (2 * %d)).1" % (advp, advp, W, P)
                src = "(%s)" % pair if p != "ii" else "((%s).map fun t => (t.1, -t.2))" % pair
                dec = ["theorem %s_%s_dec :" % (nm, p)] + wrap(("dyadicTerms (2 * %d) %s.scale %s %s = some %s :="
                                                               % (P, advp, fpart[p], src, tn)).split(" "), "    ")
                dec += ["  eq_some_of_termsBeq_cseg (by decide +kernel)"]
                mods.append(self.tree.write("Prod/M%d%sDec" % (k, p.upper()), imps,
                                            "Packed product %d, part %s: decode" % (k, p),
                                            "The decode of one packed real product (L1c (b)).", dec, heavy=True))
                hpre = aux("checkPackedSpPrefix %s %s %s = true" % (advp, ea, eb))
                body += ["theorem %s_%s_sp :" % (nm, p)] + wrap(("checkPackedSp %s %s %s = true :=" % (advp, ea, eb)
                                                                 ).split(" "), "    ")
                body += ["  checkPackedSp_of_groups %s %s %s [%s.shardRange] %s" % (advp, ea, eb, advp, hpre),
                         "    (fun s hs => ⟨%s.shardRange, List.mem_singleton_self _, hs⟩)" % advp,
                         "    (fun g hg => by rw [List.mem_singleton.1 hg]; exact %s_%s_shards)" % (nm, p), ""]
                hx = aux("%s.isEmpty = false" % X)
                hy = aux("%s.isEmpty = false" % Y)
                hla = aux("%s.la.allSlots %s = true" % (advp, X))
                hlb = aux("%s.lb.allSlots %s = true" % (advp, Y))
                hparts[p] = ("(packedRealProduct_eq_of_sparse %s %s (2 * %d) %s %s %s %s %s %s %s_%s_sp)"
                             % (advp, W, P, X, Y, hx, hy, hla, hlb, nm, p))
                tparts[p] = "%s_%s_dec" % (nm, p)
                rems[p] = "%s.remainderBound %s (2 * %d)" % (advp, W, P)
                tt[p] = tn
            else:
                xe = parts[p]["x"] == 0
                hparts[p] = ("(packedRealProduct_eq_nil_left %s %s (2 * %d) %s %s)"
                             % (advp, W, P, Y, aux("%s.isEmpty = true" % X)) if xe else
                             "(packedRealProduct_eq_nil_right %s %s (2 * %d) %s %s)"
                             % (advp, W, P, X, aux("%s.isEmpty = true" % Y)))
                tparts[p] = "(dyadicTerms_nil_cseg _ _ _)"
                rems[p] = "0"
                tt[p] = "([] : List (CertKey × CC %s))" % CE.TY
        tl = " ++ ".join(tt[p] for p in CE.PART_ORDER)
        rl = " + ".join(rems[p] for p in CE.PART_ORDER)
        hca = aux("%s.isConst = false" % a)
        hcb = aux("%s.isConst = false" % b)
        hma = aux("(%s).isSome = true" % ma)
        hmb = aux("(%s).isSome = true" % mb)
        out = "((⟨%s⟩ : CertPoly %s), (ofRatUp (%s) : %s))" % (tl, CE.TY, rl, CE.TY)
        self.memo_out[k] = "(%s.1.toErrTerms, %s.2)" % (out, out)
        stmt = "CertModel.polyProduct %s %s %s %s %s = some (%s.1.toErrTerms, %s.2)" % (W, cfg, key, a, b, out, out)
        body += ["/-- The packed product %d (%s, key %s). -/" % (k, m["cfg"], list(m["fullKey"]))]
        body += ["theorem %s :" % nm] + wrap(stmt.split(" "), "    ")
        body[-1] += " :="
        pp = {p: ("(%s.%s.targetTerms, %s)" % (advname, p, rems[p]) if p in ne else
                  "(([] : List (CertKey × ℤ)), (0 : ℚ))") for p in CE.PART_ORDER}
        body += wrap(["polyProduct_eq_of_mulPacked", W, cfg, key, a, b, str(P)] +
                     ["%s.%s" % (advname, p) for p in CE.PART_ORDER] + [out, hca, hcb, "rfl"], "  ")
        body += wrap(["(CertPoly.mulPacked_eq_of_parts", "%s.toMant" % cfg, W, str(P)] +
                     ["%s.%s" % (advname, p) for p in CE.PART_ORDER] + [a, b,
                     "(ma := (%s.getD ([], [])))" % ma, "(mb := (%s.getD ([], [])))" % mb] +
                     ["(p%s := %s)" % (p.upper(), pp[p]) for p in CE.PART_ORDER] +
                     ["(t%s := %s)" % (p.upper(), tt[p]) for p in CE.PART_ORDER], "    ")
        body += ["      (eq_some_getD_cseg ([], []) %s)" % hma, "      (eq_some_getD_cseg ([], []) %s)" % hmb]
        for p in CE.PART_ORDER:
            body += ["      " + hparts[p]]
        for p in CE.PART_ORDER:
            body += ["      " + tparts[p]]
        body[-1] += ")"
        mod = self.tree.write("Prod/M%d" % k, imps + mods, "Packed product %d" % k,
                              "The product equation from its parts' shards and decodes (L1c).",
                              [CE.Emitter.fix_long(l) for l in body], heavy=True)
        self.prod_done[k] = mod

    def emit_rem(self, k, adv, P, imps, register=True):
        """`adv.remainderBound W (2 * P)` as a literal, from the slot ranges (RemSplit.lean): per range one module
        for the largest slot degree and one for the slot sum, and an assembly module.  Returns (module, theorem,
        the literal's text, the term it replaces)."""
        po = ADVOBJ[adv]
        degs = SP.slotDegs(po)
        box = SP.InBox(po)
        n = len(degs)
        cuts = list(range(0, n, REM_CHUNK)) + [n]
        M = max(degs) if degs else 0
        num, den = WEIGHT_W.numerator, WEIGHT_W.denominator
        hi_in, hi_out = 1 << po.scale, 1 << (po.outLog + 1)
        tag = "%s%s" % (self.memo_name(k), adv.rsplit(".", 1)[1].upper())
        Ms, Ns, mods = [], [], []
        f = ("(fun i => %s.slotErr i * base.weight.w.num.toNat ^ %s.slotDeg i * base.weight.w.den ^ (%d - %s.slotDeg"
             " i))" % (adv, adv, M, adv))
        for j in range(len(cuts) - 1):
            a, b = cuts[j], cuts[j + 1]
            Ms.append(max(degs[a:b]))
            Ns.append(sum((hi_in if box(i) else hi_out) * num ** degs[i] * den ** (M - degs[i]) for i in range(a, b)))
            body = ["theorem %s_remM%d :" % (tag, j)] + wrap(("packRangeMax %s.slotDeg (%d - %d) %d (%d - %d) = %d := by"
                                                               % (adv, b, a, a, b, a, Ms[-1])).split(" "), "    ")
            body += ["  decide +kernel", "", "/-- The slot sum of the range. -/", "def %s_remN%d : ℕ :=" % (tag, j)]
            body += wrap(natlit(Ns[-1]).split(" "), "  ") + ["", "theorem %s_remS%d :" % (tag, j)]
            body += wrap(("packRangeSum %s (%d - %d) %d (%d - %d) = %s_remN%d := by" % (f, b, a, a, b, a, tag, j)
                          ).split(" "), "    ") + ["  decide +kernel"]
            mods.append(self.tree.write("Prod/%sRem%d" % (tag[len(self.t):], j), self.base + list(imps) + [REMSPLIT],
                                        "Remainder bound of %s, slots %d to %d" % (adv, a, b),
                                        "One kernel run per theorem (RemSplit.lean).",
                                        [CE.Emitter.fix_long(l) for l in body], heavy=True))
        ps = "[%s]" % ", ".join(map(str, cuts[1:]))
        Mf, Nf = ".nil", ".nil"
        for j in reversed(range(len(Ms))):
            Mf = "(.cons %s_remM%d %s)" % (tag, j, Mf)
            Nf = "(.cons %s_remS%d %s)" % (tag, j, Nf)
        cp = "(cutPairs [%s])" % ", ".join(map(str, cuts))
        lit = "(([%s].sum : ℕ) : ℚ) / ((base.weight.w.den ^ %d * 2 ^ (2 * %d) : ℕ) : ℚ)" % (
            ", ".join("%s_remN%d" % (tag, j) for j in range(len(Ns))), M, P)
        body = ["theorem %s_len : %s.prodLen = %d := by" % (tag, adv, n), "  decide +kernel", ""]
        body += ["theorem %s_maxF :" % tag] + wrap(("List.Forall₂ (fun p M => packRangeMax %s.slotDeg (p.2 - p.1) p.1"
                                                     " (p.2 - p.1) = M) %s [%s] :=" % (adv, cp, ", ".join(map(str, Ms)))
                                                     ).split(" "), "    ") + wrap(Mf.split(" "), "  ") + [""]
        body += ["theorem %s_max : %s.maxSlotDeg = %d := by" % (tag, adv, M)]
        body += _hang("rw [maxSlotDeg_eq_of_cuts %s %d %s_len %s (by decide +kernel) (by decide +kernel) %s_maxF]"
                      % (adv, n, tag, ps, tag))
        body += ["  decide +kernel", ""]
        body += ["theorem %s_sumF :" % tag] + wrap(("List.Forall₂ (fun p N => packRangeSum %s (p.2 - p.1) p.1 (p.2 - p.1)"
                                                     " = N) %s [%s] :=" % (f, cp, ", ".join("%s_remN%d" % (tag, j) for j in range(len(Ns))))).split(" "),
                                                    "    ") + wrap(Nf.split(" "), "  ") + [""]
        body += ["theorem %s_rb :" % tag] + wrap(("%s.remainderBound base.weight (2 * %d) = %s := by" % (adv, P, lit)
                                                  ).split(" "), "    ")
        body += _hang("rw [remainderBound_eq_of_cuts %s base.weight (2 * %d) %d %d %s_len %s_max %s (by decide +kernel)"
                      " (by decide +kernel) %s_sumF]" % (adv, P, n, M, tag, tag, ps, tag))
        mod = self.tree.write("Prod/%sRem" % tag[len(self.t):], self.base + list(imps) + [REMSPLIT] + mods,
                              "Remainder bound of %s" % adv, "Assembled from the slot ranges (RemSplit.lean).",
                              [CE.Emitter.fix_long(l) for l in body], heavy=False)
        if register:
            REMLIT["%s.remainderBound base.weight (2 * %d)" % (adv, P)] = lit
        return (mod, "%s_rb" % tag, lit, "%s.remainderBound base.weight (2 * %d)" % (adv, P))


    def emit_products(self, operand_of):
        self.prod_done = {}
        self.memo_out = {}
        self.prod_led = {}
        memo_only = {k: v for k, v in operand_of.items() if self.led_route(k) is None}
        items = []
        for k in sorted(memo_only):
            m = self.led["memos"][k]
            terms = list(m["out"][0]) if m["out"] else []
            split = self.part_terms(k, m)
            if split is None:
                items.append(("%sT" % self.memo_name(k), CE.terms_defs(self.memo_name(k) + "T", terms, named=True)[0]))
            else:
                for p_, ts_ in split.items():
                    tn_ = "%sT%s" % (self.memo_name(k), p_.upper())
                    items.append((tn_, CE.terms_defs(tn_, ts_, named=True)[0]))
        self.memo_data = self.tree.data("Memo", "Decoded packed products of the lock",
                                        "The decoded output of the products not checked against the ledger.",
                                        items, self.base) if items else []
        for k in sorted(operand_of):
            if k in memo_only:
                self.emit_product(k, self.led["memos"][k], *operand_of[k])
            else:
                self.emit_product_led(k, self.led["memos"][k], *operand_of[k])

    def emit_product_led(self, k, m, cfg, key, a, b, imps):
        """per nonempty real part its shards (as `emit_product`); then `mulN … = (C.slotPair W slot).1`, the decodes
        by `getD`, the result compared with the ledger model in the kernel: no decoded literal."""
        P = CE.P
        chain, slot, sa, sb = self.led_route(k)
        C, W = self.ck(chain), self.W
        nm = self.memo_name(k)
        advname, Pm = self.advRef(m["cfg"], m["fullKey"])
        assert Pm == P
        parts = {p["part"]: p for p in m["parts"]}
        ne = [p for p in CE.PART_ORDER if not parts[p]["empty"]]
        if LED_HEAVY:
            # the heavy classification of `emit_product` (operand slot-term pairs >= HEAVY_PAIRS): missing here
            # before, so ~570 heavy ledger-routed products ran their shards without operand literals (M7 OOM)
            for p in ne:
                advp = "%s.%s" % (advname, p)
                rec = EAEB.get(ADVKEY[advp][:2], {}).get(p)
                if rec and len(rec[0]) * len(rec[1]) >= HEAVY_PAIRS:
                    HEAVYADV.add(advp)
        imps = self.base + imps
        ma = "(%s.toMants %s.toMant %d)" % (a, cfg, P)
        mb = "(%s.toMants %s.toMant %d)" % (b, cfg, P)
        xy = dict(rr=(".1", ".1"), ii=(".2", ".2"), ri=(".1", ".2"), ir=(".2", ".1"))
        fpart = dict(rr="(fun v => ⟨v, ofInt 0⟩)", ii="(fun v => ⟨v, ofInt 0⟩)", ri="(fun v => ⟨ofInt 0, v⟩)",
                     ir="(fun v => ⟨ofInt 0, v⟩)")
        shmods, body, dmods = [], [], []
        hparts, tparts, tt, pp, rems = {}, {}, {}, {}, {}
        for p in CE.PART_ORDER:
            advp = "%s.%s" % (advname, p)
            X = "((%s.getD ([], []))%s)" % (ma, xy[p][0])
            Y = "((%s.getD ([], []))%s)" % (mb, xy[p][1])
            if p in ne:
                ea = "(%s.la.slotTerms %s)" % (advp, X)
                eb = "(%s.lb.slotTerms %s)" % (advp, Y)
                sh = ["theorem %s_%s_shards :" % (nm, p)] + wrap(
                    ("%s.shardRange.all (checkShardAt %s %s %s) = true := by" % (advp, advp, ea, eb)).split(" "),
                    "    ") + ["  decide +kernel"]
                shmods.append(self.tree.write("Prod/M%d%sSh" % (k, p.upper()), imps,
                                              "Packed product %d, part %s: shards" % (k, p),
                                              "The shard group of one packed real product (L1c (a)).", sh, heavy=True))
                body += ["theorem %s_%s_sp :" % (nm, p)] + wrap(
                    ("checkPackedSp %s %s %s = true :=" % (advp, ea, eb)).split(" "), "    ")
                body += ["  checkPackedSp_of_groups %s %s %s [%s.shardRange] (by decide +kernel)" % (advp, ea, eb, advp),
                         "    (fun s hs => ⟨%s.shardRange, List.mem_singleton_self _, hs⟩)" % advp,
                         "    (fun g hg => by rw [List.mem_singleton.1 hg]; exact %s_%s_shards)" % (nm, p), ""]
                # the four side checks one module each (inline in one module with the comparison: Prod.M7 OOM)
                sides = []
                for q, st_ in enumerate(("%s.isEmpty = false" % X, "%s.isEmpty = false" % Y,
                                         "%s.la.allSlots %s = true" % (advp, X),
                                         "%s.lb.allSlots %s = true" % (advp, Y))):
                    tn = "%s_%s_side%d" % (nm, p, q)
                    dmods.append(self.tree.write("Prod/M%d%sSide%d" % (k, p.upper(), q), imps,
                                                 "Packed product %d, part %s: side check %d" % (k, p, q),
                                                 "One kernel run.", ["theorem %s :" % tn] +
                                                 wrap(("%s := by" % st_).split(" "), "    ") + ["  decide +kernel"],
                                                 heavy=True))
                    sides.append(tn)
                hparts[p] = ("(packedRealProduct_eq_of_sparse %s %s (2 * %d) %s %s %s %s_%s_sp)"
                             % (advp, W, P, X, Y, " ".join(sides), nm, p))
                rems[p] = "%s.remainderBound %s (2 * %d)" % (advp, W, P)
                pp[p] = "(%s.targetTerms, %s)" % (advp, rems[p])
                pair = "(%s.targetTerms, %s.remainderBound %s (2 * %d)).1" % (advp, advp, W, P)
                src = "(%s)" % pair if p != "ii" else "((%s).map fun t => (t.1, -t.2))" % pair
                tt[p] = "((dyadicTerms (2 * %d) %s.scale %s %s).getD [])" % (P, advp, fpart[p], src)
                # named (own heartbeat budget): the inline decodes made the product theorem time out (M7)
                # standalone statement: the coefficient maps typed (`CertArith ?m` stuck otherwise, measured)
                fty = fpart[p].replace("⟩)", "⟩ : CC %s))" % TY).replace("=> ⟨", "=> (⟨")
                ttd = "((dyadicTerms (2 * %d) %s.scale %s %s).getD [])" % (P, advp, fty, src)
                dst = "dyadicTerms (2 * %d) %s.scale %s %s = some %s :=" % (P, advp, fty, src, ttd)
                # its own module: one process decoding twice (here and in the final comparison) was OOM-killed (M7)
                dmods.append(self.tree.write("Prod/M%d%sLDec" % (k, p.upper()), imps,
                                             "Packed product %d, part %s: the decode" % (k, p), "One kernel run.",
                                             ["theorem %s_%s_dec :" % (nm, p)] + wrap(dst.split(" "), "    ") +
                                             ["  eq_some_getD_cseg [] (by decide +kernel)"], heavy=True))
                tparts[p] = "%s_%s_dec" % (nm, p)
            else:
                xe = parts[p]["x"] == 0
                # the emptiness check named, in its own module (inline, it recomputed the operand mantissas inside
                # _mp: heartbeat timeout, M7MP)
                ztn = "%s_%s_nil" % (nm, p)
                zst = "%s.isEmpty = true := by" % (X if xe else Y)
                dmods.append(self.tree.write("Prod/M%d%sNil" % (k, p.upper()), imps,
                                             "Packed product %d, part %s: empty operand" % (k, p), "One kernel run.",
                                             ["theorem %s :" % ztn] + wrap(zst.split(" "), "    ") + ["  decide +kernel"],
                                             heavy=True))
                hparts[p] = ("(packedRealProduct_eq_nil_left %s %s (2 * %d) %s %s)" % (advp, W, P, Y, ztn)
                             if xe else
                             "(packedRealProduct_eq_nil_right %s %s (2 * %d) %s %s)" % (advp, W, P, X, ztn))
                rems[p] = "0"
                pp[p] = "(([] : List (CertKey × ℤ)), (0 : ℚ))"
                tt[p] = "([] : List (CertKey × CC %s))" % TY
                tparts[p] = "(dyadicTerms_nil_cseg _ _ _)"
        tl = " ++ ".join(tt[p] for p in CE.PART_ORDER)
        rl = " + ".join(rems[p] for p in CE.PART_ORDER)
        out = "((⟨%s⟩ : CertPoly %s), (ofRatUp (%s) : %s))" % (tl, TY, rl, TY)
        sA, sB = "(%s.slotPair %s %d)" % (C, W, sa), "(%s.slotPair %s %d)" % (C, W, sb)
        stmt = ("CertModel.mulN %s %s %s %s.1 %s.2 %s.1 %s.2 = (%s.slotPair %s %d).1"
                % (W, cfg, key, sA, sA, sB, sB, C, W, slot))
        # the operand mantissas and the whole mulPacked equation as named theorems (each its own heartbeat budget;
        # the single inline term timed out at the default heartbeats, M7)
        advs = " ".join("%s.%s" % (advname, p) for p in CE.PART_ORDER)
        mant = []
        for nmx, mx in (("ma", ma), ("mb", mb)):
            mant += ["theorem %s_%s :" % (nm, nmx)] + wrap(("%s = some (%s.getD ([], [])) :=" % (mx, mx)).split(" "),
                                                            "    ")
            mant += ["  eq_some_getD_cseg ([], []) (by decide +kernel)", ""]
        dmods.append(self.tree.write("Prod/M%dMant" % k, imps, "Packed product %d: operand mantissas" % k,
                                     "Two kernel runs.", mant, heavy=True))
        mp = (["CertPoly.mulPacked_eq_of_parts", "%s.toMant" % cfg, W, str(P)] +
              ["%s.%s" % (advname, p) for p in CE.PART_ORDER] + [a, b,
              "(ma := (%s.getD ([], [])))" % ma, "(mb := (%s.getD ([], [])))" % mb] +
              ["(p%s := %s)" % (p.upper(), pp[p]) for p in CE.PART_ORDER] +
              ["(t%s := %s)" % (p.upper(), tt[p]) for p in CE.PART_ORDER] +
              ["%s_ma" % nm, "%s_mb" % nm] + [hparts[p] for p in CE.PART_ORDER] + [tparts[p] for p in CE.PART_ORDER])
        body += ["theorem %s_mp :" % nm] + wrap(("CertPoly.mulPacked %s.toMant %s %d %s %s %s = some %s :="
                                                 % (cfg, W, P, advs, a, b, out)).split(" "), "    ")
        body += wrap(mp, "  ") + [""]
        # everything up to here (shard cover/groups, _sp, _mp with its inline side checks) in its own module; the
        # product module keeps the final comparison with the ledger model (Prod.M7 at 10 GB holding both)
        mpmod = self.tree.write("Prod/M%dMP" % k, imps + shmods + dmods, "Packed product %d: the packed equation" % k,
                                "Shard cover, groups, the sparse checks and the mulPacked equation.",
                                [CE.Emitter.fix_long(l) for l in body], heavy=True)
        dmods.append(mpmod)
        body = []
        body += ["/-- The packed product %d (%s, key %s), checked against the ledger model of slot %d. -/"
                 % (k, m["cfg"], list(m["fullKey"]), slot)]
        body += ["theorem %s :" % nm] + wrap(stmt.split(" "), "    ")
        body[-1] += " := by"
        hp = (["(polyProduct_eq_of_mulPacked", W, cfg, key, a, b, str(P)] +
              ["%s.%s" % (advname, p) for p in CE.PART_ORDER] + [out, "(by decide +kernel)", "(by decide +kernel)",
                                                                "rfl", "%s_mp)" % nm])
        body += wrap(["rw", "[CertModel.mulN_eq_of_polyProduct", W, cfg, key, "_", "_", "_", "_"] + hp + ["]"], "  ")
        # the comparison with the ledger model by parts, each in its own module (the whole comparison recomputes
        # the decode, truncation, error radius and cross terms at once: OOM at 10 GB, M7)
        outp = "(%s.1.toErrTerms, %s.2)" % (out, out)
        led_m = "(%s.slotPair %s %d).1" % (C, W, slot)
        pst = "(truncPoly %s.cutoff %s.1).terms = %s.poly.terms :=" % (cfg, outp, led_m)
        rst = ("upAdd (upAdd %s.2 (errRadius %s (%s.1.map (truncErr %s.cutoff)))) (upAdd (upAdd (crossUp %s.2 %s.1.rad)"
               " (crossUp %s.2 %s.1.rad)) (upMul %s.1.rad %s.1.rad)) = %s.rad := by"
               % (outp, W, outp, cfg, sA, sB, sB, sA, sA, sB, led_m))
        pm_ = self.tree.write("Prod/M%dPoly" % k, imps + shmods + dmods, "Packed product %d: terms against the ledger" % k,
                              "One kernel run: the truncated decoded terms equal the ledger model's.",
                              ["theorem %s_poly :" % nm] + wrap(pst.split(" "), "    ") +
                              ["  eq_of_termsBeq (by decide +kernel)"], heavy=True)
        # the radius by its three summands, each a literal from the mirror proved in its own module (the whole radius
        # in one kernel run: OOM at 10 GB, M7Rad and M725Rad in tp10): the remainder `out.2`, the error radius of the
        # decoded terms, and the cross terms of the two operand models; the radius module adds the three literals
        R_, E_, X_ = self.rad_parts(k, m, chain, slot, sa, sb)
        rdeps = imps + shmods + dmods
        rparts = (("R", "%s.2 = %s := by" % (outp, CE.fixed(R_)), "the packed remainder"),
                  ("E", "errRadius %s (%s.1.map (truncErr %s.cutoff)) = %s := by" % (W, outp, cfg, CE.fixed(E_)),
                   "the error radius of the decoded terms"),
                  ("X", "upAdd (upAdd (crossUp %s.2 %s.1.rad) (crossUp %s.2 %s.1.rad)) (upMul %s.1.rad %s.1.rad) = %s := by"
                   % (sA, sB, sB, sA, sA, sB, CE.fixed(X_)), "the cross terms of the operands"))
        # the remainder from its slot ranges (RemSplit.lean, as the memo products): inline, one kernel run of the
        # remainder bound peaked at 10.1-10.3 GB (M7RadR, M725RadR in tp15)
        rems_ = [self.emit_rem(k, "%s.%s" % (advname, p), P, imps, register=False) for p in ne]
        rmods = []
        for tag, st_, what in rparts:
            deps_, pf_ = rdeps, ["  decide +kernel"]
            if tag == "R" and rems_:
                deps_ = rdeps + [r_[0] for r_ in rems_]
                pf_ = _hang("rw [%s]" % ", ".join(r_[1] for r_ in rems_)) + ["  decide +kernel"]
            rmods.append(self.tree.write("Prod/M%dRad%s" % (k, tag), deps_,
                                         "Packed product %d: radius, %s" % (k, what),
                                         "One kernel run: %s equals its literal (mirror)." % what,
                                         ["theorem %s_rad%s :" % (nm, tag)] + wrap(st_.split(" "), "    ") + pf_,
                                         heavy=True))
        fin = ("(congrArg₂ upAdd (congrArg₂ upAdd %s_radR %s_radE) %s_radX).trans (by decide +kernel)"
               % (nm, nm, nm))
        rm_ = self.tree.write("Prod/M%dRad" % k, imps + rmods, "Packed product %d: radius against the ledger" % k,
                              "The product's radius equals the ledger model's: the sum of its three literal summands.",
                              ["theorem %s_rad :" % nm] + wrap(rst[:-len(" by")].split(" "), "    ") +
                              wrap(fin.split(" "), "  "), heavy=True)
        dmods += [pm_] + rmods + [rm_, FALLBACKMUL]
        body += ["  exact certModel_eq_of_parts (by decide +kernel) %s_poly %s_rad" % (nm, nm)]
        mod = self.tree.write("Prod/M%d" % k, imps + shmods + dmods, "Packed product %d" % k,
                              "The product against its ledger model (B3 lever (c); no decoded literal).",
                              [CE.Emitter.fix_long(l) for l in body], heavy=True)
        self.prod_done[k] = mod
        self.prod_led[k] = nm

    def rad_parts(self, k, m, chain, slot, sa, sb):
        """the mirror's three summands of a ledger-routed product's radius (`mulN`): the remainder, the error radius of
        the decoded terms and the cross terms; checked against the ledger model's radius."""
        import sofx_model as SM
        c = self.mirror
        B, Wm = c.B, c.weight
        cf = c.cfgFull if chain == "cfgFull" else c.cfgLow
        L = self.led["chains"][chain]["ledger"]
        assert m["out"], k
        items = SM.toErrTerms(B, m["out"][0])
        R = m["out"][1]
        E = SM.errRadius(B, Wm, [SM.truncErr(B, cf.cutoff, t_) for t_ in items])
        (ma_, na), (mb_, nb) = L[sa], L[sb]
        X = B.upAdd(B.upAdd(SM.crossUp(B, na, mb_.rad), SM.crossUp(B, nb, ma_.rad)), B.upMul(ma_.rad, mb_.rad))
        assert B.beq(B.upAdd(B.upAdd(R, E), X), L[slot][0].rad), ("radius mismatch", k, slot)
        return R, E, X

    def forced_mul_none(self, chain, j, s, nm):
        """the forced `.mul` segment of a product whose packed advice fails (memo without output): the composition
        step takes the `none` branch of `mulN` (FallbackMul.lean), the `none` decided by the kernel."""
        i = s["start"]
        op = self.led_ops[i]
        a, b = op[1], op[2]
        C, W, cfg = self.ck(chain), self.W, self.cfgOf(chain)
        spec = "(%sSegs.getD %d ⟨0, 0, [], [], []⟩)" % (C, j)
        meta = "(%sMetas.getD %d ⟨0, 0, 0, []⟩)" % (C, j)
        head = ["theorem %s :" % nm] + wrap(self.seg_stmt(chain, j).split(" "), "    ")
        head[-1] += " := by"
        # the `none` fact in its own module, under its own default budget (inline it exceeded the segment's
        # heartbeats: Low.S159/S169/S192/S202 in tp9; alone 8:39, 4.33 GB, probe)
        sub = "Full" if chain == "cfgFull" else "Low"
        nn = nm + "_none"
        mt = "(%s.metas[%d]?.getD (⟨0, 0, 0, []⟩ : ComposeMeta _))" % (C, j)
        nb = ["/-- The packed check of this segment's product fails (`none`; the composition takes the ball "
              "branch). -/",
              "theorem %s :" % nn,
              "    (CertModel.polyProduct %s %s" % (W, cfg),
              "      [0, %s.len]" % mt,
              "      (%s.slotPair %s %d).1.poly" % (C, W, a),
              "      (%s.slotPair %s %d).1.poly).isNone = true := by" % (C, W, b),
              "  decide +kernel"]
        nmod = self.tree.write("%s/S%dNone" % (sub, j), self.base + [self.plan_mods[chain]],
                               "The failed packed product of segment %d of the %s %s chain" % (j, self.w, chain),
                               "One `polyProduct … = none` fact (forced fallback segment; FallbackMul).", nb,
                               heavy=True)
        self.forced_imports[(chain, j)] = [FALLBACKMUL, nmod]
        return head + ["  refine ComposeCkpt.segOk_one_of (s := %s)" % spec,
                       "    (m := %s)" % meta,
                       "    (op := %s) (st' := ?st) rfl rfl rfl (by decide +kernel) ?hop ?hres" % self.op_lit(op),
                       "  case hop =>",
                       "    rw [shadowStep_of_live 2 base.emb base.wit %s %s %s (by decide +kernel)," % (W, cfg, self.pe),
                       "      composeStep_mul_eq,",
                       "      seed_slot_of_mem %s %s %s (a := %d) (by decide +kernel) (by decide +kernel)," % (W, meta, C, a),
                       "      seed_slot_of_mem %s %s %s (a := %d) (by decide +kernel) (by decide +kernel)," % (W, meta, C, b),
                       "      mulN_eq_of_polyProduct_none %s %s _ _ _ _ _ ?hnone]" % (W, cfg),
                       "    case hnone => exact %s" % nn,
                       "  case hres =>",
                       "    decide +kernel"]

    def forced_mul(self, chain, j, s, nm):
        """the forced `.mul` segment, rewriting with the ledger-checked product (lever (c))."""
        i = s["start"]
        op = self.led_ops[i]
        k = self.memo_index(chain, (0, i))
        if k not in self.prod_led:
            return None
        C, W, cfg, pe = self.ck(chain), self.W, self.cfgOf(chain), self.pe
        spec = "(%sSegs.getD %d ⟨0, 0, [], [], []⟩)" % (C, j)
        meta = "(%sMetas.getD %d ⟨0, 0, 0, []⟩)" % (C, j)
        head = ["theorem %s :" % nm] + wrap(self.seg_stmt(chain, j).split(" "), "    ")
        head[-1] += " := by"
        self.forced_imports[(chain, j)] = [self.prod_done[k]]
        return head + ["  refine ComposeCkpt.segOk_one_of (s := %s)" % spec,
                       "    (m := %s)" % meta,
                       "    (op := %s) (st' := ?st) rfl rfl rfl (by decide +kernel) ?hop ?hres" % self.op_lit(op),
                       "  case hop =>",
                       "    rw [shadowStep_of_live 2 base.emb base.wit %s %s %s (by decide +kernel)," % (W, cfg, pe),
                       "      composeStep_mul_eq,",
                       "      seed_slot_of_mem %s %s %s (a := %d) (by decide +kernel) (by decide +kernel)," % (
                           W, meta, C, op[1]),
                       "      seed_slot_of_mem %s %s %s (a := %d) (by decide +kernel) (by decide +kernel)," % (
                           W, meta, C, op[2]),
                       "      %s]" % self.prod_led[k],
                       "  case hres =>",
                       "    decide +kernel"]

    # ------------------------------------------------------------------ the parts emitted here
    def entry_eq(self, name, stmt, rws, rhs):
        """`csplit_emit.Emitter.entry_eq` with the DK models of the right side replaced by their kernel-checked
        literals (`DK/{A,P}ij`, `lock_dk…` rewrites): a Gram entry recomputing four DK models was OOM-killed at
        10 GB."""
        # the memoized products' remainder bounds as the literals their statements carry (Gram.E00 evaluated four
        # inline remainder bounds, ~30k slots each, and was OOM-killed at 10 GB)
        for term, lit in REMLIT.items():
            rhs = rhs.replace(term, "(%s)" % lit)
        pat = re.compile(r"\((dkAngleModel|dkActionModel) 2 base\.emb base\.weight base\.piEnc (\d) (\d)\)")
        used = sorted({("a" if m.group(1) == "dkAngleModel" else "p", m.group(2), m.group(3))
                       for m in pat.finditer(rhs)})
        if used:
            rhs = pat.sub(lambda m: "lockDK%s%s%s" % ("a" if m.group(1) == "dkAngleModel" else "p", m.group(2),
                                                      m.group(3)), rhs)
            rws = list(rws) + ["lock_dk%s%s%s" % u for u in used]
        mg = re.match(r"^lock_GE(\d)(\d)$", name)
        head = "modelSum base.weight base.piEnc ["
        if mg and rhs.startswith(head) and rhs.endswith("]") and getattr(self, "mirror", None) is not None:
            # each product model of the Gram entry proved equal to its literal in its own module (one kernel run;
            # Gram.E01 evaluating its four product models at once was OOM-killed at 10 GB); the entry decides on
            # the four literals.  Literals: the mirror's model_mul on the DK models with the cfgLow books.
            import sofx_model as SM
            a_, b_ = int(mg.group(1)), int(mg.group(2))
            inner = rhs[len(head):-1]
            spans = _arg_spans(inner.replace(", ", "  ") + " ", 0, 4)
            items = [inner[i:j].rstrip(",") for i, j in spans]
            c = self.mirror
            f = lambda r, x: ("a", r, x) if r < 2 else ("p", r - 2, x)
            imps = self.base + [self.stage_mod] + self.memo_imports(rws) + \
                ["%s.%s%s%s" % (DKNS, u[0].upper(), u[1], u[2]) for u in used]
            names = []
            for r, it in enumerate(items):
                m = SM.model_mul(c.B, c.weight, c.cfgLow, (3, 0, a_, b_, r), c.DKc[f(r, a_)], c.DKc[f(r, b_)])
                nmx = "lockGE%d%dX%d" % (a_, b_, r)
                body = CE.model_defs(nmx, m)
                body += ["theorem lock_GE%d%dX%d :" % (a_, b_, r)] + wrap(("%s = %s :=" % (it, nmx)).split(" "),
                                                                            "    ")
                body += ["  CertModel.eq_of_segBeq (by decide +kernel)"]
                self.tree.write("Gram/E%d%dX%d" % (a_, b_, r), imps, "Gram entry (%d, %d), product model %d"
                                % (a_, b_, r), "One kernel run: the product model equals its literal.", body,
                                heavy=True)
                names.append(nmx)
            rhs = head + ", ".join(names) + "]"
            rws = list(rws) + ["lock_GE%d%dX%d" % (a_, b_, r) for r in range(len(items))]
        return CE.Emitter.entry_eq(self, name, stmt, rws, rhs)

    def emit_plans(self):
        """`csplit_emit.Emitter.emit_plans` with each list (segments, metadata, ledger) cut into chunks of
        PLAN_CHUNK entries, written as data parts and joined by `++` (the cfgLow plan is ~3000 lines; same values,
        same names)."""
        self.plan_mods = {}
        for chain in ("cfgFull", "cfgLow"):
            p, ck = self.plan[chain], self.ck(chain)
            segs = []
            for s in p["segs"]:
                one = ["⟨%d, %d, %s, %s, %s⟩" % (s["start"], s["stop"], nat_list(s["live"]), nat_list(s["imports"]),
                                                nat_list(s["exports"]))]
                segs.append(wrap(one, "  ") if len(one[0]) < 96 else self.long_spec(s, False))
            for e in segs:
                if not e[-1].endswith("⟩"):       # long_spec closes with "⟩]"
                    e[-1] = e[-1][:-1]
            bounds = [s["start"] for s in p["segs"]] + [p["segs"][-1]["stop"]]
            metas = [wrap(self.meta_lit(chain, b).split(" "), "  ") for b in bounds]
            led = sorted(self.led["chains"][chain]["ledger"])
            ledl = [["  (%d, (%s, %sN))" % (i, self.slotName(chain, i), self.slotName(chain, i))] for i in led]
            items, joins, needs = [], {}, {}
            for tag, ty, ents in (("Segs", "List SegSpec", segs),
                                  ("Metas", "List (ComposeMeta %s)" % CE.TY, metas),
                                  ("Ledger", "List (ℕ × (CertModel %s × %s))" % (CE.TY, CE.TY), ledl)):
                names = []
                for c0 in range(0, len(ents), PLAN_CHUNK):
                    ch = ents[c0:c0 + PLAN_CHUNK]
                    nm = "%s%s.c%d" % (ck, tag, c0 // PLAN_CHUNK)
                    lines = ["def %s : %s := [" % (nm, ty)]
                    for j, e in enumerate(ch):
                        lines += e[:-1] + [e[-1] + ("," if j + 1 < len(ch) else "]")]
                    items.append((nm, lines + [""]))
                    names.append(nm)
                    if tag == "Ledger":
                        needs[nm] = sorted({self.tree.defs[self.slotName(chain, i)]
                                            for i in led[c0:c0 + PLAN_CHUNK]})
                joins[tag] = (ty, names)
            stem = "Plan%s" % ("Full" if chain == "cfgFull" else "Low")
            parts = data_flat(self.tree, stem + "Part", "The %s plan of the %s chain (lists)" % (self.w, chain),
                              "Chunks of the segments, boundary metadata and ledger (untrusted data).", items,
                              self.base, needs=lambda nm: needs.get(nm, []))
            body = []
            for tag, doc in (("Segs", "The segments"), ("Metas", "The boundary metadata"), ("Ledger", "The ledger")):
                ty, names = joins[tag]
                body += ["/-- %s of the %s chain. -/" % (doc, chain), "def %s%s : %s :=" % (ck, tag, ty)]
                body += ["  " + " ++\n    ".join(names), ""]
            body += ["/-- The checkpointed %s composition. -/" % chain,
                     "def %s : ComposeCkpt %s := ⟨%sSegs, %sMetas, %sLedger⟩" % (ck, CE.TY, ck, ck, ck)]
            self.plan_mods[chain] = self.tree.write(stem, self.base + parts,
                                                    "The %s plan of the %s chain" % (self.w, chain),
                                                    "Segments, boundary metadata and ledger (untrusted data; "
                                                    "`planOk`/`segOk` check them).", body)

    def emit_ledger(self):
        """`csplit_emit.Emitter.emit_ledger` with the parts unchained (`data_flat`): each ledger part imports only
        the base, so the parts elaborate in parallel; the plan's ledger chunks import the parts of their slots."""
        mods = {}
        for chain in ("cfgFull", "cfgLow"):
            L = self.led["chains"][chain]["ledger"]
            items = [(self.slotName(chain, i), CE.model_defs(self.slotName(chain, i), L[i][0], L[i][1]))
                     for i in sorted(L)]
            mods[chain] = data_flat(self.tree, "Ledger%s" % ("Full" if chain == "cfgFull" else "Low"),
                                    "The %s ledger of the %s chain" % (self.w, chain),
                                    "Ledger pairs `(model, cached norm)` (route E; SO-CSPLIT §5).", items, self.base)
        self.ledger_mods = mods

    def emit_charE(self):
        """`charE`: the terms of the character witness of the forced character slot (the lunar emitter's name)."""
        c = self.led["char"]["cfgFull"]["cidx"]
        body = ["/-- The character witness of the forced character slot. -/",
                "def charE : List (CertKey × CC %s) := %s.terms" % (TY, self.char_term(c))]
        self.base = self.base + [self.tree.write("CharE", self.base, "The forced character witness",
                                                "The witness of the character slot, by name.", body)]

    def run(self):
        self.led_ops = [tuple(o) for o in self.led["ops"]]
        self.emit_charE()
        self.emit_ledger()
        self.emit_plans()
        self.stage_mod = self.tree.mod("StageMats")
        self.ops_map = self.operands()
        self.emit_products(self.ops_map)
        if self.slots is None or self.led["char"]["cfgFull"]["slot"] in self.slots:
            self.emit_char()
        self.emit_segments()
        if self.slots is None and os.environ.get("LOCK_STAGES", "1") != "0":
            # the landed stages and checks (Gram, torsion, invariance, energy, frames)
            self.emit_stage_data()
            self.emit_chain()
            self.emit_gram()
            self.emit_torsion()
            self.emit_checks()


def main(argv):
    slots = None
    if "--slots" in argv:
        slots = {int(x) for x in argv[argv.index("--slots") + 1].split(",")}
    gdir, plan_path, led_path, fall_path, root = argv[:5]
    import json
    import lock_seg as LSG
    plan = json.load(open(plan_path))
    led = pickle.load(open(led_path, "rb"))
    fall = pickle.load(open(fall_path, "rb"))
    _load_eaeb(os.path.join(os.path.dirname(fall_path), "eaeb.pkls"))
    if os.environ.get("LOCK_SOSK"):
        sk = pickle.load(open(os.environ["LOCK_SOSK"], "rb"))
        led["memos"] = list(led["memos"]) + sk["memos"]
        for key_, rec in sk["eaeb"].items():
            EAEB[(key_[0], tuple(key_[1]))] = rec
        print("SOS option (a): %d memos appended (indices %d..)" % (len(sk["memos"]), len(led["memos"]) - 2))
    E = LockEmitter(gdir, plan, led, fall, root, slots)
    c, _d = LSG.lock_cert(gdir)
    E.mirror = c
    E.set_char_wit(c.wit.charWit)
    E.run()
    E.tree.save()
    n = sum(t.count("\n") for t in E.tree.files.values())
    by = sum(len(t.encode()) for t in E.tree.files.values())
    print("lock", len(E.tree.files), "modules", n, "lines", by, "bytes", len(E.tree.heavy), "heavy")
    print("hk by chunks: %d products" % len(HKFIXED))
    print("heavy product parts (operand literals): %d" % len(HEAVYADV))
    print("remainder literal: %d product parts in %d products (heavy %d parts)" % (
        len(REMCLASS), len({k for k, _ in REMCLASS}), len({a for _, a in REMCLASS if a in HEAVYADV})))


if __name__ == "__main__":
    main(sys.argv[1:])
