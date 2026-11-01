#!/usr/bin/env python3
"""V2-TOOLS #6: emit a forced-toy certificate (forced_cert.generate) as Lean data.  Untrusted tooling.

The data module defines, in `namespace KAM.CertificateSharp.V2.Forced`, for a certificate tag `T`:
    T.params : CertParams, T.ham : HamExpr 2, T.u T.p T.J : CertRealPoly FB, T.E<k> : CertPoly FB,
    T.gramInv, T.torsInv, T.advFull, T.advLow, T.box, T.cert : TorusCertificate 2 FB
with `FB = CertFixed P`.  A Fourier term is `ft k0 k1 re im` (mantissas at 2^-P); `Format.lean` holds the helpers.
Every line is at most 100 columns; a poly longer than CHUNK terms is split into `++`-joined parts.
"""
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import forced_model as FM          # noqa: E402

HEADER = """/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

"""
CHUNK = 40
WIDTH = 100


def q(x):
    return FM.lean_q(F(x))


def wrap(head, items, indent="  ", sep=", ", close="]"):
    """`head` then the items, wrapped at WIDTH."""
    lines, cur = [], head
    for i, it in enumerate(items):
        last = i == len(items) - 1
        s = it + (sep.rstrip() if not last else "")
        if len(cur) + len(s) + 1 + (len(close) if last else 0) > WIDTH:
            lines.append(cur.rstrip())
            cur = indent + s + " "
        else:
            cur += s + " "
    cur = cur.rstrip() + close
    lines.append(cur)
    return "\n".join(lines)


def z(x):
    return "(%d)" % x if x < 0 else "%d" % x


def term(k, v):
    return "ft %s %s %s %s" % (z(k[0]), z(k[1]), z(v[0]), z(v[1]))


def poly_def(name, terms, doc):
    """terms: list of (key, (re, im)) mantissas; split into chunks."""
    out = []
    if len(terms) <= CHUNK:
        out.append("/-- %s -/" % doc)
        out.append("def %s : List (CertKey × CC FB) :=" % name)
        out.append(wrap("  [", [term(k, v) for k, v in terms]) if terms else "  []")
        return "\n".join(out) + "\n"
    parts = [terms[i:i + CHUNK] for i in range(0, len(terms), CHUNK)]
    for j, P in enumerate(parts):
        out.append("/-- %s, part %d -/" % (doc, j))
        out.append("def %s_%d : List (CertKey × CC FB) :=" % (name, j))
        out.append(wrap("  [", [term(k, v) for k, v in P]))
        out.append("")
    out.append("/-- %s -/" % doc)
    out.append("def %s : List (CertKey × CC FB) :=" % name)
    out.append(wrap("  ", ["%s_%d" % (name, j) for j in range(len(parts))], sep=" ++", close=""))
    return "\n".join(out) + "\n"


def params_lean(p):
    keys = [("tau", "tau"), ("rho", "rho"), ("rhoInf", "rhoInf"), ("M", "M"), ("σK", "sK"), ("σB", "sB"),
            ("σT", "sT"), ("μ", "mu"), ("γbar", "gbar"), ("σω", "som"), ("nuRay", "nu"), ("γ", "gamma"),
            ("s", "s"), ("err", "err"), ("E0", "E0"), ("disp", "disp")]
    items = []
    for ln, pk in keys:
        v = p[pk]
        items.append("%s := %s" % (ln, str(v) if ln == "tau" else q(v)))
    return wrap("  { ", items, indent="    ", close=" }")


def adv_lean(book):
    keys = ["[%s]" % ", ".join(str(x) for x in k) for k, adv in book]
    for _, adv in book:
        assert adv[0] == "direct"
    return wrap("  [", ["(%s, .direct)" % k for k in keys]) if keys else "  []"


def mant_pair(w):
    return "⟨⟨%d⟩, ⟨%d⟩⟩" % (w[0], w[1])


def emit_data(c, tag, modname, doc):
    """The data module text for certificate `c` under the namespace prefix `tag`."""
    B = c.B
    e = c.emb
    out = [HEADER, "public import KAM.CertificateSharp.V2.Tests.Forced.Format\n\n"]
    out.append("/-!\n# %s\n\n%s\n-/\n\n" % (modname, doc))
    out.append("@[expose] public section\n\nnamespace KAM.CertificateSharp.V2.Forced\n\nopen KAM.Certificate\n\n")
    out.append("namespace %s\n\n" % tag)
    out.append("/-- The parameters. -/\ndef params : CertParams :=\n%s\n\n" % params_lean(c.params))
    out.append("/-- The Hamiltonian. -/\ndef ham : HamExpr 2 :=\n%s\n\n" % wrap("  ", FM.ham_lean(c.toy.ham()).split(" "),
                                                                             indent="    ", sep="", close=""))
    for nm, R, d in (("u", e.angle[0], "angle 0, `u = 2π U` (degree -1)"), ("p", e.action[0], "action 0, `p`"),
                     ("J", e.action[1], "action 1, `J`")):
        out.append(poly_def(nm + "Half", R.half, "the half keys of " + d))
        out.append("\n/-- %s -/\ndef %s : CertRealPoly FB := ⟨⟨%d⟩, %sHalf⟩\n\n" % (d, nm, R.zero, nm))
    for k, E in c.wit.charWit:
        nm = "E%d" % k[0]
        out.append(poly_def(nm + "Terms", E[0], "the character witness `exp(i %d u)`" % k[0]))
        out.append("\n/-- The character witness at the normalized key `(%d, 0)`. -/\n" % k[0])
        out.append("def %s : CertKey × ExpWitness FB := ([%d, 0], ⟨⟨%sTerms⟩, %d, %d⟩)\n\n" % (
            nm, k[0], nm, E[1], E[2]))
    gi = c.gramInv
    for i in range(2):
        for j in range(2):
            out.append(poly_def("B%d%d" % (i, j), gi[i][j], "the Gram inverse, entry `(%d, %d)`" % (i, j)))
            out.append("\n")
    out.append("/-- The torsion inverse. -/\ndef torsInv : List (List (CC FB)) :=\n")
    rows = [wrap("    [", [mant_pair(z) for z in r], indent="     ") for r in c.torsInv]
    out.append("  [" + ",\n".join(r.lstrip() if i == 0 else r for i, r in enumerate(rows)) + "]\n\n")
    out.append("/-- The advice of the full stage. -/\ndef advFull : AdviceBook :=\n%s\n\n" % adv_lean(c.books["cfgFull"]))
    out.append("/-- The advice of the low stage. -/\ndef advLow : AdviceBook :=\n%s\n\n" % adv_lean(c.books["cfgLow"]))
    def qb(x, ind):
        t = q(x)
        if len(t) + len(ind) + 3 <= WIDTH:
            return t
        x = F(x)
        return "(%d /\n%s  %d)" % (x.numerator, ind, x.denominator)
    box = ["(%s,\n    %s)" % (qb(a, "    "), qb(b, "    ")) for a, b in c.freqBox]
    out.append("/-- The frequency box. -/\ndef box : FreqBox :=\n  [%s]\n\n" % ",\n   ".join(box))
    pe = c.piEnc
    W, WH = c.weight, c.weightH
    chars = ", ".join("E%d" % k[0] for k, _ in c.wit.charWit)
    out.append("""/-- The whole certificate. -/
def cert : TorusCertificate 2 FB where
  params := params
  ham := ham
  weightH := ⟨%s, %s⟩
  centre := [%s]
  radius := [%s]
  freqBox := box
  emb := ⟨[-1, 0], [u, ⟨⟨0⟩, []⟩], [0, 0], [p, J]⟩
  weight := ⟨%s, %s⟩
  wit := ⟨[], [], [%s], []⟩
  gramInv := [[⟨B00⟩, ⟨B01⟩], [⟨B10⟩, ⟨B11⟩]]
  torsInv := torsInv
  cfgFull := ⟨%d, %d, %d, fun _ _ => none, advFull⟩
  cfgLow := ⟨%d, %d, %d, fun _ _ => none, advLow⟩
  piEnc := ⟨⟨%d⟩, ⟨%d⟩, %d, %d⟩
  expHalvings := %d
  expOrder := %d

end %s

end KAM.CertificateSharp.V2.Forced

end
""" % (q(WH.rho), q(WH.w), ", ".join(q(x) for x in c.centre), ", ".join(q(x) for x in c.radius), q(W.rho),
       q(W.w), chars, c.cfgFull.cutoff, c.cfgFull.taylorN, c.cfgFull.halvings, c.cfgLow.cutoff, c.cfgLow.taylorN,
       c.cfgLow.halvings, pe.centre, pe.rad, pe.machinK, pe.machinJ, c.expHalvings, c.expOrder, tag))
    text = "".join(out)
    for ln in text.split("\n"):
        assert len(ln) <= WIDTH, ln[:120]
    return text


FORMAT = HEADER + """public import KAM.Certificate.Defs
public import KAM.Certificate.Arith.Fixed
public import KAM.CertificateSharp.Kernel.SegDefs

/-!
# Format of the forced-toy data (V2-TOOLS #6)

The backend `FB = CertFixed %d`, the Fourier term `ft k₀ k₁ re im` (mantissas at `2^-%d`), and
tail-recursive Boolean equalities of model lists and model matrices with their reflection lemmas
(`eq_of_modelsBeq`, `eq_of_matBeq`, `eq_of_optModelsBeq`), used to re-prove each memoized stage
literal by one kernel run.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced

open KAM.Certificate

/-- The backend of the forced toys. -/
abbrev FB : Type := CertFixed %d

/-- A Fourier term: the key `[k₀, k₁]` and the mantissas of the coefficient. -/
def ft (k₀ k₁ re im : ℤ) : CertKey × CC FB := ([k₀, k₁], ⟨⟨re⟩, ⟨im⟩⟩)

section Beq

variable {α : Type} [DecidableEq α]

/-- Tail-recursive equality of model lists. -/
def modelsBeq : List (CertModel α) → List (CertModel α) → Bool
  | [], [] => true
  | a :: as, b :: bs => a.segBeq b && modelsBeq as bs
  | _, _ => false

theorem eq_of_modelsBeq : ∀ {l l' : List (CertModel α)}, modelsBeq l l' = true → l = l'
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [modelsBeq, Bool.and_eq_true] at h
    rw [CertModel.eq_of_segBeq h.1, eq_of_modelsBeq h.2]
  | [], _ :: _, h => by simp [modelsBeq] at h
  | _ :: _, [], h => by simp [modelsBeq] at h

/-- Tail-recursive equality of model matrices (row by row). -/
def matBeq : ModelMatrix α → ModelMatrix α → Bool
  | [], [] => true
  | r :: rs, s :: ss => modelsBeq r s && matBeq rs ss
  | _, _ => false

theorem eq_of_matBeq : ∀ {A B : ModelMatrix α}, matBeq A B = true → A = B
  | [], [], _ => rfl
  | r :: rs, s :: ss, h => by
    simp only [matBeq, Bool.and_eq_true] at h
    rw [eq_of_modelsBeq h.1, eq_of_matBeq h.2]
  | [], _ :: _, h => by simp [matBeq] at h
  | _ :: _, [], h => by simp [matBeq] at h

/-- Equality of an optional model list with a literal one. -/
def optModelsBeq : Option (List (CertModel α)) → List (CertModel α) → Bool
  | some l, l' => modelsBeq l l'
  | none, _ => false

theorem eq_of_optModelsBeq {o : Option (List (CertModel α))} {l : List (CertModel α)}
    (h : optModelsBeq o l = true) : o = some l := by
  cases o with
  | none => simp [optModelsBeq] at h
  | some l₀ => rw [eq_of_modelsBeq (l := l₀) h]

end Beq

end KAM.CertificateSharp.V2.Forced

end
"""


def format_text(P):
    return FORMAT % (P, P, P)
