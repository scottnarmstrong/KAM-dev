#!/usr/bin/env python3
"""Write the SO frozen files from FREEZE-PROPOSAL-2 §1 (+ proposal 1 §1.1-1.8) with D46/D48 literals."""
from pathlib import Path
import sys
import textwrap


def fill(t):
    return textwrap.fill(t.replace("\n", " "), 100, break_on_hyphens=False, break_long_words=False)


def split_long(txt):
    """D-SOF-5: in an approved line over 100 characters, replace exactly one space (the last one at
    or before column 100 outside a code span) by a newline; nothing else changes."""
    out = []
    for l in txt.split("\n"):
        if len(l) > 100:
            k = max(i for i in range(101) if l[i] == " " and l[:i].count("`") % 2 == 0)
            out += [l[:k], l[k + 1:]]
        else:
            out.append(l)
    return "\n".join(out)

root = Path(sys.argv[1])
COPY = """/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
"""
APPROVAL = ("Owner-approved on 2026-10-31 (decision D40, docs/tracks/SO/FREEZE-PROPOSAL-2.md; literals D46 and\n"
            "D48). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an\n"
            "owner-approved versioned successor.")
NC = "@[expose] public noncomputable section"
PS = "@[expose] public section"
F = "KAM.Frozen.SpinOrbit.Defs."
defs = {
 "SoEcc": ("soEcc", ["Mathlib.Basic.Real.Basic"], NC, None,
  "/-- The eccentricity `e_* = 549/10000` of the lunar model. -/\ndef soEcc : ℝ := 549 / 10000"),
 "SoEps": ("soEps", ["Mathlib.Basic.Real.Basic"], NC, None,
  "/-- The asphericity parameter `ε_* = 69/200000` (`ε = (3/2)(B − A)/C`) of the lunar model. -/\n"
  "def soEps : ℝ := 69 / 200000"),
 "SoCoeffPoly": ("soCoeffPoly", ["Mathlib.Algebra.Field.Basic"], NC, None,
  "/-- The coefficient polynomials `A_m(e)` of the model (zero outside `1 ≤ m ≤ 7`); `A_m = W(m/2, e)/2`\n"
  "in Celletti's notation (eq. (7.55)). -/\n"
  "def soCoeffPoly {R : Type*} [Field R] (e : R) : ℕ → R\n"
  "  | 1 => -e / 4 + e ^ 3 / 32\n"
  "  | 2 => 1 / 2 - 5 * e ^ 2 / 4 + 13 * e ^ 4 / 32\n"
  "  | 3 => 7 * e / 4 - 123 * e ^ 3 / 32\n"
  "  | 4 => 17 * e ^ 2 / 4 - 115 * e ^ 4 / 12\n"
  "  | 5 => 845 * e ^ 3 / 96 - 32525 * e ^ 5 / 1536\n"
  "  | 6 => 533 * e ^ 4 / 32\n"
  "  | 7 => 228347 * e ^ 5 / 7680\n"
  "  | _ => 0"),
 "SoA": ("soA", [F + "SoEcc", F + "SoCoeffPoly"], NC, None,
  "/-- `A_m(e_*)` as a real number. -/\ndef soA (m : ℕ) : ℝ := soCoeffPoly soEcc m"),
 "SoModes": ("soModes", ["Mathlib.Order.Interval.Finset.Nat"], PS, None,
  "/-- The index set `{1, …, 7}` of the seven forcing modes. -/\ndef soModes : Finset ℕ := Finset.Icc 1 7"),
 "SoV": ("soV", ["Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic", F + "SoEps", F + "SoA", F + "SoModes"],
  NC, "open Real",
  "/-- The period-one potential `V(q, φ) = -ε_* Σ_{m=1}^7 A_m(e_*) cos (2π (2q - mφ))`\n"
  "(`q` spin angle, `φ` orbital phase, both in turns). -/\n"
  "def soV (q φ : ℝ) : ℝ :=\n"
  "  -soEps * ∑ m ∈ soModes, soA m * Real.cos (2 * π * (2 * q - m * φ))"),
 "SoField": ("soField", ["Mathlib.Analysis.Calculus.Deriv.Basic", F + "SoV"], NC, None,
  "/-- The physical spin–orbit vector field on `(q, p, φ)`: `q̇ = p`, `ṗ = -∂_q V`, `φ̇ = 1`.\n"
  "Time is measured in orbital periods and `p` is the spin rate divided by the orbital mean motion. -/\n"
  "def soField (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=\n"
  "  (x.2.1, -deriv (fun s => soV s x.2.2) x.1, 1)"),
 "SoBarrier": ("SoBarrier", ["Mathlib.Order.Interval.Set.OrdConnected", F + "SoField"], NC, None,
  "/-- An invariant barrier graph `p = P(q, φ)` of the physical flow with values in `[lo, hi]`:\n"
  "continuous, 1-periodic in both angles, and invariant (a solution on an interval that meets the\n"
  "graph once stays on it). -/\n"
  "structure SoBarrier (lo hi : ℝ) where\n"
  "  P : ℝ → ℝ → ℝ\n"
  "  continuous : Continuous fun x : ℝ × ℝ => P x.1 x.2\n"
  "  periodic_q : ∀ q φ, P (q + 1) φ = P q φ\n"
  "  periodic_φ : ∀ q φ, P q (φ + 1) = P q φ\n"
  "  invariant : ∀ (J : Set ℝ) (y : ℝ → ℝ × ℝ × ℝ), J.OrdConnected →\n"
  "    (∀ t ∈ J, HasDerivAt y (soField (y t)) t) →\n"
  "    ∀ t₁ ∈ J, (y t₁).2.1 = P (y t₁).1 (y t₁).2.2 → ∀ t ∈ J, (y t).2.1 = P (y t).1 (y t).2.2\n"
  "  lower : ∀ q φ, lo ≤ P q φ\n"
  "  upper : ∀ q φ, P q φ ≤ hi"),
 "LunarPLo": ("lunarPLo", ["Mathlib.Data.Rat.Init"], PS, None,
  "/-- Lower end of the certified initial momentum window (ruling O1). -/\ndef lunarPLo : ℚ := 9934 / 10000"),
 "LunarPHi": ("lunarPHi", ["Mathlib.Data.Rat.Init"], PS, None,
  "/-- Upper end of the certified initial momentum window (ruling O1). -/\ndef lunarPHi : ℚ := 10066 / 10000"),
}
for stem, (name, imps, sec, op, body) in defs.items():
    kw = "structure" if name == "SoBarrier" else "definition"
    txt = (COPY + "module\n\n" + "".join(f"public import {i}\n" for i in imps) +
           f"\n/-!\n# Frozen {kw} `KAM.SpinOrbit.{name}`\n\n{APPROVAL}\n-/\n\n{sec}\n\n" +
           (f"{op}\n\n" if op else "") +
           f"namespace KAM.SpinOrbit\n\n{body}\n\nend KAM.SpinOrbit\n\nend\n")
    txt = split_long(txt)
    p = root / f"KAM/Frozen/SpinOrbit/Defs/{stem}.lean"
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(txt)

thms = {
 "LunarBarriers": ("lunar_barriers", ["SoBarrier", "LunarPLo", "LunarPHi"],
  "/-- **Theorem A (continuous form).** In the seven-mode lunar spin–orbit model there are two invariant\n"
  "continuous barrier graphs with values in the band `[0.97245, 1.02755]`, the lower one strictly below the\n"
  "window end `lunarPLo` and the upper one strictly above `lunarPHi`. -/\n"
  "theorem lunar_barriers :\n"
  "    ∃ (Bm : SoBarrier (97245 / 100000) (102755 / 100000))\n"
  "      (Bp : SoBarrier (97245 / 100000) (102755 / 100000)),\n"
  "      (∀ q φ, Bm.P q φ < Bp.P q φ) ∧\n"
  "      (∀ q φ, Bm.P q φ < lunarPLo) ∧ (∀ q φ, (lunarPHi : ℝ) < Bp.P q φ) :="),
 "LunarSpinConfinement": ("lunar_spin_confinement", ["SoField", "LunarPLo", "LunarPHi"],
  "/-- **Theorem B.** In the seven-mode lunar spin–orbit model, every initial state `(q₀, p₀, φ₀)` with\n"
  "`lunarPLo < p₀ < lunarPHi` (any angles) has a global solution, unique among global solutions, and its\n"
  "spin rate satisfies `|p(t) − 1| ≤ 2755/100000` (2.755 %) for all real `t`. -/\n"
  "theorem lunar_spin_confinement (q₀ p₀ φ₀ : ℝ) (hp : (lunarPLo : ℝ) < p₀ ∧ p₀ < lunarPHi) :\n"
  "    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧\n"
  "      (∀ t, |(z t).2.1 - 1| ≤ 2755 / 100000) ∧\n"
  "      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →\n"
  "        y = z :="),
 "LunarWindow": ("lunarPLo_lt_lunarPHi", ["LunarPLo", "LunarPHi"],
  "/-- The initial momentum window of `lunar_spin_confinement` is nonempty. -/\n"
  "theorem lunarPLo_lt_lunarPHi : lunarPLo < lunarPHi :="),
}
for stem, (name, imps, body) in thms.items():
    txt = (COPY + "-- FROZEN_ANCHOR_PREFIX_BEGIN\nmodule\n\n" +
           "".join(f"public import {F}{i}\n" for i in imps) +
           f"import KAM.Provider.SpinOrbit.{stem}\n\n"
           f"/-!\n# Frozen theorem `KAM.SpinOrbit.{name}`\n\n" + fill(APPROVAL + f" Only the proof body between the markers may change, and only to `by exact KAM.Provider.SpinOrbit.{name} …` when the provider `KAM.Provider.SpinOrbit.{stem}` is complete (sealing).") + f"\n-/\n\n{PS}\n\nnamespace KAM.SpinOrbit\n\n"
           f"{body}\n  -- FROZEN_ANCHOR_PROOF_BEGIN\n  by sorry\n  -- FROZEN_ANCHOR_PROOF_END\n"
           "-- FROZEN_ANCHOR_SUFFIX_BEGIN\n\nend KAM.SpinOrbit\n\nend\n-- FROZEN_ANCHOR_SUFFIX_END\n")
    txt = split_long(txt)
    p = root / f"KAM/Frozen/SpinOrbit/Theorems/{stem}.lean"
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(txt)
    prov = (COPY + "module\n\n/-!\n" f"# Provider for the frozen theorem `KAM.SpinOrbit.{name}`\n\n" +
            fill(f"The proof of `KAM.SpinOrbit.{name}` is assembled here as `KAM.Provider.SpinOrbit.{name}`, from landed results only. While the frozen anchor is `DRAFT_SORRY`, this module is quarantined: no module other than the anchor may import it.") + "\n-/\n")
    pp = root / f"KAM/Provider/SpinOrbit/{stem}.lean"
    pp.parent.mkdir(parents=True, exist_ok=True)
    pp.write_text(prov)
