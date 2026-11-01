# Track LP: freeze proposal, DRAFT 8 (the LP3 delta on top of the D62 freeze)

Status: 2026-11-01. **Draft 8 is not approved; nothing of it is frozen.** Draft 7 revision 1 is frozen and sealed on
`main` (`f46b94fb`, decision D62; record [FREEZE.md](FREEZE.md)): 89 definitions, 34 characterization theorems and 5
anchors (LP0, LP1, LP1-H, LP2, LP2-H). Draft 8 is a **delta document**: it adds the two LP3 anchors and changes no
frozen file. This revision (package LP-FREEZE8R) **regenerates draft 8 against the frozen definitions**: every text is
derived from the frozen LP1 / LP2 files themselves, every import is a real frozen definition module, and every check
runs against the real modules (no stand-in, no simulated environment). The two anchor texts come out byte-identical to
the first draft-8 run (LP-FREEZE8); only the manifest entries' `source.revision` changes (the regeneration base).
Draft 8 follows draft 7's conventions exactly (file form, paths, namespaces, provider names, manifest fields,
docstring template). Like draft 7 it is written under the rulings of D59; LP3 itself was started under D56's
strongest-version mandate (OD-12) and consumes the sealed `KAM.Nekhoroshev.partialConvex_nekhoroshev` under D58
(OD-13). root-b8 (2026-11-01): "LP3 is not in draft 7. … when LP3-PS and LP3-SP-SAFE are proved and audited, propose
its anchors as a separate delta (draft 8)." Both are proved, and the package audit LP-W5C-1 passed with all three
components PASS ([audit](audits/LP-W5C-audit-1.md)). This text goes to its independent statement audit
([AUDIT-DRAFT8-BRIEF.md](freeze/AUDIT-DRAFT8-BRIEF.md)) and then to the owner for approval of the exact text, before
anything enters `KAM/Frozen/` or `manifest/`. D62: "Not covered: draft 8 (the LP3 anchors) needs its own approval."

Source: [`source/MAIN.md`](source/MAIN.md) (sha256 `68e9167f…48c1b`) as amended by
[`source/AMENDMENTS.md`](source/AMENDMENTS.md) (sha256 `c887d1e2…51881`), cited as `LP:MAIN <item> (<lines>)`, with
the LP3 proof plan [`lp3/LP3-PLAN.md`](lp3/LP3-PLAN.md) §1 (targets) and §2–§4 (the replaced drift supplier). MAIN
states the nonresonant theorems T15/T19; it leaves the resonance-tolerant upgrade as separate work (`LP:MAIN 616`).
LP3 keeps every MAIN lemma used by LP1/LP2 except the drift supplier L12–L13 (381–467), which is replaced by the
sealed partial-convexity Nekhoroshev theorem (LP3-PLAN §0, §2; LP-W5C-1).

**What is approved, exactly.** The approval object of draft 8 is the set of 2 frozen file texts under
[`freeze/draft8/`](freeze/draft8/) (path `freeze/draft8/<frozen path>.txt`), together with the manifest entry drafts
[`freeze/draft8/manifest-entries.json`](freeze/draft8/manifest-entries.json). Every Lean code block in §3 is a
byte-identical excerpt of those files (re-checked by script). At freeze, fill `<APPROVAL-DATE>` and `<DECISION>` in each
module docstring, fill the manifest's `author_approval`, extend each `split_policy.ruling_ref` with the exact-text
approval decision, and compute every `TBD at freeze` hash; all other approved declaration bytes remain unchanged.
Draft 8 is installed **already sealed, in one pass**, like D62 (§6).

**Counts.** 2 theorem anchors (LP3-1, LP3-2); **0 new definitions; 0 new characterization theorems**. The two texts
import 57 frozen definition files directly (distinct): 42 D62 LP definitions (LP3-1: 17, LP3-2:
29) and 15 earlier frozen definitions, of which two are new to the LP texts: the track-P exponents
`KAM.Planetary.planetaryTimeExponent` and `KAM.Planetary.planetaryDriftExponent` (frozen under D25). Each text imports
the frozen LP1 / LP2 file's definition modules minus `KAM.Frozen.Defs.IsDiophantine`, plus the two exponent files.

**Derived from the frozen LP1 / LP2.** LP3-1 is the frozen
`KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafety.lean` statement (LP1), and LP3-2 the frozen
`KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafety.lean` statement (LP2, with its F1 form:
`∀ hμ : 0 < μ` and the source-facing barycentric maps), each with exactly the three LP3 changes of LP3-PLAN §1.2 and the
new name. The generator reads the frozen files (git blob equal on this tree, `main` and `f46b94fb`; prefix and suffix
hashes equal to their SEALED manifest entries, computed with the guard's own split and digest), applies the three
changes by asserted substitutions, and checks the result against the proved implementation statements
`lp3_{planar,spatial}_strongAMD_safety_source` (whitespace-normalized equality). The token-level difference from LP1 /
LP2 is listed in the verification record (§1) and is exactly: the name; `γ τ`, `hγ`, `hτ` and the Diophantine premise
removed; the time exponent; `Real.sqrt μ` → `μ ^ planetaryDriftExponent n` three times.

**Verification** (commands and full outputs in [`freeze/verification-draft-8.txt`](freeze/verification-draft-8.txt)):
- **(a) Text elaborates:** each file with only its provider import removed, i.e. importing exactly its frozen
  definition modules (real oleans): 2/2 exit 0; and each file byte for byte (its staged provider is built): 2/2 exit 0.
  The only message is the expected "declaration uses `sorry`" warning, one per file.
- **(b) Bodies equal:** not applicable (no new definition).
- **(c) Verification:** both anchors, stated verbatim in their real namespaces, close by `exact` of the proved
  implementation theorem. LP3-1's elaborated type is Expr-equal to `lp3_planar_strongAMD_safety_source`'s; LP3-2's is
  Expr-equal to `lp3_spatial_strongAMD_safety_source`'s after delta-expanding exactly the two frozen source barycentric
  maps (the implementation uses the raw maps, which they are by `rfl`; frozen LP2's provider instead applies a
  restated source-map theorem, `lp2_spatial_strongAMD_safety_source_isDiophantine`). `#print axioms`:
  exactly `[propext, Classical.choice, Quot.sound]` for both.
- **Closure:** Lean's constant closure of the two anchors has 104 definitions = 81 D62 LP definitions + 23
  earlier frozen ones; of the closing implementation theorems 102 = 79 + 23. **Every member is frozen; 0 new
  definitions.**
- **Seal (one pass):** a dry run of the D62 install scripts on a scratch export of the committed tree
  (`lp_freeze_install.py --sealed`, `lp_manifest_add.py`, the frozen-anchor guard, the root generator) passes; the
  sealed files differ from the draft texts only in the two placeholders and the body; each sealed file elaborates with no
  message; anchor and provider types are Expr-equal (`#sameDecl`, `#typeEqv`, `example : type_of% @X := @Pv`); axioms
  of both anchors and both providers are exactly `[propext, Classical.choice, Quot.sound]`.

## 1. The rulings in the text

| Ruling | Where it shows in the LP3 text |
|---|---|
| **D59, OD-1** `C = ΣΛ − |L|`, no prograde premise | As LP1/LP2: `sourceStrongAMD` (planar), `spatialSourceStrongAMD` (spatial). No sign, prograde, inclination, alignment, `L ≠ 0` or secular premise. |
| **D59, OD-2 + OD-11 (b)** source carriers | As LP1/LP2, unchanged: thresholds only through `orderedStrongThreshold hn ⟨_, h⟩`; strong AMD, canonical annulus radii and osculating elements only through the `source*` / `spatialSource*` restrictions; every carrier membership is a typing binder (`h₀`) or an existential output (`∃ hcht`, `∃ hs`, `∃ ho`). |
| **D59, OD-3** `max ν = 1` kept | `hνmax : ∃ i, ν i = 1`, `hνle : ∀ i, ν i ≤ 1`, as in LP1/LP2. They are unused by the proof; the general-mass versions `lp3_planar_strongAMD_safety_source_general`, `lp3_spatial_strongAMD_safety_source_general` stay ordinary theorems. |
| **D59, OD-4** τ free, plus τ = n − 1/2 | Not applicable: LP3 has no `γ`, `τ` and no Diophantine premise, so there is no `τ`-corollary (no LP3-H). |
| **D59, OD-5 + OD-9** crossing notion | As LP1/LP2, unchanged: canonical annuli, star and all pair distances, actual-velocity osculating annuli with half gaps; the N10 inequalities `Aosc * μ₀ ≤ dStar / 2`, `2 * (Aosc * μ₀) ≤ dPair / 2` are displayed outputs. |
| **Draft-7 audit F1** (frozen LP2 form, D62) | LP3-2 binds `∀ hμ : 0 < μ` and uses the frozen `spatialSourceBarycentricPositions ν μ hν hμ`, `spatialSourceBarycentricVelocities ν μ hν hμ`, exactly as the frozen LP2. These proof arguments add no premise. LP3-1 uses the frozen planar maps, as the frozen LP1. |
| **D59, OD-6** new anchors only | Both anchors are new; `KAM.Planetary.planetaryExponentialSafety` (P-EXP-SAFE) and every existing frozen file are untouched. |
| **D56 / OD-12** strongest version | LP3 is the stretch goal "sharp threshold without arithmetic hypothesis". |
| **D58 / OD-13** sealed-anchor import | The closing theorems import the **sealed** frozen `KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev` (never its provider). The anchor texts themselves do not mention it. |
| **LP3-PLAN O-1** exponent names | The frozen track-P names `planetaryTimeExponent n`, `planetaryDriftExponent n` (the plan's recommendation; definitionally the `partial*` exponents, bridges `planetaryTimeExponent_eq_partial`, `planetaryDriftExponent_eq_partial` in `KAM/Planetary/Exponential/Stopped.lean`). |
| **LP3-PLAN O-3** anchors or not | Answered by root-b8 (2026-11-01): anchors, as this separate delta. |

## 2. Anchors

| Id | Lean name | Frozen path | Provider (module; export) | Closed by (implementation theorem; module) | MAIN |
|---|---|---|---|---|---|
| LP3-1 | `KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_noArith` | `KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafetyNoArith.lean` | `KAM.Provider.Planetary.StrongAMD.PlanarStrongAMDExponentialSafetyNoArith`; `KAM.Provider.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_noArith` | `KAM.Planetary.StrongAMD.lp3_planar_strongAMD_safety_source`; `KAM.Planetary.StrongAMD.Nek.PlanarSafety.Source` | T15 (502–506) with §1 (6)–(9) (69–93) without (5), L14 (468–500), L16 (508–529); N8, N10; drift supplier L12–L13 (381–467) replaced by the sealed partialConvex_nekhoroshev (LP3-PLAN §1–§2) |
| LP3-2 | `KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety_noArith` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafetyNoArith.lean` | `KAM.Provider.Planetary.Spatial.SpatialStrongAMDExponentialSafetyNoArith`; `KAM.Provider.Planetary.Spatial.spatial_strongAMD_exponentialSafety_noArith` | `KAM.Planetary.Spatial.lp3_spatial_strongAMD_safety_source`; `KAM.Planetary.Spatial.Nek.SpatialSafety.Source` | T19 (599–603) with §1 (6)–(9) (69–93) without (5), L14 (468–500), L16 (508–529), d = 3; drift supplier L12–L13 (381–467) replaced by the sealed partialConvex_nekhoroshev (LP3-PLAN §1–§2) |

Paths, namespaces and providers follow draft 7 (frozen path and provider path mirror the namespace; file name =
CamelCase of the declaration name). Each anchor is sealed by the one-line body `by exact <provider export> hn ν hν hνmax
hνle A hA hAord δ hδ` (the anchor guard's sealed-body rule); each provider is a one-line application of the proved
implementation theorem in the "Closed by" column.

**Names.** `planar_strongAMD_exponentialSafety_noArith` and `spatial_strongAMD_exponentialSafety_noArith` (suffix
suggested by the package brief). Justification:
- the suffix names the one property that distinguishes LP3 from LP1/LP2 in the statement: **no arithmetic
  (Diophantine) hypothesis** (the wording of D56, OD-12 and LP3-PLAN's title); the common prefix keeps the four
  safety anchors together (`…_exponentialSafety`, `…_halfInteger`, `…_noArith`);
- `…_resonant` / `…_nonresonant` are avoided: MAIN calls T15/T19 "nonresonant", and LP3 is not a statement about
  resonant states only; `…_uniform` is ambiguous (LP1 is also uniform in the initial state, for fixed `γ, τ`);
  `…_nekhoroshev` names the proof method, not the content, and evokes the `KAM.Nekhoroshev` namespace;
- the names are new: no clash with any draft-7 name, any existing frozen name, or a Mathlib declaration (the generator
  asserts the draft-7/frozen part; `grep` finds no `noArith` in `KAM/` or Mathlib).
Alternatives, if the owner prefers: `…_noArithmetic`, `…_noDiophantine`.

## 3. Anchor texts (exact)

Each block is the declaration region of the frozen file (from `namespace` to the end marker of the proof body).

### 3.1 LP3-1: planar strong-AMD exponential safety with no arithmetic hypothesis

```lean
namespace KAM.Planetary.StrongAMD

/-- **LP3-1** (`LP:MAIN T15 (502–506) with §1 (6)–(9) (69–93) without (5), L14 (468–500), L16
(508–529); N8, N10; drift supplier L12–L13 (381–467) replaced by the sealed
partialConvex_nekhoroshev (LP3-PLAN §1–§2)`): planar strong-AMD exponential safety with no
arithmetic hypothesis (time exponent `planetaryTimeExponent n`, drift exponent
`planetaryDriftExponent n`). -/
theorem planar_strongAMD_exponentialSafety_noArith {n : ℕ} (hn : 2 ≤ n) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i) (hνmax : ∃ i, ν i = 1) (hνle : ∀ i, ν i ≤ 1)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 2),
        (∀ i, 0 < planeLength (bodyVector z₀.1 i) ∧ keplerEnergy ν z₀ i < 0) →
        (fun i => keplerAxis ν z₀ i) ∈ A →
        ∀ hch : (fun i => keplerAction ν z₀ i) ∈ chamber ν,
        ∀ h₀ : (∀ i, 0 < ν i) ∧
          ∀ i, 0 < planeLength (bodyVector z₀.1 i) ∧ keplerEnergy ν z₀ i < 0,
        sourceStrongAMD (⟨z₀, h₀⟩ : SourceCanonicalPhase n ν) ≤
          orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        let T := T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n))
        ∃ z : ℝ → Phase (n * 2), z 0 = z₀ ∧
          IsMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
          MovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
          IsNewtonSolutionOn (actualMasses 1 ν μ) (Set.Icc (-T) T)
            (fun t => barycentricPositions 1 ν μ (z t).1)
            (fun t => barycentricVelocities 1 ν μ (z t).2) ∧
          ∀ t ∈ Set.Icc (-T) T,
            (∀ i, 0 < planeLength (bodyVector (z t).1 i) ∧ keplerEnergy ν (z t) i < 0) ∧
            (∃ hcht : (fun i => keplerAction ν (z t) i) ∈ chamber ν,
              ∃ hs : (∀ i, 0 < ν i) ∧
                ∀ i, 0 < planeLength (bodyVector (z t).1 i) ∧ keplerEnergy ν (z t) i < 0,
              sourceStrongAMD (⟨z t, hs⟩ : SourceCanonicalPhase n ν) ≤
                orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2) ∧
            ‖(fun i => keplerAction ν (z t) i) - fun i => keplerAction ν z₀ i‖ ≤
              AΛ * μ ^ planetaryDriftExponent n ∧
            ‖(fun i => keplerAxis ν (z t) i) - fun i => keplerAxis ν z₀ i‖ ≤
              Aa * μ ^ planetaryDriftExponent n ∧
            (∃ hs : (∀ i, 0 < ν i) ∧
                ∀ i, 0 < planeLength (bodyVector (z t).1 i) ∧ keplerEnergy ν (z t) i < 0,
              |sourceStrongAMD (⟨z t, hs⟩ : SourceCanonicalPhase n ν) -
                  sourceStrongAMD (⟨z₀, h₀⟩ : SourceCanonicalPhase n ν)| ≤
                n * AΛ * μ ^ planetaryDriftExponent n) ∧
            (∀ i, dStar ≤ keplerAxis ν (z t) i *
              (1 - planeLength (keplerEccVector ν (z t) i))) ∧
            (∀ a : AdjIdx n, dPair ≤ keplerAxis ν (z t) a.upperIdx *
                (1 - planeLength (keplerEccVector ν (z t) a.upperIdx)) -
                keplerAxis ν (z t) a.1 * (1 + planeLength (keplerEccVector ν (z t) a.1))) ∧
            (∀ i, dStar ≤ planeLength (bodyVector (z t).1 i)) ∧
            (∀ i j, i ≠ j → dPair ≤ planeLength (bodyVector (z t).1 i - bodyVector (z t).1 j)) ∧
            (∃ hs : (∀ i, 0 < ν i) ∧
                ∀ i, 0 < planeLength (bodyVector (z t).1 i) ∧ keplerEnergy ν (z t) i < 0,
             ∃ ho : (∀ i, 0 < ν i) ∧ 0 < μ ∧
                ∀ i, 0 < planeLength (bodyVector (z t).1 i) ∧
                  oscEnergy ν μ (z t) i < 0 ∧ oscEcc ν μ (z t) i < 1,
              (∀ i, sourceOscEnergy (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i < 0 ∧
                  0 < sourceOscAxis (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i ∧
                  sourceOscEcc (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i < 1 ∧
                  sourceOscPeri (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i ≤
                    planeLength (bodyVector (z t).1 i) ∧
                  planeLength (bodyVector (z t).1 i) ≤
                    sourceOscApo (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i ∧
                  |sourceOscAxis (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i -
                      keplerAxis ν (z t) i| +
                    planeLength (sourceOscEccVector (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i -
                      keplerEccVector ν (z t) i) ≤ Aelem * μ) ∧
              (∀ i, |sourceOscPeri (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i -
                      sourceKeplerPeri (⟨z t, hs⟩ : SourceCanonicalPhase n ν) i| ≤ Aosc * μ ∧
                  |sourceOscApo (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i -
                      sourceKeplerApo (⟨z t, hs⟩ : SourceCanonicalPhase n ν) i| ≤ Aosc * μ) ∧
              (∀ i, dStar / 2 ≤
                  sourceOscPeri (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) i) ∧
              (∀ a : AdjIdx n, dPair / 2 ≤
                  sourceOscPeri (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) a.upperIdx -
                    sourceOscApo (⟨z t, ho⟩ : SourceOsculatingPhase n ν μ) a.1)) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
```

Reading: for fixed positive masses normalized by `max ν = 1`, a compact set `A` of ordered axis vectors and a
margin `δ > 0`, the constants `μ₀, c, T₀, A_Λ, A_a, d⋆, d_pair, A_osc, A_elem` (with the N10 inequalities) are chosen
before `μ` and the initial state, and depend only on `(n, ν, A, δ)`. For every `0 < μ ≤ μ₀` and **every** initial
state with nonzero positions, negative Kepler energies, axes in `A`, actions in the chamber and strong AMD
`≤ B(Λ) − δ` (resonant mean motions included), the unique moving solution exists on `[−T, T]` with
`T = T₀ exp(c μ^(−a_n))`, `a_n = planetaryTimeExponent n = 2/(6n² − 3n + 14)`, reconstructs the Newtonian `(1+n)`-body
motion, and along it: ellipticity, chamber membership with strong AMD `≤ B − δ/2`, action and axis drift
`≤ A_Λ μ^(b_n)`, `≤ A_a μ^(b_n)` with `b_n = planetaryDriftExponent n = 3/(6n² − 3n + 14)`, AMD drift
`≤ n A_Λ μ^(b_n)`, canonical perihelia `≥ d⋆` and adjacent annulus gaps `≥ d_pair`, all star and pair distances, and
valid actual-velocity osculating ellipses through the current position with L16's element error `≤ A_elem μ`,
endpoint errors `≤ A_osc μ` and half gaps.

The text is the frozen LP1 statement (D62) with exactly the three LP3 changes of LP3-PLAN §1.2 and the anchor
name (unified diff against the frozen file's statement; the substitutions are asserted by the generator, and the
result equals the proved implementation statement up to whitespace; the two drift lines are re-broken to stay
within 100 columns):

```diff
--- frozen KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafety.lean
+++ draft 8 KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafetyNoArith.lean
@@ -1,2 +1,2 @@
-theorem planar_strongAMD_exponentialSafety {n : ℕ} (hn : 2 ≤ n) (ν : Fin n → ℝ)
+theorem planar_strongAMD_exponentialSafety_noArith {n : ℕ} (hn : 2 ≤ n) (ν : Fin n → ℝ)
     (hν : ∀ i, 0 < ν i) (hνmax : ∃ i, ν i = 1) (hνle : ∀ i, ν i ≤ 1)
@@ -4,3 +4,3 @@
     (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
-    (δ γ τ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) (hτ : (n : ℝ) - 1 < τ) :
+    (δ : ℝ) (hδ : 0 < δ) :
     ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
@@ -12,3 +12,2 @@
         (fun i => keplerAxis ν z₀ i) ∈ A →
-        KAM.IsDiophantine γ τ (fun i => ν i ^ 3 / keplerAction ν z₀ i ^ 3) →
         ∀ hch : (fun i => keplerAction ν z₀ i) ∈ chamber ν,
@@ -18,3 +17,3 @@
           orderedStrongThreshold hn ⟨_, hch⟩ - δ →
-        let T := T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1)))))
+        let T := T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n))
         ∃ z : ℝ → Phase (n * 2), z 0 = z₀ ∧
@@ -32,4 +31,6 @@
                 orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2) ∧
-            ‖(fun i => keplerAction ν (z t) i) - fun i => keplerAction ν z₀ i‖ ≤ AΛ * Real.sqrt μ ∧
-            ‖(fun i => keplerAxis ν (z t) i) - fun i => keplerAxis ν z₀ i‖ ≤ Aa * Real.sqrt μ ∧
+            ‖(fun i => keplerAction ν (z t) i) - fun i => keplerAction ν z₀ i‖ ≤
+              AΛ * μ ^ planetaryDriftExponent n ∧
+            ‖(fun i => keplerAxis ν (z t) i) - fun i => keplerAxis ν z₀ i‖ ≤
+              Aa * μ ^ planetaryDriftExponent n ∧
             (∃ hs : (∀ i, 0 < ν i) ∧
@@ -38,3 +39,3 @@
                   sourceStrongAMD (⟨z₀, h₀⟩ : SourceCanonicalPhase n ν)| ≤
-                n * AΛ * Real.sqrt μ) ∧
+                n * AΛ * μ ^ planetaryDriftExponent n) ∧
             (∀ i, dStar ≤ keplerAxis ν (z t) i *
```

### 3.2 LP3-2: spatial strong-AMD exponential safety with no arithmetic hypothesis (`d = 3`)

```lean
open KAM.Planetary.StrongAMD

namespace KAM.Planetary.Spatial

/-- **LP3-2** (`LP:MAIN T19 (599–603) with §1 (6)–(9) (69–93) without (5), L14 (468–500), L16
(508–529), d = 3; drift supplier L12–L13 (381–467) replaced by the sealed partialConvex_nekhoroshev
(LP3-PLAN §1–§2)`): spatial strong-AMD exponential safety with no arithmetic hypothesis (time
exponent `planetaryTimeExponent n`, drift exponent `planetaryDriftExponent n`). -/
theorem spatial_strongAMD_exponentialSafety_noArith {n : ℕ} (hn : 2 ≤ n) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i) (hνmax : ∃ i, ν i = 1) (hνle : ∀ i, ν i ≤ 1)
    (A : Set (Fin n → ℝ)) (hA : IsCompact A)
    (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
      0 < μ₀ ∧ 0 < c ∧ 0 < T₀ ∧ 0 < AΛ ∧ 0 < Aa ∧ 0 < dStar ∧ 0 < dPair ∧ 0 < Aosc ∧
      0 < Aelem ∧ Aosc * μ₀ ≤ dStar / 2 ∧ 2 * (Aosc * μ₀) ≤ dPair / 2 ∧
      ∀ μ : ℝ, ∀ hμ : 0 < μ, μ ≤ μ₀ →
      ∀ z₀ : Phase (n * 3),
        (∀ i, 0 < spaceLength (bodyVector3 z₀.1 i) ∧ spatialKeplerEnergy ν z₀ i < 0) →
        ∀ h₀ : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 z₀.1 i) ∧
          spatialKeplerEnergy ν z₀ i < 0,
        (fun i => spatialSourceKeplerAxis (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i) ∈ A →
        ∀ hch : (fun i => spatialSourceKeplerAction
            (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i) ∈ chamber ν,
        spatialSourceStrongAMD (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) ≤
          orderedStrongThreshold hn ⟨_, hch⟩ - δ →
        let T := T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n))
        ∃ z : ℝ → Phase (n * 3), z 0 = z₀ ∧
          IsSpatialMovingSolutionOn ν μ (Set.Icc (-T) T) z ∧
          SpatialMovingUniqueOn ν μ (Set.Icc (-T) T) z ∧
          IsSpatialNewtonSolutionOn (spatialMasses ν μ) (Set.Icc (-T) T)
            (fun t => spatialSourceBarycentricPositions ν μ hν hμ (z t).1)
            (fun t => spatialSourceBarycentricVelocities ν μ hν hμ (z t).2) ∧
          ∀ t ∈ Set.Icc (-T) T,
            ∃ hs : ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 (z t).1 i) ∧
                spatialKeplerEnergy ν (z t) i < 0,
            ∃ hcht : (fun i => spatialSourceKeplerAction
                (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) ∈ chamber ν,
            spatialSourceStrongAMD (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) ≤
                orderedStrongThreshold hn ⟨_, hcht⟩ - δ / 2 ∧
            ‖(fun i => spatialSourceKeplerAction (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) -
                fun i => spatialSourceKeplerAction (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i‖ ≤
              AΛ * μ ^ planetaryDriftExponent n ∧
            ‖(fun i => spatialSourceKeplerAxis (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) -
                fun i => spatialSourceKeplerAxis (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i‖ ≤
              Aa * μ ^ planetaryDriftExponent n ∧
            |spatialSourceStrongAMD (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) -
                spatialSourceStrongAMD (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν)| ≤
              n * AΛ * μ ^ planetaryDriftExponent n ∧
            (∀ i, dStar ≤
                spatialSourceKeplerPeri (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) ∧
            (∀ a : AdjIdx n, dPair ≤
                spatialSourceKeplerPeri (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) a.upperIdx -
                  spatialSourceKeplerApo (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) a.1) ∧
            (∀ i, dStar ≤ spaceLength (bodyVector3 (z t).1 i)) ∧
            (∀ i j, i ≠ j →
              dPair ≤ spaceLength (bodyVector3 (z t).1 i - bodyVector3 (z t).1 j)) ∧
            ∃ ho : (∀ i, 0 < ν i) ∧ 0 < μ ∧
                ∀ i, 0 < spaceLength (bodyVector3 (z t).1 i) ∧
                  spatialOscEnergy ν μ (z t) i < 0 ∧ spatialOscEcc ν μ (z t) i < 1,
              (∀ i, spatialSourceOscEnergy (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i < 0 ∧
                  0 < spatialSourceOscAxis (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i ∧
                  spatialSourceOscEcc (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i < 1 ∧
                  spatialSourceOscPeri (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i ≤
                    spaceLength (bodyVector3 (z t).1 i) ∧
                  spaceLength (bodyVector3 (z t).1 i) ≤
                    spatialSourceOscApo (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i ∧
                  |spatialSourceOscAxis (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i -
                      spatialSourceKeplerAxis (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i| +
                    spaceLength (spatialSourceOscEccVector
                        (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i -
                      spatialSourceKeplerEccVector
                        (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) ≤ Aelem * μ) ∧
              (∀ i, |spatialSourceOscPeri (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i -
                      spatialSourceKeplerPeri (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i| ≤
                    Aosc * μ ∧
                  |spatialSourceOscApo (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i -
                      spatialSourceKeplerApo (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i| ≤
                    Aosc * μ) ∧
              (∀ i, dStar / 2 ≤
                  spatialSourceOscPeri (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) i) ∧
              (∀ a : AdjIdx n, dPair / 2 ≤
                  spatialSourceOscPeri (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ)
                      a.upperIdx -
                    spatialSourceOscApo (⟨z t, ho⟩ : SpatialSourceOsculatingPhase n ν μ) a.1) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
```

Reading: LP3-1 in dimension three, with LP2's review-4 resolution (A) form and the frozen (D62, F1) source-facing
barycentric maps (their `hν`, `hμ` arguments are the anchor's own premise `hν` and the bound `hμ : 0 < μ`): every canonical element at `z₀` and `z t`
(axis, action, eccentricity vector, strong AMD, perihelion, aphelion) is a `spatialSource*` restriction, `h₀` follows
the physical premise. No prograde, inclination, nonzero-total-angular-momentum, alignment, secular or arithmetic
premise. The exponents are the planar `a_n`, `b_n` (the fast dimension is `n`; the `2n` slow pairs change constants
only; LP3-PLAN §1.3, `LP:MAIN T19 (603)`). The only raw total helpers in the text are, as in LP2,
`spatialKeplerEnergy`, `spatialOscEnergy`, `spatialOscEcc`, each only as a sign condition inside a guarded predicate
(draft 7 §4.4).

The text is the frozen LP2 statement (D62, which already carries the F1 form: the `hμ` binder and the two source
barycentric maps) with exactly the same three LP3 changes and the anchor name (unified diff against the frozen
file's statement; same assertions as for LP3-1):

```diff
--- frozen KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafety.lean
+++ draft 8 KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafetyNoArith.lean
@@ -1,2 +1,2 @@
-theorem spatial_strongAMD_exponentialSafety {n : ℕ} (hn : 2 ≤ n) (ν : Fin n → ℝ)
+theorem spatial_strongAMD_exponentialSafety_noArith {n : ℕ} (hn : 2 ≤ n) (ν : Fin n → ℝ)
     (hν : ∀ i, 0 < ν i) (hνmax : ∃ i, ν i = 1) (hνle : ∀ i, ν i ≤ 1)
@@ -4,3 +4,3 @@
     (hAord : ∀ a ∈ A, (∀ i, 0 < a i) ∧ ∀ i j, i < j → a i < a j)
-    (δ γ τ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) (hτ : (n : ℝ) - 1 < τ) :
+    (δ : ℝ) (hδ : 0 < δ) :
     ∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem : ℝ,
@@ -14,4 +14,2 @@
         (fun i => spatialSourceKeplerAxis (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i) ∈ A →
-        KAM.IsDiophantine γ τ (fun i => ν i ^ 3 /
-            spatialSourceKeplerAction (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i ^ 3) →
         ∀ hch : (fun i => spatialSourceKeplerAction
@@ -20,3 +18,3 @@
           orderedStrongThreshold hn ⟨_, hch⟩ - δ →
-        let T := T₀ * Real.exp (c * μ ^ (-(1 / (2 * (τ + 1)))))
+        let T := T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n))
         ∃ z : ℝ → Phase (n * 3), z 0 = z₀ ∧
@@ -36,9 +34,9 @@
                 fun i => spatialSourceKeplerAction (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i‖ ≤
-              AΛ * Real.sqrt μ ∧
+              AΛ * μ ^ planetaryDriftExponent n ∧
             ‖(fun i => spatialSourceKeplerAxis (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) i) -
                 fun i => spatialSourceKeplerAxis (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν) i‖ ≤
-              Aa * Real.sqrt μ ∧
+              Aa * μ ^ planetaryDriftExponent n ∧
             |spatialSourceStrongAMD (⟨z t, hs⟩ : SpatialSourceCanonicalPhase n ν) -
                 spatialSourceStrongAMD (⟨z₀, h₀⟩ : SpatialSourceCanonicalPhase n ν)| ≤
-              n * AΛ * Real.sqrt μ ∧
+              n * AΛ * μ ^ planetaryDriftExponent n ∧
             (∀ i, dStar ≤
```

### 3.3 What is weaker and what is stronger than LP1 / LP2 (LP3-PLAN §1.4)

| | LP1 / LP2 (frozen, D62) | LP3-1 / LP3-2 (draft 8) |
|---|---|---|
| arithmetic premise | Diophantine `(γ, τ)` at `ω(Λ(z₀))`: the frozen `KAM.IsDiophantine γ τ ω`, `ωᵢ = νᵢ³/Λᵢ³` (option C; `LP:MAIN (5)`) | **none**: every initial state of the sharp sublevel, resonant ones included (**stronger**) |
| data and constants depend on | `(n, ν, A, δ, γ, τ)` | `(n, ν, A, δ)`: uniform over the whole compact sublevel (**stronger**) |
| time | `T₀ exp(c μ^(−1/(2(τ+1))))`; the half-integer choice `1/(2n+1)` at `τ = n − 1/2` (LP1-H, LP2-H) | `T₀ exp(c μ^(−a_n))`, `a_n = 2/(6n² − 3n + 14)` (**weaker**) |
| action / axis / AMD drift | `A_Λ √μ`, `A_a √μ`, `n A_Λ √μ` | `A_Λ μ^(b_n)`, `A_a μ^(b_n)`, `n A_Λ μ^(b_n)`, `b_n = 3/(6n² − 3n + 14) < 1/2` (**weaker**) |
| threshold, margin `δ/2`, separations, osculating annuli, N10, existence/uniqueness, Newtonian reconstruction | sharp `B`, all as stated | identical |

Neither result implies the other. For `n = 2, 3, 4, 5`: `(a_n, b_n) = (1/16, 3/32), (2/59, 3/59), (1/49, 3/98),
(2/149, 3/149)`, against LP1-H/LP2-H's time exponent `1/5, 1/7, 1/9, 1/11` and drift `√μ`. LP3 is also **not
comparable** with track P's frozen `planetaryExponentialSafety` (LP3-PLAN review C2): same exponents, but LP3 covers
the sharp curved sublevel (not an `AMDBox`) and adds the separation and osculating conclusions, while P states
conclusions LP3 does not.

## 4. Definition closure delta

**New definitions: none. New characterization theorems: none.** Lean's constant closure of the two anchors as
elaborated in check (c) (verification §5), against the live manifest:

- closure size: 104 definitions = 81 D62 LP frozen definitions + 23 earlier frozen definitions;
  **0 definitions that are not frozen**;
- of the closing implementation theorems: 102 = 79 + 23, 0 not frozen;
- earlier frozen definitions in the closure: `KAM.Iso.IsHamiltonianSolutionOn`, `KAM.Planetary.IsMovingSolutionOn`, `KAM.Planetary.IsNewtonSolutionOn`, `KAM.Planetary.MovingUniqueOn`, `KAM.Planetary.NoCollision`, `KAM.Planetary.Phase`, `KAM.Planetary.actualMasses`, `KAM.Planetary.barycentricPositions`, `KAM.Planetary.barycentricVelocities`, `KAM.Planetary.bodyVector`, `KAM.Planetary.keplerAction`, `KAM.Planetary.keplerAxis`, `KAM.Planetary.keplerEccVector`, `KAM.Planetary.keplerEnergy`, `KAM.Planetary.movingHamiltonian`, `KAM.Planetary.planeCross`, `KAM.Planetary.planeDot`, `KAM.Planetary.planeLength`, `KAM.Planetary.planeSq`, `KAM.Planetary.planetaryDriftExponent`, `KAM.Planetary.planetaryTimeExponent`, `KAM.Planetary.totalMomentum`, `KAM.hamiltonianVectorField`.

### 4.1 Already-frozen definitions newly referenced (reused unchanged; no new file)

Directly referenced by the draft-8 texts and not by the frozen LP1 / LP2:

- `KAM.Planetary.planetaryDriftExponent` — `KAM/Frozen/Planetary/Defs/PlanetaryDriftExponent.lean`
- `KAM.Planetary.planetaryTimeExponent` — `KAM/Frozen/Planetary/Defs/PlanetaryTimeExponent.lean`

Their frozen texts (track P, owner-approved under D25; excerpts of the existing frozen files):

```lean
/-- Nek77 (12.4), n counts planets, not total canonical pairs. -/
def planetaryTimeExponent (n : ℕ) : ℝ := 2 / (6 * (n : ℝ) ^ 2 - 3 * (n : ℝ) + 14)

/-- Nek77 (12.5). No optimized exponent is asserted. -/
def planetaryDriftExponent (n : ℕ) : ℝ := 3 * planetaryTimeExponent n / 2
```

So `planetaryTimeExponent n = 2/(6n² − 3n + 14)` and `planetaryDriftExponent n = 3 · planetaryTimeExponent n / 2
= 3/(6n² − 3n + 14)`, with `n : ℕ` the number of planets (the number of fast actions), cast to `ℝ`. Both are
literal closed formulas; no carrier or characterization is needed (for `n ≥ 2` the denominator is `≥ 32`).

No longer referenced: `KAM.IsDiophantine` (the frozen LP1 / LP2 import `KAM.Frozen.Defs.IsDiophantine`; LP3 has no
arithmetic premise). The other directly imported earlier frozen definition files are those of LP1 / LP2: LP3-1
`ActualMasses`, `BarycentricPositions`, `BarycentricVelocities`, `BodyVector`, `IsMovingSolutionOn`, `IsNewtonSolutionOn`, `KeplerAction`, `KeplerAxis`, `KeplerEccVector`, `KeplerEnergy`, `MovingUniqueOn`, `Phase`, `PlaneLength`;
LP3-2 `Phase`.

### 4.2 D62 LP definitions used

The texts import 42 distinct D62 LP definition files directly (LP3-1: 17, LP3-2: 29), exactly those the frozen LP1 /
LP2 import (verification §1, whole-file diffs). They are frozen and sealed with their characterization theorems under
D62; draft 8 adds nothing to them and changes none.

- LP3-1: `AdjIdx`, `AdjIdxUpperIdx`, `Chamber`, `OrderedStrongThreshold`, `OscEcc`, `OscEnergy`, `SourceCanonicalPhase`, `SourceKeplerApo`, `SourceKeplerPeri`, `SourceOscApo`, `SourceOscAxis`, `SourceOscEcc`, `SourceOscEccVector`, `SourceOscEnergy`, `SourceOscPeri`, `SourceOsculatingPhase`, `SourceStrongAMD`.
- LP3-2: `BodyVector3`, `IsSpatialMovingSolutionOn`, `IsSpatialNewtonSolutionOn`, `SpaceLength`, `SpatialKeplerEnergy`, `SpatialMasses`, `SpatialMovingUniqueOn`, `SpatialOscEcc`, `SpatialOscEnergy`, `SpatialSourceBarycentricPositions`, `SpatialSourceBarycentricVelocities`, `SpatialSourceCanonicalPhase`, `SpatialSourceKeplerAction`, `SpatialSourceKeplerApo`, `SpatialSourceKeplerAxis`, `SpatialSourceKeplerEccVector`, `SpatialSourceKeplerPeri`, `SpatialSourceOscApo`, `SpatialSourceOscAxis`, `SpatialSourceOscEcc`, `SpatialSourceOscEccVector`, `SpatialSourceOscEnergy`, `SpatialSourceOscPeri`, `SpatialSourceOsculatingPhase`, `SpatialSourceStrongAMD`, `AdjIdx`, `AdjIdxUpperIdx`, `Chamber`, `OrderedStrongThreshold`.

### 4.3 Frozen import closure (manifest `definition_closure`)

Following draft-7 convention 8, `definition_closure` lists the complete transitive closure of frozen definition files
imported, computed with the D62 install's own closure (`lp_manifest_add.closure`) over the real frozen files. For
LP3-1 it is LP1's manifest closure plus the two exponent files (79 files; `IsDiophantine.lean` stays, through the
track-P files). For LP3-2 it is LP2's manifest closure plus 17 files (96 files): the two exponent files and the planar
track-P files that the frozen `PlanetaryTimeExponent.lean` imports (`MovingHamiltonian`, `PairBounds`,
`SecularAverage`, `Fast`, `Slow`, `OscillatorAction`, … and their imports). Those are file-import dependencies only, not
semantic ones: the Lean constant closure (§4 above) adds exactly the two exponents to that of LP1 / LP2.

## 5. Manifest entry drafts

[`freeze/draft8/manifest-entries.json`](freeze/draft8/manifest-entries.json) has one entry per file (2), in the schema
and conventions of draft 7 §6:

- `id` `planetary.d59.<name>.v1`, `contract` `{id: planetary.d59.<name>, version: "1"}`;
- `kind` `theorem`, `path`, `export` as in §2; `implementation` = the provider module and export;
  `state: "DRAFT_SORRY"`, `prefix_sha256`, `suffix_sha256`, `abi_sha256` `"TBD at freeze"`, empty `draft_allowlist`;
- `source.revision` = `KAM-inp@2bbacd66 docs/tracks/LP/source/MAIN.md (sha256 …) as amended by
  docs/tracks/LP/source/AMENDMENTS.md (sha256 …), with the LP3 proof plan docs/tracks/LP/lp3/LP3-PLAN.md (sha256 …);
  exact text docs/tracks/LP/FREEZE-PROPOSAL-DRAFT8.md draft 8` (the regeneration base; the first run had `ced282aa`,
  same three hashes); `source.range` = the MAIN items and lines of §2;
- `split_policy` `NOT_SPLIT`, one source group per entry, `ruling_ref` `docs/DECISIONS.md D59` (extended at freeze by
  the decision that approves the exact text, from the approval record);
- `definition_closure` as in §4.3, `sha256: "TBD at freeze"`;
- `author_approval: "PENDING (D59 approves rulings only)"`; `state` becomes `SEALED` at install (approval record).

## 6. One-pass install (frozen and sealed together, like D62)

There is no new definition, so **no implementation module changes** (no rebase, no moved proof, no renamed theorem),
and both proofs exist. Draft 8 is therefore installed already sealed in one commit, with D62's scripts unchanged,
after the owner's exact-text approval (decision `<DECISION>` on `<APPROVAL-DATE>`) and the dedicated seal audit.

**Exact files of the install** (4 Lean files and the manifest; nothing else under `KAM/Frozen/`, `KAM/Provider/` or
`manifest/`):

| # | File | Kind | Content |
|---|---|---|---|
| 1 | `KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafetyNoArith.lean` | frozen anchor LP3-1 (new) | the approved `.txt` with the two placeholders filled and the sealed body `by exact KAM.Provider.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_noArith hn ν hν hνmax hνle A hA hAord δ hδ` (wrapped at 100 columns, 6-space continuation) |
| 2 | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafetyNoArith.lean` | frozen anchor LP3-2 (new) | the same, with `KAM.Provider.Planetary.Spatial.spatial_strongAMD_exponentialSafety_noArith` |
| 3 | `KAM/Provider/Planetary/StrongAMD/PlanarStrongAMDExponentialSafetyNoArith.lean` | provider (staged on this branch) | `KAM.Provider.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_noArith`: the anchor's exact type, proved by `lp3_planar_strongAMD_safety_source …`; imports `KAM.Planetary.StrongAMD.Nek.PlanarSafety.Source` |
| 4 | `KAM/Provider/Planetary/Spatial/SpatialStrongAMDExponentialSafetyNoArith.lean` | provider (staged on this branch) | `KAM.Provider.Planetary.Spatial.spatial_strongAMD_exponentialSafety_noArith`, by `lp3_spatial_strongAMD_safety_source …`; imports `KAM.Planetary.Spatial.Nek.SpatialSafety.Source`, `KAM.Planetary.Spatial.SourceBarycentric` |
| 5 | `manifest/frozen-anchors.json` | 2 new entries, state `SEALED` | below; the 307 existing entries JSON-equal |

Generated, not hand-edited: `KAM/Root/Frozen.lean` (+2 lines, the two anchors) and `KAM/Root/Provider.lean` (+2 lines,
the two providers), by `scripts/gen_root_imports.py`; `docs/MANIFEST-CHANGES.md` gets 2 rows citing the approval
decision (`lp_manifest_changes_rows.py`).

**Manifest entries** (from the dry run; `prefix_sha256` depends on the filled date and decision, so its dry-run value
is not final; `abi_sha256` from `scripts/abi_hashes.py` at install):

| Id | Entry | Path | Provider (implementation.module) | `definition_closure` files |
|---|---|---|---|---|
| LP3-1 | `planetary.d59.planar_strongAMD_exponentialSafety_noArith.v1` | `KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafetyNoArith.lean` | `KAM.Provider.Planetary.StrongAMD.PlanarStrongAMDExponentialSafetyNoArith` | 79 |
| LP3-2 | `planetary.d59.spatial_strongAMD_exponentialSafety_noArith.v1` | `KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafetyNoArith.lean` | `KAM.Provider.Planetary.Spatial.SpatialStrongAMDExponentialSafetyNoArith` | 96 |

**Commands** (the D62 sequence, FREEZE.md §Method 3, 6, 7; `A8` = the approved commit of this draft, `DATE`, `DEC` the
approval; an approval record `approval-<DEC>.json` as `approval-D62.json`):

1. `python3 docs/tracks/LP/freeze/lp_freeze_install.py --root . --approved $A8:docs/tracks/LP/freeze/draft8 --date
   $DATE --decision $DEC --kind theorem --sealed` (asserts: only the two placeholders and the body change; the sealed
   body equals the sealing string of the file's own docstring; ≤ 3 lines, ≤ 240 bytes, ≤ 100 columns).
2. `python3 docs/tracks/LP/freeze/lp_manifest_add.py --root . --approved $A8:docs/tracks/LP/freeze/draft8 --approval
   docs/tracks/LP/freeze/approval-$DEC.json` (hashes with the guard's code; closure cross-checked; existing entries
   JSON-equal), then `abi_hashes.py` on the 2 new entries (twice, identical) and `lp_manifest_add.py --abi`.
3. `python3 scripts/gen_root_imports.py`; `lp_manifest_changes_rows.py` (2 rows).
4. Checks: `lp_build.sh` of the two frozen modules (the providers are already built); `check_frozen_anchors.py`;
   `abi_hashes.py --check`; the probe `lp_axioms.py --probe` / `--verify` (Expr-equal types, standard axioms); kernel
   replay of the 4 modules; `lp_lint.sh` exit 0 (the staged-provider root deviation disappears with the entries).

**Dry run** of steps 1–3 against this commit's draft (verification §6): passes. Import chain after the install: frozen
LP3 anchor → (private import) its provider → the LP3 implementation → the **sealed** frozen
`KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev` → (private import) its provider (D58 pattern); no other
module imports either provider.

## 7. Notes

- **Not frozen (stay ordinary theorems).** `lp3_planar_strongAMD_safety_source_general`,
  `lp3_spatial_strongAMD_safety_source_general` (OD-3); the non-source forms `lp3_planar_strongAMD_safety{,_normalized}`
  and `lp3_spatial_strongAMD_safety{,_normalized}` (they use the total helpers, superseded by OD-11 (b) as LP1/LP2's
  were).
- **MAIN tags.** The implementation docstrings of the LP3 Source modules cite `LP:MAIN L15 (502–506)`; MAIN's item at
  502–506 is Theorem 15, so the anchors write `T15`, as the frozen LP1 does (implementation docstring nit, not frozen).
- **Staged providers before the install.** `scripts/gen_root_imports.py` quarantines only providers of DRAFT_SORRY
  anchors, so while the two providers are staged without manifest entries, `lp_lint.sh` reports
  `KAM/Root/Provider.lean` out of date; the roots are deliberately not regenerated (AGENTS rule 9). The install's
  manifest entries resolve it (verification §7).
- **Provider docstrings** still name package LP-FREEZE8 and say "The statement surface is proposed in
  docs/tracks/LP/FREEZE-PROPOSAL.md" (SPEC §4 sentence); they are byte-identical to the first run (not frozen files).
