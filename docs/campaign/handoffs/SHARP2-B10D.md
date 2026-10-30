# Handoff SHARP2-B10D: design of the ℓ¹ hybrid Newton scheme (package B10)

30 October 2026. Branch `sharp-b10` (from `sharp-v2` at b52d6b71). Design only: blueprint, signatures, Python. No Lean
module was added; no merge was made.

## Verdict

- **The hybrid is an ℓ¹ entry step.** The first Newton step solves its two cohomological equations, takes its average
  and bounds the Lagrangian defect of the initial torus from weighted-ℓ¹ data of that torus, with Γ_∞ (SHARP-L9).
  Everything else, and every later step, is the sup-norm v2 scheme. The conclusion is the frozen `G1Body`/`IG1Body`.
- **No sup → ℓ¹ conversion is used.** At later stages it would cost coth(πσ)ⁿ ≥ 10³, against a small-divisor gain
  ≤ 6–18.
- **PlasmaLean (owner requirement met).** Best margin over its 10⁻¹⁸·²⁴: **+2.84** like for like (ℓ¹ error vs its ℓ¹
  error) and **+2.31** sup-equivalent (ℓ¹/sup = 3.6), at its pessimistic norms. The best variant is route A with the
  entry and the ℓ¹ frame increment. The sup-norm v2 gives +0.97.
- **R1.** Route A goes −11.18 → **−10.13** (fixed) and −11.37 → **−10.32** (iso), +1.05 orders, on measured ℓ¹ data
  (heuristic until enclosed). Route B gains 0.1.

## Files

| File | Status | Content |
|---|---|---|
| `blueprint/parts/p2s2-l1hybrid.tex` | new | Addendum, labels `bp:p2s2l1:*`: norms and toolkit; prices of conversion and composition; ℓ¹ solves; defect identity; design decision with the pricing table; entry data (L1)–(L5); entry constants and steps for routes A and B; ℓ¹ frame increment; never-worse lemma; engine bookkeeping (restart, route-A embedding, closeness); theorems; register |
| `blueprint/sharp2-l1.tex` | new | Top file (sharp2.tex + the new part) |
| `blueprint-I/parts/p2s2-iso-l1hybrid.tex` | new | Iso delta, labels `bpI:p2s2l1:*`: bordered averages and the tangential datum in ℓ¹; iso entry constants; I-G1 with the entry; certificate cost |
| `blueprint-I/sharp2-l1.tex` | new | Top file |
| `docs/campaign/design/APOST-SHARP-V2-L1.md` | new | Design note: decision, mathematics, numbers, signature deltas, package split, coordination, risks, reproduction |
| `docs/campaign/design/APOST-SHARP-V2-L1-SIGNATURES.lean.txt` | new | Copy of `.drafts/sharp2/L1Signatures.lean` (sha256 identical) |
| `scripts/apost_sharp/l1_entry_r1.py` | new | R1's weighted-ℓ¹ data (heuristic, sampled FFT) |
| `scripts/apost_sharp/thresholds_v2.py` | extended (named in the brief) | Changes listed below |
| `scripts/apost_sharp/dominance.py` | extended (named in the brief) | `plasmalean_l1()` (the B10 table) after the existing table |

Changes to `thresholds_v2.py`:
- `stageA` and `stageB` take `l1=` (stage 0 only), with the per-ingredient minimum and the split of C_Ω.
- The route-A ℓ¹ frame increment (`nuK`, `nuN`).
- `c_inf_fn`, which computes Γ_∞ at the actual bites with the fibered SHARP-L9 routine.
- `entry_variants`, `run_l1`, `main_l1` and the `--l1` command.
- `engine_A(b5=…)`: the conditions of the Lean predicate.
- `R1_L1`.

Default outputs are byte-identical.

## Approach

1. **Read the inputs:** the design §10, the audits AUDIT-SHARP-V2-{fixed,iso}-1 (per the orchestrator note), the SHARP-L9
   handoff, the v2 blueprints and signatures, and `sharp-v2`'s B1/B2/B3/B5 (read-only through `git show`).
2. **Priced the options.** Converting the later-stage errors to ℓ¹ costs ϱ ≥ 2·10³. On R1 the Taylor term is 16–68 %
   of route A's C_E at stages 0–4 (measured with `stageA`), so a propagated ℓ¹ error is ≥ 300× its sup bound. Decision:
   ℓ¹ only at the entry, where the certificate computes the data.
3. **Found two further levers inside the entry:**
   - the defect identity Ω_K = −(Du − (Du)ᵀ), u = 𝓡ηᴺ, with the row-sum ℓ¹ Cauchy factor n/e instead of 2(n−1);
   - the ℓ¹ frame increment |ΔL| ≤ ‖ΔK‖₁/(eηδ) instead of n|ΔK|/(ηδ). This acts on route A's binding ⟨T⟩⁻¹ cap sum and
     is worth +0.5 orders.
4. **Made the entry never worse than the sup stage:** per-ingredient minimum, and the iso cubic term keeps its sup
   denominator (a first draft lost 0.09 on route B iso through that division).
5. **Measured R1's ℓ¹ data and computed the tables.** Then wrote the blueprint, the probe and the design note.

## Checks and their output

- **Signature probe.** `nice -n 5 lake env lean .drafts/sharp2/L1Signatures.lean`: exit 0, exactly 22 warnings
  "declaration uses `sorry`", no other diagnostic.
  - 1116 lines; lines 1–304 are a verbatim copy of the `sharp-v2` declarations used (B1 `SDConst`; B2 `RefData`,
    `RefHyp`; B3 `StepIn`, `stepConsts`, `stepCond`; the planned B4 `modNewton`; the B5 engine with `converge_checked`).
    Those modules are not built in this worktree.
  - `entryConstsB`, `stageConstsA`, `engineConstsA` and the predicates are full definitions.
  - `g1Body_iff_split` and `ig1Body_iff_split` are proved.
- **Axioms** (`#print axioms` in a transient probe):
  - `g1Body_iff_split` and `ig1Body_iff_split`: `[propext, Classical.choice, Quot.sound]`;
  - the main results (`g1_l1A`, …): `sorryAx` plus the standard three. They are signatures only, as briefed.
- **Lint.** `sh scripts/lint_sources.sh`: exit 1, with only the two pre-existing failures that the v2 audits also
  record:
  - the generated `KAM.lean` is over 1500 lines;
  - the ABI step lacks `KAM/Frozen/Planetary/Theorems/FixedSunPlanetaryKAM.olean`.

  `check_lean_modules: PASS (1487 Lean files)` and `FROZEN-ANCHOR GUARD OK`. No Lean module was added, so no targeted
  `lake build` applies.
- **Python.**
  - `thresholds_v2.py` (default): output byte-identical to the committed version (diff against `git show HEAD:`
    copies).
  - `dominance.py --plasmalean`: the original table is identical; the B10 table is added.
  - `thresholds_v2.py --l1` (12 s), `dominance.py --plasmalean` (12 s) and `l1_entry_r1.py` (6 s): exit 0, tables as in
    the design note §3.
- **Blueprint.** `pdflatex` (two passes) of `blueprint/sharp2-l1.tex` and `blueprint-I/sharp2-l1.tex`: exit 0, 0
  undefined references. Three overfull boxes of at most 25 pt remain in the new part; the existing parts have 27.

## Main numbers

`thresholds_v2.py --l1`, `dominance.py --plasmalean`.

**PlasmaLean (cA-like).**

| Variant | (a) ℓ¹ vs ℓ¹ | Margin | (b) ×3.6 | Margin |
|---|---:|---:|---:|---:|
| A7 (sup) | −17.27 | +0.97 | −17.27 | +0.97 |
| A7 + entry | −15.91 | +2.33 | −16.44 | +1.80 |
| A7 + entry + frame increment | −15.40 | +2.84 | −15.93 | +2.31 |
| B6 + entry | −17.12 | +1.12 | −17.65 | +0.59 |

With the R1-like norms the margins are +6.18 and +5.73.

**R1.**

| Variant | Fixed | Iso |
|---|---:|---:|
| A7 + entry + frame increment | −10.13 | −10.32 |
| B6 + entry | −12.16 | −12.31 |

The sensitivity to the ℓ¹/sup ratio a runs from −9.67 (a = 1) to −10.29 (a = 8).

**Measured R1 data:**

| Object | Value |
|---|---:|
| ‖E‖₁/sup | 4.28 (matches CERTIFIER-SHARPNESS) |
| a_N | 3.92 |
| a_L | 0.26 |
| ‖T‖₁ | 3.55 (sup 3.31) |
| ‖L‖₁ | 1.36 |
| ‖N‖₁ | 1.42 |

The small-divisor constants:

| | c_∞(δ₀) | c_freq |
|---|---:|---:|
| R1 | 0.00051 | 0.0030 |
| PlasmaLean | 0.00126 | 0.0075, computed at each bite (§10.1's flat value agrees to 3 digits) |

## Package split

Full table in the design note §5.

| Package | Lines |
|---|---:|
| B10a NORMS | 450 |
| B10b SOLVE | 350 |
| B10c ROUTE A | 750 |
| B10d ROUTE B (optional) | 450 |
| B10e G1/ISO | 650 |
| Total | ≈ 2.65k (2.2k without route B) |

- **Start now:** B10a and B10b (they depend only on SHARP-L9 and B2).
- **Then:** B10c after B9, and B10d after B4.

**Requested deltas:**
- **B4:** state the modified step from solve bounds (`modified_step_of_solve`), with the C_Ω split of audit F8.
- **B9:** parametrize the route-A stage constants by the solve record (`stageConstsA … EntryNumA` is the reference
  transcription of `stageA`), and enter the B5 engine through the reparametrisation μ = ε/(γ³δ^{3κ−1}),
  Q = 2^{3κ−1}C_E.
- **B3:** add the certified c_Th and c_DTh to `StepIn`.

## Uncertainties

- **R1's ℓ¹ data** are sampled FFT coefficients, not enclosures. The theorem's data are these × 1.05.
- **PlasmaLean's bounds** (σ_K 3.1, σ_B 2, M 3, ‖T‖ 19.84, twist 0.22) are read as both sup and ℓ¹ bounds, with
  transposes at the conservative defaults. The comparison is not like for like (non-canonical field, 1½ degrees of
  freedom).
- **Route A's v2 stage constants** (`stageConstsA`) are my transcription of `stageA` (levers A7). If B9 lands a
  different transcription, the B10 delta is only the `EntryNumA` parametrisation.
- **Inherited gaps.** Audit F8 (the torsion of the new torus at the stage transition) and iso-F5 (moving-frequency
  factors) apply unchanged to the K̄ part of the entry. The entry inherits their repairs through the sup constants.
- **`routeA_isNewton`** defines the constants of non-schedule bites through `schedIdx` (floor/log). This is a choice of
  B9/B10c, not a mathematical claim.
- **Line estimates** are ±20 %. The bridges of B10a (products and derivatives of absolutely convergent Fourier series on
  strips) are the main new analysis; `KAM/Weighted` has the Fourier–Taylor templates.

## Suspected errata and deviations

**Pinned sources.** None found.

**Own design and code** (for the orchestrator):
1. **Design doc §10.1, PlasmaLean "freq" row.** It uses a flat c_freq at δ₀ for all stages, which is not a per-bite
   certificate (audit F3/F9 style). Recomputed per bite (0.00754 → 0.00752), the number is unchanged (−17.27).
2. **Design doc §10.2.** "A parallel norm layer for the step (1.5–2k lines)" is superseded: the entry design needs no ℓ¹
   step layer beyond stage 0 (≈ 2.65k lines, mostly theorem assembly).
3. **B3 interface gap.** `StepIn` has no c_Th or c_DTh, but the design's route-B rows B1–B6 use the certified c_Th, so
   `stepConsts` mirrors `stageB` only with c_Th = 2M₁.
4. **Python mirror vs the Lean predicates.** Route B's prefix conditions lack the local contraction 2^{κ+1}QX ≤ 1 (audit
   F8); it is added at the entry stage only. Route A's tail check is ≤ 1 (the v1 engine); B5 needs ≤ 1/2. The B10
   route-A rows use `b5=True` (local contraction at every prefix stage, tail ≤ 1/2), with no number change. The default
   v2 rows are left as they were (not mine).

**Deviations introduced** (recorded in Remark `bp:p2s2l1:register`(iv)):
- the entry step itself;
- the per-ingredient minimum;
- the ℓ¹ frame increment (route A);
- the defect identity used constructively;
- the full-bite average in ℓ¹ at real points;
- reading (a) of the PlasmaLean comparison.

## What remains

- **Implementation.** Packages B10a–e.
- **Certificate side.** Enclosures of ‖ηᴺ‖₁, ‖ηᴸ‖₁, ‖T‖₁ and ‖L‖₁, ‖N‖₁ on the models the checker already builds, plus
  three Γ_∞ certificates (`smallDivisorSup_snoc_le`; for R1 752, 1518 and fewer entries).
- **Data.** H50's ℓ¹ data (no H50 rows yet).
- **Audit.** An independent design audit of the B10 deltas before implementation.
