# Handoff SHARP2-HYBRID: the certified first step (hybrid), design for theorem and certifier

30 October 2026. Branch `sharp-hybrid` (from `sharp-v2` at f7bd6712). Design work: blueprint, signatures (elaborating in
a `.drafts` probe), Python. No Lean module was added or changed; no kernel test was built or run; no merge was made.
Main text: `docs/campaign/design/APOST-SHARP-V2-HYBRID.md`.

## Outcome

- **Theorem form: a restart.** The hybrid applies a proved v2 branch theorem to the new torus K₁ = K + ΔK and transfers
  its conclusion back to K (Proposition `bp:p2s2hc:restart`, proved in the probe as `concl_restart`; iso
  `iconcl_restart`).
  - **Transfer lemmas.** Every hypothesis for K₁ follows from explicit bounds by the transfer lemmas: new torus, new error,
    frames, torsion, and iso new errors, ray and bordered torsion. The bounds are on ΔK, on the linearised new error
    Ẽ = E + DX_h(K)ΔK − DΔK·ω, and on data of K that the checker already certifies.
  - **The new error** is |E₁| ≤ |Ẽ| + (M₂/2)|ΔK|²: Taylor around K, with no composition of h with K₁.
  - **Conclusion.** The frozen bodies. The minimum with the existing routes is by cases: never worse, because the plain
    branch remains available. Exact recovery at ΔK = 0 is not claimed (SHARP2-HYBRID-FIX, F3).
  - **Soundness never uses that ΔK solves the cohomological equations.** The producer computes ΔK; the kernel divides by
    no small divisor and needs no `cohSolve`. The step is additive, so route B's composition K̃∘(id + ξᴸ) is not needed.
- **Certifier side.** One new primitive is needed: a product of models (DX_h∘K times ΔK), plus Cauchy for a model's
  remainder (optional). Otherwise it uses norms of a polynomial, exact polynomial products for Ω_K and Ω_{K₁}, and the
  existing route cores at the restart numbers.
  - The composition (exp witnesses) runs once, on the coarse K, at the accuracy of the final error. Frame, Gram and
    torsion models run on the coarse K (23 instead of 87 terms of v at R1's numbers: up to ≈ 14× fewer operations for
    those models).
  - Package split C8a–C8d: the R1-scale test goes to `kernel-tests/`, unbuilt, with its expected cost stated.
- **The R1 planning scale** (wording corrected in SHARP2-HYBRID-FIX, F2). This is a sampled analytic-graph experiment
  in the enclosures' intended norms, not a certificate; the finite-candidate numbers are in the SHARP2-HYBRID-FIX section.
  On R1's truncations, iso route A′:
  - the plain v2 passes the floating tests from L = 15 (87 terms of v, residual 4.6·10⁻¹², threshold 10^{−10.95});
  - the hybrid passes them from **L = 8 (23 terms, residual 3.9·10⁻⁶): an admissible residual scale around 10^{−5.28}**;
  - route B's hybrid is 10^{−5.96}; route A′ fixed (formal) 10^{−5.16};
  - the best restart strip is ρ₁ = ρ.

  On R1's own 10⁻⁷⁹ residual shape (formal scaling model) the hybrid gives 10^{−3.80} (iso) / 10^{−3.57} (fixed) at
  ρ₁ = ρ − 3δ₀. The earlier heuristic gave −4.4 / −4.2; the enclosure numbers are 0.6 better because Ẽ is measured at
  the restart strip.
- **Remaining binding terms.**
  - The restarted theorem's own threshold: route A′'s cap sum `Tab` (iso tail E at reduced strips), route B's tail decay.
  - The quadratic Newton residual Ẽ: ≈ 0.39 e² in ℓ¹ on truncations, 2.4× its true sup.
  - Negligible: the Taylor remainder (10⁻³ of e₁), every transfer increment (≤ 4.4·10⁻⁴ relative), the energy and
    frequency terms, the displacement (5.7·10⁻⁸ on T_{ρ∞}, against SO's 1.4·10⁻⁵).
  - Projected next levers (not computed): a two-step ΔK from the producer (≈ +1.3 orders), and modelling the quadratic
    Taylor term (then the frozen |DK| and ball budgets bind, e ≲ 2·10⁻³).
- **Observation on R1** (wording corrected in SHARP2-HYBRID-FIX, F4). The ordinary torsion average is sampled as nearly
  singular (|⟨T⟩⁻¹| ≈ 8·10¹⁹); the package bounds only the bordered inverse (0.584). Only the isoenergetic theorems apply to R1; the fixed-frequency R1 rows of the
  design tables are formal (design note §4.6).

## Files

| File | Status | Content |
|---|---|---|
| `blueprint/parts/p2s2-hybrid-cert.tex` | new | Track K, labels `bp:p2s2hc:*`: standing data; linearised new error; step bounds (S1)–(S7); restart (Proposition); transfer lemmas (new torus, new error, frames, torsion); restart data and `HybOk_R`; the hybrid theorem; the minimum with the existing routes; checker interface; register |
| `blueprint/sharp2-hybrid.tex` | new | Driver (sharp2.tex + the new part) |
| `blueprint-I/parts/p2s2-iso-hybrid-cert.tex` | new | Iso delta, labels `bpI:p2s2hc:*`: linearised energy error, iso step bounds, iso restart, new errors and the ray, bordered torsion of the new torus, the iso theorem and minimum |
| `blueprint-I/sharp2-hybrid.tex` | new | Driver |
| `docs/campaign/design/APOST-SHARP-V2-HYBRID.md` | new | Design note: decision, mathematics, certifier side (computations, precision, cost, package split, SO wiring), R1 numbers, Lean signatures and package split, risks, reproduction, audit answers |
| `docs/campaign/design/APOST-SHARP-V2-HYBRID-SIGNATURES.lean.txt` | new | Copy of the probe `.drafts/hybrid/Signatures.lean` (byte-identical, sha256 prefix e62e0a781c28f2fc) |
| `docs/campaign/design/hybrid/r1-{trunc,shape,sizes}.json` | new | Raw outputs of the three runs |
| `scripts/apost_sharp/hybrid_cert_r1.py` | new | R1 numbers in the enclosures' norms: `--trunc` (truncated candidates, with the new error also computed directly), `--shape` (R1's residual shape), `--sizes` (model sizes) |
| `docs/campaign/handoffs/SHARP2-HYBRID.md` | new | This handoff |

No existing tracked file was modified (additive-only rule).

## Approach

1. Read the earlier hybrid (Corollary `bp:p2s2:hybrid`, `thresholds_v2.hybrid`, `step0_actual.py`), the audits' F6, the
   ℓ¹-entry design (B10), and the branch theorems of routes A, A′, B (fixed and iso). A subagent surveyed the certifier
   (`KAM/CertificateSharp/**`, handoffs C5CORE, C6, C6L8, C7, PLCERT, CERTIFIER-SHARPNESS).
2. **Decision: restart instead of an engine stage.** It is composable with every proved theorem, needs no step
   identities, leaves the restart strip free, and is never worse. It loses nothing against continuing the schedule
   (design note §1.1).
3. **Transfer lemmas** built on existing pieces: `taylor_iteratedFDeriv`, the torsion polynomial and
   `norm_torsion_sub_torsionAB_le`, `inv_le_of_ref`, `cauchy_strip`. The torsion is handled through its frame part plus
   local parts, so no derivative of the frame of K₁ is needed.
4. **Signatures** in a `.drafts` probe against `sharp-v2`. Each `sorry` target was then checked against its intended
   proof; three statements were repaired (design note §5.2).
5. **Numbers.** For R1's truncations, the iso step is computed on shifted grids; Ẽ, the increments, and the directly
   computed E₁ are measured in weighted ℓ¹ (and sampled sup); the transfer and the restarted theorem
   (`thresholds_v2.py`) are evaluated at seven restart strips. For R1's own residual the same is done in the scaling
   model.

## Checks and their output

- `nice -n 5 lake env lean .drafts/hybrid/Signatures.lean` (with `set_option autoImplicit false`): exit 0, 15 "declaration
  uses `sorry`" (the targets), no error; 9 s, 3.6 GB peak (`/usr/bin/time -v`). 785 lines, 52 declarations, no line over
  100 characters.
- Name-clash probe `.drafts/hybrid/Clash.lean`: every built library module (1186 of the 1658 reachable from `KAM.lean`)
  plus the signature body. Exit 0, the same 15 `sorry`, no redeclaration; 7.1 GB peak under an 8.5 GB watchdog.
  - The 472 unbuilt modules (358 `Planetary`) were not built (forbidden).
  - A textual search of `KAM/**/*.lean` finds none of the new names (namespaces `KAM.Sharp2.Hybrid`,
    `KAM.Iso.Sharp2.Hybrid`, plus `KAM.Sharp2.RouteA.NumA.restart`).
- `latexmk -pdf` on `blueprint/sharp2-hybrid.tex` and `blueprint-I/sharp2-hybrid.tex` (out of tree): exit 0, no undefined
  reference, no `??` in the new sections. The new pages were checked rendered; one overfull display and one Lean name
  were fixed.
- `scripts/apost_sharp/hybrid_cert_r1.py`:
  - `--trunc`: exit 0, 11 candidates × 4 forms × 7 strips; the tables of design note §4.3 (renumbered in SHARP2-HYBRID-FIX). e₁ bounds the directly
    computed E₁ in every row (ratio ≈ 2.4).
  - `--shape`: exit 0; table §4.4. The solver agrees with (log e₁* − log A)/2 to 0.01.
  - `--sizes`: exit 0; table §3.3.
  - The plain thresholds reproduced: route A′ −10.71 / −10.95, route B −12.25 / −12.33 (fixed / iso).
- `scripts/lint_sources.sh`: exit 1. Every check passes (forbidden tokens, providers, root imports, errata render, 1687
  module files, frozen-anchor guard) except `abi_hashes.py`. That step needs the frozen planetary modules built
  ("object file … `KAM/Frozen/Planetary/Theorems/FixedSunPlanetaryKAM.olean` … does not exist") and they are not built in
  this worktree. No Lean module changed in this package.

## Axioms

`.drafts/hybrid/Axioms.lean` (the probe plus `#print axioms`):
- `KAM.Sharp2.Hybrid.restart_close`, `concl_restart`, `iconcl_restart`: `[propext, Classical.choice, Quot.sound]`.
- `KAM.Sharp2.Hybrid.g1_hybrid_R`, `KAM.Iso.Sharp2.Hybrid.iso_g1_hybrid_R`: `[propext, sorryAx, Classical.choice,
  Quot.sound]` (targets).

## Uncertainties

- **Design numbers, not certificates.** They are double precision on sampled grids (512 × 128 and 1024 × 256). The kernel
  would compute the analogous norms of finite inputs; the analytic-graph experiment is not such an input (SHARP2-HYBRID-FIX,
  F1). For L ≥ 12 the computed Ẽ is at the double-precision floor (≈ 10⁻¹⁸); those margins are
  unresolved numerical estimates, not lower bounds (SHARP2-HYBRID-FIX, F2).
- **The truncation family is a model of a coarse candidate.** A producer's own coarse torus (fewer Newton iterations
  rather than truncation) may have a different residual spectrum. The certificate always measures the actual step, so
  this affects planning numbers only.
- **The R1 package (c = 7/4, separate σ's) is the design package**, not SO's `lunarR1` (c = 237/125, one σ = 1.987,
  M = 2.03); see the certifier survey in the design note §3.
- **Kernel cost is estimated.** The ≈ 1 μs per product rate is inferred from CERTIFIER-SHARPNESS §4.2. The route-A′
  numerical core at R1 (C6L8: 19.2 GB) is above the machine's 10 GB cap and must be split; that is inherited, not caused
  by the hybrid.
- **Integrability side conditions.** `torsionAverage_step`, `energyAverage_step_le` and `extTorsionAverage_step` state
  them as hypotheses in the probe; H2/H4 must derive them from holomorphy.
- **The iso minimum** (`iso_g1_v2A'_hybrid`) is specified (blueprint `bpI:p2s2hc:frozen`, design note §5) but not stated in
  the probe (800-line cap); it is the same proof by cases as `g1_v2A'_hybrid`.
- **The projected levers** of §4.5 (multi-step ΔK, modelled quadratic term) are estimates, not computations.

## Suspected errata and deviations

- **Errata in pinned sources: none.**
- **Recorded for the orchestrator.** R1's ordinary torsion average is sampled as nearly singular, so the fixed-frequency R1 rows in earlier
  design tables (APOST-SHARP-V2 §§6, 11; SHARP2-FIX, DOMPLUS) are formal (design note §4.6).
- **Deviations: none from a source.** The restart, the transfer lemmas and the additive step for every route are ours.
- **Superseded.** Corollary `bp:p2s2:hybrid` and `thresholds_v2.hybrid` are superseded by the new part. They were not edited
  (additive rule); the orchestrator may add pointers.
- **Process note.** Twice in this package a `pgrep -f`/kill pattern matched my own shell command and killed it (exit 144).
  The jobs affected were restarted from scratch. Every reported number comes from a complete run. The truncated run
  started before the last two script edits (the defect-lemma default for |Ω_{K₁}| and the shape solver's bisection);
  neither is on its code path (it uses the measured Ω_{K₁} and no solver).


## SHARP2-HYBRID-FIX

30 October 2026, branch `sharp-hybrid`. This repairs AUDIT-HYBRID-1 (`/home/scott/kam-tools/audits/AUDIT-HYBRID-1.md`):
PASS for the restart/transfer design, with F1–F4 to repair, and the implementation split into packages C8a–C8d. Python,
documents and blueprint only; no Lean module was added or changed and no Lean process was run in this repair.

### Outcome

- **F1 (HIGH, finite inputs): repaired.** `hybrid_cert_r1.py --finite` builds the checker's carrier and recomputes every
  bound from it.
  - **The finite candidate.** K̂ = (ψ + Û, φ, P̂₁, P̂₂), every component a finite dyadic trigonometric polynomial (2⁻⁶⁰).
    P̂₂ = P̂₁ + Ĵ, with Ĵ a truncation of the infinite series J = −P̂₁²/2 − V(q, φ).
  - **The finite step.** The step is computed on K̂ and emitted as a finite dyadic ΔK̂.
  - **Every bound is recomputed from K̂ and ΔK̂:** the residual and energy error of K̂, Ẽ, the direct E₁, exact coefficient
    norms of ΔK̂ and DΔK̂, DE, the Ω products, ε̃ and K̂'s own caps.
  - **Ledger and supports.** A truncation and rounding ledger is recorded, and the supports of every component and of
    the witness W = e^{4πiÛ} are counted.
  - **Emitted data.** The L = 8 candidate is in `docs/campaign/design/hybrid/r1-L8-finite-candidate.json` (Û 46, P̂₁ 47,
    P̂₂ 73, ΔK̂ 127 / 60 / 149 / 191 coefficients, integers at 2⁶⁰).
  - **Results** (iso route A′, best ρ₁ = ρ):

    | Theorem | First L that passes | Margin | Supports |
    |---|---:|---:|---|
    | Plain | 15 | +0.39 | Û 174, P̂₂ 310 |
    | Hybrid | 8 | +0.34 | Û 46, P̂₂ 73 |

    - At L = 7 the hybrid margin is −0.86. The planning scale is about 10⁻⁵·²⁵, within 0.06 orders of the
      analytic-graph experiment at L ≤ 9.
    - Route B passes from L = 9.
    - K̂'s sampled caps equal R1's base values at every L.
    - The 2⁻⁶⁰ rounding of ΔK̂ floors Ẽ at about 2·10⁻¹⁴ (L ≥ 10), 10⁻³ of e₁*.
  - **Cost proxy, now counting every component.** The embedding shrinks 3.8–4.2× (frame-type products ≈ 15–18×). The
    witness does not shrink (101 against 113 terms).
  - **Old tables relabelled.** The analytic-graph tables are kept as planning experiments (design note §4.3).
- **F2 (MEDIUM, wording): repaired.**
  - "Certified threshold" is replaced by "planning scale", and "certifies" by "passes the floating test". This applies
    in the design note (§0, §§4.2–4.5), the original handoff sections, the blueprint register (i) and the script
    docstring.
  - Floor values are "unresolved numerical estimates, not lower bounds".
  - The 10% model-remainder allowance is stated as unchecked.
- **F3 (MEDIUM, zero step): repaired.**
  - Corollary `bp:p2s2hc:frozen` now says: acceptance is never worse because the plain branch remains available.
  - Exact recovery through the transfer formulas is withdrawn, because the local torsion bounds λ₀ and λ₁ do not cancel
    at ΔK = 0.
  - A remark says the displayed maximum is a common bound; a consumer such as SO's `disp` keeps the closeness of the
    branch that holds. The same change is in the design note §0 and the original handoff section.
- **F4 (MEDIUM, singularity): repaired.**
  - New wording: "the ordinary torsion average is sampled as nearly singular (|⟨T⟩⁻¹| ≈ 8·10¹⁹; 6·10¹⁰ to 1.5·10²⁰ on the
    finite candidates); the design package uses the bordered inverse and so supplies only isoenergetic applicability;
    the fixed-frequency rows are formal scalar experiments; exact singularity is not claimed."
  - Changed in the design note (§0, §4.1, §4.6), blueprint register (v), the iso part's introduction, the script
    docstrings and the original handoff sections.
  - The older landed claims in `APOST-SHARP-V2.md` (§§6, 11, line 686) and the SHARP2-FIX/DOMPLUS tables need the
    orchestrator's pointer; they were not edited (additive rule).
- **Packages C8a–C8d** (design note §3.4; they replace the earlier H1–H5 / C8a–C8d split):

  | Package | Content | Lines | Lean process budget |
  |---|---|---:|---|
  | C8a | restart and transfer lemmas, theorem side (four modules) | ≈ 1.45k | ≤ 5 GB per module |
  | C8b | step-form theorems and the minimum, fixed and iso (five modules) | ≈ 1.8k | ≤ 6 GB per module |
  | C8c | certifier primitives (model products, Cauchy for a remainder), the hybrid checker and soundness, the iso wrapper | ≈ 1.75k | ≤ 4 GB per module |
  | C8d | the R1 producer of finite K̂ and ΔK̂ in SO's package (Python ≈ 450 lines), and the R1-scale tests | ≈ 400 | ≤ 6 GB per declaration by construction |

  - **Kernel tests.** C8a and C8b have none. C8c has a toy T² test only (≤ 2 GB, seconds). C8d's R1-scale tests go in
    `kernel-tests/`, are not built, and are split per stage: witness and composition; frames; Ẽ; and the route-A′ core per
    engine stage and per small-divisor bite.
  - **Expected cost of C8d.** It is dominated by the core, which took 19.2 GB unsplit in C6L8 and must be split below
    8 GB.
  - **Order.** C8a, then C8b, then C8c; the C8d producer can start at once.

### Files (this repair)

| File | Change |
|---|---|
| `scripts/apost_sharp/hybrid_cert_r1.py` | `--finite` (finite K̂, ΔK̂; `--emit`); `FinTorus`, `build_finite`, `step_fin`, `finite_measure`, `coef_from_corners`, `trunc_tail`, `l1_coef`; docstrings (F2, F4) |
| `docs/campaign/design/hybrid/r1-finite.json`, `r1-L8-finite-candidate.json` | new: the finite run and the emitted L = 8 candidate |
| `docs/campaign/design/APOST-SHARP-V2-HYBRID.md` | §0, §1.1, §3.2–3.4 (finite supports, packages C8a–C8d), §4 restructured (4.2 finite candidates, 4.3 analytic graph, 4.4 shape, 4.5 planning scale, 4.6 observation), §5, §6, §7, §8 (AUDIT-HYBRID-1 dispositions) |
| `blueprint/parts/p2s2-hybrid-cert.tex` | Corollary `bp:p2s2hc:frozen` (F3), register (i) numbers (F1, F2), (v) observation (F4) |
| `blueprint-I/parts/p2s2-iso-hybrid-cert.tex` | introduction (F4) |
| `docs/campaign/handoffs/SHARP2-HYBRID.md` | the original sections' wording (F2–F4), and this section |

### Checks and their output

- `python3 -I scripts/apost_sharp/hybrid_cert_r1.py --finite --emit DIR --json OUT` (niced, one thread): exit 0, about
  15 min.
  - L = 6, 7, 8, 9, 10, 15; the table of design note §4.2.
  - Plain thresholds reproduced: route A′ −10.71 / −10.95, route B −12.25 / −12.33 (fixed / iso).
  - e₁ ≥ E₁ (direct sampled sup) in every row; the ratio is 2.1–2.2 for L ≤ 9.
  - The test run `--finite --L 8` gave the same L = 8 numbers.
- `latexmk -pdf` on both blueprint drivers (out of tree): exit 0, no undefined reference. The new corollary page was
  checked rendered.
- No Lean module changed, and the signature file is unchanged (sha256 prefix e62e0a781c28f2fc). The probe result of
  SHARP2-HYBRID stands (exit 0, 15 `sorry`, 3.6 GB), as confirmed by the audit (5.27 s, 3.56 GB). No Lean process was
  run in this repair.

### Uncertainties

- **Still floating, still uncertified** (F2). The finite candidates are the checker's carrier, but every norm of a
  non-finite function (E, Ẽ, the witness) is a corner-grid FFT estimate on 512 × 128. The 10% remainder allowance is not
  checked, and no outward rounding was done. The C8c/C8d kernel computes the real enclosures.
- **Truncation rules are choices.** Ĵ's truncation at 10⁻³e and ΔK̂'s at 10⁻³e² were chosen by hand. A producer may trade
  support for residual differently; the supports in §3.3 are for this rule.
- **The design package is not SO's `lunarR1`** (c = 7/4 against c = 237/125). The C8d producer must use SO's package.

### Suspected errata and deviations

None in pinned sources. No new deviation; the F1–F4 repairs are to our own design and claims.
