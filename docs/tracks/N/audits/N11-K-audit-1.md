# N11-K1 and N11-K2: independent audit 1

Lane N (Zohar's team), 2026-10-29. This is an independent, refute-first, read-only audit. Nothing was compiled
during the audit; the gate build is recorded separately: commit `af839ecc` on `zohar/n11`, 0 errors and 0
warnings, and `#print axioms KAM.Provider.Nekhoroshev.partialConvex_nekhoroshev` (whose proof uses `nf`) shows
only `propext`, `Classical.choice` and `Quot.sound`.
- **Scope:** `KAM/Nekhoroshev/Partial/NormalFormInduction.lean` (K1, 750 lines) and `NormalForm.lean` (K2, 635
  lines; the signed `nf`).
- **Read against:** the signature file with ruling F2-C1, design rows 216–224 and 367–368, blueprint p11b
  L141–160, the DEPGRAPH records of `bpN:p11:nf` and its steps, and every upstream lemma consumed.

## Verdict

**N11-K1/K2 `nf`: PASS WITH NOTES.** No fidelity, soundness or hygiene defect.

## (a) Signed declarations

| Declaration | Compared against | Result |
|---|---|---|
| `nf` (K2:605–628) | signature file L414–437 | IDENTICAL after whitespace normalization |
| `iterative` (consumed) | signature with F2-C1 `hc` | IDENTICAL |
| `ExtNFHyp` (consumed) | signature L343–365 | IDENTICAL |

`nnfMap` is literally `extFlow b R s ρ σ (homGenerator K Λ h f) 1`, the `Φ` of `iterative`. F2-C1 is honoured:
`hc` comes from `nnf_c_pos` (`radius_pos`, `slow_width_pos`); `nf` itself is unchanged.

## (b) Node coverage

| Node | Declaration or step | Result |
|---|---|---|
| `bpN:p11:nf` | signed `nf`: `nnf_caseA` / `nnf_caseB` | PASS (radius tails of (c): K-1) |
| `stepN:p11:nf-sl` | `nnf_slowLoss`, `nnf_slow_at`, `nnf_caseB_step` | PASS |
| `stepN:p11:nf-first` | `iterU_first`, `nnf_small_at` at i = 0 | PASS |
| `stepN:p11:nf-case` | `nnfBound_caseA`, `nnfBound_caseB`, `nnf_caseB_step`, `nnf_caseB` | PASS (constant: K-2) |
| `stepN:p11:nf-N` | `nnf_floor`, `nnf_sixtwo` | PASS (K-2) |
| `stepN:p11:nf-induct` | `nnf_induct_step`, `nnf_star_at`, `nnf_inv_succ`, `nnf_inv_all` (induction on i) | PASS |
| `stepN:p11:nf-concl` | `nnf_chain_*` (extended telescope), `nnf_chain_identity` | PASS |
| `stepN:p11:nf-disp` | `nnf_chain_disp`, `nnf_disp_T`, `nnf_disp_slow`, `nnf_disp_slow_B` | PASS (K-1, K-2) |
| `stepN:p11:nf-real` | `NnfInv` reality, `iterative` (e), `nnf_chain_real` | PASS |

The induction is over the iteration count (`nnfState` by recursion on i, `nnf_inv_all` by induction on
i ≤ N+1), with the blueprint's constants: losses R/8, s/6 then R/(8N), s/(4N); ε₁ = 2⁷qε²/(ᾱRs);
B_{j+1} = ε₁/4^j; N = ⌊κ/(12 ln 2)⌋. The final bounds of `nf` are derived, not assumed.

## (c) Soundness

- `NnfStep` is output-only; `NnfInv` is discharged by `nnf_inv_zero` and `nnf_inv_succ`; `NnfConcl` is the
  `nf` conclusion verbatim. Every conditional helper has its premises discharged from `ExtNFHyp`, `hsmall`
  or the case split.
- The witness `f_{i+1}` is `(h+g+f)∘Φ − h − g₊`, so the identity holds by definition; class, bound and reality
  are transferred from `iterative` by `EqOn` on `Dom(R−2ρ, s−2σ)`.

## (d) Hygiene

Lines at most 100 characters; no forbidden tokens; `check_lean_modules.py` PASS; none of the 77 public short
names occurs elsewhere in KAM; no root shadow; M-2 of N11-M-audit-1 is satisfied.

## Findings

- **K-1 (low, graph-literal coverage).** The node conclusion (c) of `bpN:p11:nf` and step `nf-disp` carry the
  tails `qKε/α ≤ R/2⁷`, `(1/8)qKε/α ≤ R/2¹⁰` and "physical slow displacement ≤ w/2¹⁰", which the signed `nf`
  omits. Fixed: the unsigned export `nnf_disp_radius` (K2) states the three tails from the premises of `nf`;
  the graph notes cite it.
- **K-2 (low, step-literal intermediate constants).** Case B proves `|f₁| ≤ (32/31)(3/4)e^{-κ/6}ε ≈ 0.774…`
  rather than `< 0.64…`; weights `≤ 1` rather than `≤ 1/2` for j ≥ 1; `8N ≤ κ` non-strict; Case B
  displacements are bounded by the Case A bounds rather than half of them. The consumed conclusions are all
  proved. Recorded in the graph `LEAN_NOTE`s; no change.
- **K-3 (info, docstring), K1:506.** "(in fact `≤ 1/2`)" was asserted but not proved. Removed.
- **K-4 (info, duplication).** `nnf_B_nonneg`, `nnf_B_le_eps1` and `nnf_inClass_mono` copy existing public
  lemmas; reuse is optional and not done.
- **K-5 (info).** `NnfConcl` duplicates the signed conclusion; drift is caught by `exact` in `nf`.
- **K-6 (info, graph citation).** `LEAN_REF` of `bpN:p11:nf` and its steps is `nf`; helpers appear only in
  `LEAN_NOTE`. Done in the graph sync.
- **K-7 (info).** K2:313 is exactly 100 characters.
