# N11-H: independent audit 1

Lane N (Zohar's team), 2026-10-28. This is an independent, refute-first, read-only audit. Nothing was compiled
during the audit; the gate build is recorded separately: commit `c7024739` on `zohar/n11`, 0 errors, and
`#print axioms KAM.Nekhoroshev.iterative` shows only `propext`, `Classical.choice` and `Quot.sound`.
- **Scope:** `KAM/Nekhoroshev/Partial/Iterative.lean`, `IterativeMap.lean` and `IterativeRemainder.lean`
  (N11-H, `iterative`), 915 lines in all.
- **Read against:** the signature file (with ruling F2-C1), the design row, blueprint p11b L126–138, and
  every upstream lemma the three files consume.

## Verdict

**N11-H `iterative`: PASS WITH NOTES.** No soundness or fidelity defect.

## (a) Signed declarations

| Declaration | Compared against | Result |
|---|---|---|
| `iterative` (Iterative.lean:44–88) | N11-SIGNATURES.md as amended by F2-C1 | IDENTICAL after whitespace normalization |
| same | the original N11-SIGNATURES.md | differs only by `(hc : 0 < b.c)` after `hSL` (ruling F2-C1) |

`canonical_map` and `hom` are imported, not redefined.

## (b) Node coverage

| Node | Declaration or step | Result |
|---|---|---|
| `bpN:p11:iterative` | signed `iterative`, including the Revision 2 F2 exports | PASS |
| `stepN:p11:it-gen` | `NitHyp.nit_hom`, `nit_V_le`, `nit_V_half` | PASS |
| `stepN:p11:it-map` | `canonical_map`, `nit_disp`, `nit_injOn` | PASS |
| `stepN:p11:it-taylor` | `nit_remainder_core` with `ext_taylor_second` along `traj_solution` | PASS |
| `stepN:p11:it-est` | `nit_integrand_bound`, `nit_remainder_core`, `NitHyp.nit_remainder` | PASS |

## (c) Soundness

- All 16 fields of `NitHyp` are verbatim premises of the signed theorem; Iterative.lean:91 builds it
  one-to-one. No field has the shape of a conclusion, and every `ExtCompose` field is derived from it.
- Conditional helpers (`nit_disp`, `nit_integrand_bound`, `nit_remainder_core`) are discharged inside the
  proof; none stands in for a source result.
- The witness `fp` is defined as `H∘Φ − h − g₊`, so the identity clause holds by definition; the content is
  its class and bound, proved through `EqOn` with `𝓡 + (f − T_K f)∘Φ` on `Dom(R−2ρ, s−2σ)`.
- The same `Φ = extFlow b R s ρ σ φ 1` is used in `canonical_map`, in `composition` and in the witness.

## (d) Hygiene

- Lines are at most 99 characters. No `sorry`, `admit`, `axiom`, `set_option` or `EuclideanSpace`.
- None of the 55 public short names occurs elsewhere in KAM; no full-name clash; no clash with K1/K2.

## Findings

- **H-1 (low, docstring), IterativeMap.lean:335.** The docstring of `NitHyp.nit_hom` called it "the signed
  `hom` (`bpN:p11:hom`)", but it drops the `P_Λ φ = 0` clause. Fixed: it now says it is a specialization,
  with no node id, so a graph sync cannot cite it for `bpN:p11:hom`.
- **H-2 (info), IterativeMap.lean:279.** The field `NitHyp.nit_c` is unused. Kept as documentation.
- **H-3 (info), IterativeMap.lean:11.** `import Mathlib.Tactic.DefEqTransformations` was unused. Removed.
- **H-4 (info, duplication).** `nit_injOn`, `nit_freq_im` and `nit_fast_mem` re-prove existing lemmas.
  The reuse is optional and not done.
- **H-5 (info, packaging).** The package adds the module paths `IterativeMap` and `IterativeRemainder`;
  `KAM.lean` is regenerated at integration.
- **H-6 (info, provenance).** The landed files are the gate-built ones.
