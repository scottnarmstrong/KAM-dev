# Handoff DESIGN-N67b (Revision 2 of the N Parts 6-7 Lean design)

## Files
- `docs/tracks/N/design/PART67-LEAN-DESIGN.md` (committed on `inp-design-n67`): new Section 10 "Revision 2"; Sections 0.1/0.5/0.9,
  3.1, 7 (DAG, package table, totals), 7.1 (N6-2, N6-4 plans), 8 (consumer table) updated; Appendix A regenerated (1313 lines, Markdown).
- `/root/code/KAM-inp/.drafts/design/NPart67Signatures.lean` (untracked draft): 790 -> 854 lines, sha256 `c588818b1772d3f7e106aac256b8207623c8a142cf40ef0e778f0507b1945c9f`.
- Also committed: the audit report `docs/tracks/N/design/DESIGN-N67-design-audit-1.md` (was untracked).
- Scratch: `.drafts/scratch/NPart67Signatures.lean` (checked copy), `.drafts/scratch/NPart67Signatures.orig.lean` (v1), `.drafts/scratch/sigcheck-b.txt`.

## Approach (per finding)
- F1: `IsActionNorm` + `map_zero`, `smul` (audit's structure verbatim); `exit_ball` statement unchanged (now true).
- F2: `normal_form` + clause `(nfSteps K s = 0 ∨ iterU α p ε (r/8) (s/6) < exp(-κ/6)) → EqOn g (homRes K Λ f) (Dom n D (r/2) (s/6))`.
- F3: new `homGenParam`, `homResParam`, `RealOnParam`, `homological_param` (n angles, m parameters, ω : ℂᵐ → ℂⁿ) and bridges
  `homGen_eq_homGenParam`, `homRes_eq_homResParam`, `realOnParam_iff_realOn`; owner N6-2. Deviation from the audit's proposed text:
  `RealOn` (KAM/Canonical/Setting.lean:143) is square-only, so the reality clause uses the new `RealOnParam`.
- N1 q=1 wrapper documented; N2 facade moved to N6-7, `iterHyp_of_source` in `IterativeMap`, S7-6 after S7-3, summaries reconciled;
  N3 consumer attributions corrected; N4 openness convention stated; N5 Mathlib citations corrected.

## Checks
- `inp_sig_check.sh /root/code/KAM-inp-design-n67 .drafts/scratch/NPart67Signatures.lean`: rc=0, 43 warnings, all
  "declaration uses 'sorry'" (39 old + 4 new theorems), no errors. (A first run failed on `RealOn` dimension mismatch; fixed by `RealOnParam`.)
- No `set_option`, no heartbeat override; no file > 1500 lines (the Lean draft is 854). Lint not run (no Lean module changed in the repo; Markdown only).
- Axioms: no proofs written; all theorem bodies `sorry`.

## Uncertainties
- F2's Case B is tested with the carried bound ε (upper-bound formulation), as the audit proposed; at the sharp norm it is the literal case.
- `homological_param`'s fast-coordinate bridge for Part 11 is budgeted there, not designed here.
- Re-audit of F1-F3 required before releasing the affected targets.

## Suspected errata / deviations
- Errata in pinned sources: none new.
- Deviations: `RealOnParam` (new predicate, bridged); Case B via carried bound.
