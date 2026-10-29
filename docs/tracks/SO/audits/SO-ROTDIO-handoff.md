# SO-ROTDIO prover handoff (branch inp-sorotdio, 98a2bc31; track SO package run by the main orchestrator)


**Files:** new `KAM/Certificate/DiophantineTransfer.lean` (only file; ~130 lines).

**Approach:** `isDiophantine_of_index_map`: apply `hω (T k)`, rewrite by `hdot`, and compare
`γ/(C^τ |k|₁^τ) ≤ γ/|T k|₁^τ` using `|T k|₁ > 0` (T k ≠ 0), `rpow_le_rpow` and `mul_rpow`.
Instances: private `rotIdx k = ![k 0, k 1 - k 0]` with C = 2, τ = 1 (private `rot_transfer`,
`rot_half`), then `norm_num` for `(1/21)/2^1 = 1/42`, `(1/42)/2 = 1/84`. The four public
declarations have exactly the signatures of the brief.

**Checks:**
- `inp_lake_build.sh ... KAM.Certificate.DiophantineTransfer`: "Build completed successfully", no warnings.
- `#print axioms` of all five public theorems: `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: no over-100-column lines, check_lean_modules PASS, FROZEN-ANCHOR GUARD OK,
  ABI HASHES OK; only remark: "KAM.lean is out of date" (generated; rule 10, orchestrator regenerates).
- `main_shortname_check.py`: short-name check OK.

**Uncertainties:** none. No errata, no deviations.

CONTEXT: owner ruling O5 (/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md, 'Owner ruling O5 and the replay gate'): the lunar certificate works in rotated angles with frequency (nu - 1, 1). The orchestrator FIXED the five signatures in the brief /root/code/KAM-inp/.drafts/briefs/offload-main/SO-ROTDIO.md (design Revision 5 adopts them verbatim): the generic isDiophantine_of_index_map and four lunar instances. Check that the generic lemma's hypotheses are genuine side conditions (nonnegativity, the index map's properties) and not conclusion-shaped, that it holds for all dimensions n, m, and that the four instances use exactly the landed IsDiophantine (KAM/Frozen/Defs/IsDiophantine.lean) and the landed SO-DIO theorems.

AUDIT FOCUS: the five declarations match the fixed signatures verbatim; soundness with no added premise. Audit ONLY KAM/Certificate/DiophantineTransfer.lean. Common to all: (a) every SIGNED declaration = its fixed signature EXACTLY (including fully qualified names); (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no public short name reused from KAM or Mathlib, no harmful root shadow, lines <= 100, no native_decide or axiom.
