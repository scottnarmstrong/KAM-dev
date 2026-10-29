# SO-NORM independent audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-sonorm`.
Audited HEAD: `1c25459165ccd3d6b4ab1e25c87cb1230c113e0b`.
Comparison ref `inp` at audit: `6cad95806f4dbeafc1933f733daf875fdb3b097a`.

## Verdict

**PASS WITH NOTES** for SO-NORM; all five signed declarations **PASS**. The §E slice is complete,
with no proof or statement defect found. The sole qualification is the expressly permitted stale
generated `KAM.lean` lint error; see the exact lint receipt below. No frozen theorem anchor is
implemented or sealed by this helper package, so per-anchor seal-readiness is not applicable.
This verdict does not certify SO-SOUND, the full checker, or a lunar certificate.

Authority: `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`,
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the local
`docs/tracks/SO/audits/SO-NORM-handoff.md`, especially AUDIT FOCUS. The user's exact absolute
report path overrides the generic brief's main-worktree destination. Audit scope is only
`KAM/Certificate/NormBridge.lean`; existing dependencies were inspected to establish the norm
and import contracts, not re-audited as packages.

Specification: `/root/code/KAM-inp/.drafts/design/SOSignatures.lean:776–814`, §E, inside
`namespace KAM.Certificate`; Revision 4 design at
`/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md`, §1.3, §7 SO-NORM,
and Appendix A §E (L1361–1399). The signature section and design appendix agree after whitespace
normalization. The project plan at `/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md`
places this package among unfrozen helper modules. There is no local SO statement.md; the
handoff's exact design/signature sources are the applicable specification for this package.

## Declaration-by-declaration review

Line numbers refer to `KAM/Certificate/NormBridge.lean`.

| Node / role | Fully qualified declaration | Verdict | Reason |
|---|---|---|---|
| Basis expansion | `KAM.Certificate.sum_sumVec_smul_phaseBasis` (L33) | PASS | Reconstructs every phase vector; no dimensional premise. |
| Coordinate control | `KAM.Certificate.norm_sumVec_apply_le` (L41) | PASS | Each flattened coordinate is bounded by the product max norm. |
| Linear norm bridge | `KAM.Certificate.norm_clm_le_sum_phaseBasis` (L47) | PASS | Arbitrary complex normed codomain; stronger supporting generality. |
| §E.1 signed | `KAM.Certificate.norm_fderiv_le_sum_partials` (L57) | PASS | Exact signed type; no differentiability premise needed to bound an existing fderiv. |
| Bilinear norm bridge | `KAM.Certificate.norm_cmm_two_le_sum_phaseBasis` (L63) | PASS | Isometric currying twice; sums over both phase inputs. |
| §E.2 signed | `KAM.Certificate.norm_iteratedFDeriv_two_le_sum_partials` (L78) | PASS | Exact signed type and two-index sum; no extra premise. |
| Angle basis | `KAM.Certificate.phaseBasis_inl` (L85) | PASS | Identifies the angle basis with (Pi.single j 1, 0). |
| §E.3 signed | `KAM.Certificate.hamiltonianVectorFieldℂ_sumVec` (L91) | PASS | Exact signed type, coordinate swap, and Hamiltonian signs. |
| Coordinate sign definition | `KAM.Certificate.hamSign` (L100) | PASS | Total +1 on angle indices and -1 on action indices. |
| Sign norm | `KAM.Certificate.norm_hamSign` (L102) | PASS | Both complex signs have norm one. |
| Vector-field coordinates | `KAM.Certificate.sumVec_hamiltonianVectorFieldℂ_swap` (L105) | PASS | Equivalent swap/sign formulation of §E.3. |
| Vector-field transport | `KAM.Certificate.hamiltonianVectorFieldℂ_eq_symm` (L111) | PASS | Exact identity through the inverse linear isometry; no replacement field. |
| First derivative coordinates | `KAM.Certificate.sumVec_fderiv_hamiltonianVectorFieldℂ` (L120) | PASS | Local C² suffices for the chain rule; no global regularity premise. |
| §E.4 signed | `KAM.Certificate.norm_fderiv_hamiltonianVectorFieldℂ_le` (L143) | PASS | Exact local C² and 1 ≤ n premises; row bound gives B ≥ 0 and operator bound with constant 1. |
| Third derivative formula | `KAM.Certificate.iteratedFDeriv_three_apply` (L165) | PASS | Unfolds the nested fderiv convention; no smoothness premise required for this identity. |
| First-slot swap | `KAM.Certificate.iteratedFDeriv_three_swap_first` (L171) | PASS | Local C³ implies symmetry of D²(DH); swaps first two inputs. |
| Last-slot swap | `KAM.Certificate.iteratedFDeriv_three_swap_last` (L178) | PASS | Differentiates the eventual symmetry of D²H; local C³ suffices. |
| Third derivative rotation | `KAM.Certificate.iteratedFDeriv_three_rotate` (L196) | PASS | Two proved swaps rotate the last input into first position. |
| §E.5 signed | `KAM.Certificate.norm_iteratedFDeriv_two_hamiltonianVectorFieldℂ_le` (L202) | PASS | Exact local C³ and 1 ≤ n premises; isometry, coordinate chain rule, rotation, and bilinear bound give constant 1. |

All five signed headers match the signature file modulo whitespace and the section-generated
implicit `{n : ℕ}`. Binder order, implicitness, fully qualified export names, regularity order,
row sums, and conclusions agree. A scratch probe copied each signature under a fresh name,
proved it by applying the real export to exactly its explicit binders, and checked the fully
explicit types using `type_of% @...`. All ten checks elaborated at default resource settings.
No signed obligation is replaced by a conditional helper.

## Proof and consumer compatibility

The domain is literally `(Fin n → ℂ) × (Fin n → ℂ)` with Mathlib's Pi max norms and product
max norm. `KAM.Torus.sumVec` and `sumVecIso` (`KAM/Torus/Basic.lean:54–75`) identify this
space isometrically with `Fin n ⊕ Fin n → ℂ`. Coordinate expansion bounds continuous linear
maps and continuous bilinear forms with these exact norms. There is no dimension factor,
change to an ℓ² carrier, or hidden norm equivalence constant.

The frozen field is exactly `KAM.hamiltonianVectorFieldℂ`, from
`KAM/Frozen/Defs/HamiltonianVectorFieldC.lean:26`, namely `(∂I H, -∂θ H)`.
The swap/sign identity is an identity of that field. Its derivative estimates use the genuine
`fderiv ℂ` and `iteratedFDeriv ℂ 2` operator norms. These are literally the four derivative
quantities in `KAM/Iso/Charts/Inputs.lean:54–56` (`IG1Body`), with the same scalar, domain,
and codomain. The remaining zeroth-order field bound in IG1Body is obtainable from §E.3 and
the product/Pi max norm; §E does not assign a separate signed norm theorem for that bound.

For DX_H, Hessian symmetry moves the fixed swapped coordinate to the row position. For D²X_H,
linear isometry preserves the multilinear norm; coordinatewise differentiation produces D³H,
and the two independently proved swaps rotate the fixed coordinate to the first position
before the bilinear estimate. Local C²/C³ are the signed source premises, not assumptions of
the desired inequalities. The row bounds are concrete partial-derivative inputs to a genuine
operator-norm bridge. No hard analytic conclusion is hidden in an instance or structure.

The first two signed inequalities remain valid at n = 0. In the last two, `1 ≤ n` supplies
an actual row and hence `0 ≤ B`, preventing the already documented F8 empty-index/negative-B
counterexample. This is the revised signed contract, not an auditor-introduced strengthening.
All constants are exactly 1 and B is passed unchanged.

## Definition classification and imports

The only new definition/abbreviation/structure is `KAM.Certificate.hamSign` (L100):
`Sum.elim (fun _ => 1) (fun _ => -1)`. It is total and correct on every index for every n;
for n = 0 its carrier is empty. It has no exceptional branch, junk value, or fallback.
It lies in `@[expose] public section`. There are no new abbreviations, structures, instances,
or root declarations. Every new public name lies under `KAM.Certificate`.

All 19 short declaration names were searched against KAM and installed Mathlib source
(including indented declarations and qualified declaration names); exactly 19 declaration
hits, all in the audited module, and zero outside it. No harmful root shadow was found.
The direct KAM imports are PhaseBasis and the frozen HamiltonianVectorFieldC definition;
the two other direct imports are Mathlib calculus modules. Recursive KAM import inspection
found 24 KAM modules, no provider modules, and 11 manifest-listed frozen declarations, all
SEALED. In particular the directly imported HamiltonianVectorFieldC definition is SEALED.
No DRAFT_SORRY theorem is imported.

## Independent validation receipts

All commands ran from this worktree. Every Lean/Lake invocation used `LEAN_NUM_THREADS=1`
and `nice -n 5`; build, probe, kernel replay, and repository lint were serialized. No clean,
update, cache retrieval, heartbeat override, or write to dependencies was performed.

### Diff and static checks

```text
git diff inp...HEAD --stat
 KAM/Certificate/NormBridge.lean | 258 ++++++++++++++++++++++++++++++++++++++++
 1 file changed, 258 insertions(+)

git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
<empty; exit 0>

git diff --check inp...HEAD
<empty; exit 0>
```

The complete three-dot diff was read. `git status --short` initially showed only the existing
untracked `docs/tracks/SO/audits/SO-NORM-handoff.md`. The source has 258 physical lines
(the handoff says 257) and maximum line width exactly 100 Unicode characters. Module header,
copyright, public imports, module docstring, and public section are present. A source scan
found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `native_decide`, `EuclideanSpace`,
or `set_option` override.

### Targeted build

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sonorm KAM.Certificate.NormBridge
[inp-gate] slot 1 acquired 14:23:45 for KAM.Certificate.NormBridge
Build completed successfully (2886 jobs).
exit 0
```

### Signature, explicit-body, and axiom probe

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SONormAudit.lean > .lake/abi-scratch/SONormAudit.log 2>&1
exit 0
```

The five copied signatures were proved with these bodies, respectively:

```lean
by exact KAM.Certificate.norm_fderiv_le_sum_partials z
by exact KAM.Certificate.norm_iteratedFDeriv_two_le_sum_partials z
by exact KAM.Certificate.hamiltonianVectorFieldℂ_sumVec H z a
by exact KAM.Certificate.norm_fderiv_hamiltonianVectorFieldℂ_le hn hH hB
by exact KAM.Certificate.norm_iteratedFDeriv_two_hamiltonianVectorFieldℂ_le hn hH hB
```

For each fresh declaration `SONormAudit.check_<name>`, the probe also elaborated
`example : type_of% @SONormAudit.check_<name> := @KAM.Certificate.<name>`.
These are the helper-package analogue of the brief's provider/frozen-type and seal-body checks;
there is no provider export or frozen theorem seal body in this scope.

Exact `#print axioms` output for all 18 new public theorems:

```text
'KAM.Certificate.sum_sumVec_smul_phaseBasis' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_sumVec_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_clm_le_sum_phaseBasis' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_fderiv_le_sum_partials' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_cmm_two_le_sum_phaseBasis' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_iteratedFDeriv_two_le_sum_partials' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.phaseBasis_inl' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hamiltonianVectorFieldℂ_sumVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_hamSign' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sumVec_hamiltonianVectorFieldℂ_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hamiltonianVectorFieldℂ_eq_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sumVec_fderiv_hamiltonianVectorFieldℂ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_fderiv_hamiltonianVectorFieldℂ_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.iteratedFDeriv_three_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.iteratedFDeriv_three_swap_first' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.iteratedFDeriv_three_swap_last' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.iteratedFDeriv_three_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_iteratedFDeriv_two_hamiltonianVectorFieldℂ_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The printed `hamSign` body was also checked against the total definition above.

### Kernel replay

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.NormBridge > .lake/abi-scratch/SONormKernel.log 2>&1
replaying KAM.Certificate.NormBridge
exit 0
```

One invocation replays the sole new lemma module; there is no separate provider module.

### Repository lint

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh > .lake/abi-scratch/SONormLint.log 2>&1
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1291 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole failure is the exact generated-root exception authorized by the audit brief.
All substantive lint gates pass. `KAM.lean` was not regenerated.


## Findings, limitations, and handoff

No suspected source, blueprint, frozen-definition, or proof defect was found in this scoped
review. The F8 n = 0 defect is already repaired in both the signed specification and this
implementation; no new erratum is proposed. No mathematical deviations were introduced.
The handoff's physical line count differs by one, with no effect on the 1500-line limit.

Only this report is a new repository edit by the auditor. Scratch probes and their logs were
confined to this worktree's `.lake/abi-scratch/` and removed after incorporating the receipts.
Frozen files, manifest, generated root, README, source modules, and the pre-existing handoff
were untouched. No state-changing git command was run.
