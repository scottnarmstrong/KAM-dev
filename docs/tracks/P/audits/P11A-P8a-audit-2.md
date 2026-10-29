# P11A-P8a independent audit 2

Overall verdict: **PASS WITH NOTES for the assigned P8a slice**. Audit 1's F1 (missing complex domain chain and `rz/4` bound) is repaired at the audited HEAD. The selected signed clauses, quantifier order, source-only final hypotheses, proof validity and substantive hygiene checks pass. The generated-root lint exception is permitted by the audit brief. No frozen anchor is supplied or sealed by this package; per-anchor verdict is **N/A**.

## Snapshot, authority and scope

- Worktree: `/root/code/KAM-inp-p11ap8a`.
- Audited HEAD: `65cd093e629747299ce90de1a91ad4a4efb88024`.
- Comparison ref `inp`: `c1839fee225146e0c60e389ca73433801f3a9c52`.
- Requested comparison: `git diff inp...HEAD`. Git warns `multiple merge bases, using a2464f937a8b578ae414ec08331359284ec94a78`; this comparison was retained literally.
- Full diff inventory: 16 files, 3599 insertions, one deletion. This includes the audited 649-line PreparedBasic module, PreparedData, the Slow facade and nine Slow proof modules, and four P7c/P8a audit/handoff documents. Dependency/inherited files were inventoried; only PreparedBasic is certified here, as the AUDIT FOCUS requires.
- Signature authority: `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`, SHA256 `fd2c245ea48f1b99f36beb02bba0095e9a55b070be0eae178198fdf20011b9e9`.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package audit brief, P8a handoff and audit 1, Track P statement, P11A design decisions/node table/prepared registry, the two DEPGRAPH records, blueprint-P/parts/p11-cp09-preparation.tex:187-212, and the relevant signed prepared definitions and theorem. The downstream FixedSunPlanetaryKAM anchor and its set definition were inspected for context; they are not imported by this package and are not audited for sealing here.

The explicit 01:05 split ruling assigns P8a only `pr-basic` and `pr-a`. P8b/P8c/P8e retain the frequency, derivative, jet, scalar, amount and final `prepared` assembly obligations. PreparedData is treated as the supplied imported interface, not re-audited; audit 1 records that its audit status was corrected to a separate data audit. This report makes no claim that that separate audit has completed.

All repository edits are confined to this report at the user's exact absolute path, overriding the generic brief's main-worktree destination. Temporary audit files were under `.lake/abi-scratch/` and removed. No production source, generated root, frozen file, manifest or git state was changed.

## Audit 1 F1 and graph coverage

| Contract | Verdict | Evidence |
|---|---|---|
| `stepP:p11:pr-basic` | PASS on the signed prepared carrier | `p11PreparedCoreOf_chain_dom`, `P11PreparedDomSpec`, `p11_prepared_basic_dom`, and the basic holomorphy/reality/identity exports. Exact complex polar-image radius `rz/4`, not `rz/2`. |
| `stepP:p11:pr-a` | PASS | `p11PreparedCoreOf_P_bound` and the bound conjunct in `p11_prepared_basic`; the source weighted-to-sup and c2-to-c steps are proved. |
| Corresponding clauses of `P11PreparedSpec` | PASS | Whitespace-normalized source comparison and elaborated projection from a fresh copy of the signed spec. |
| Frozen theorem/provider equality and seal body | N/A | No provider or frozen theorem is implemented in this slice. |

F1 authority remains `docs/graph/P/DEPGRAPH.md:20562`, design `P11A-LEAN-DESIGN.md:388`, and blueprint `p11-cp09-preparation.tex:206`: “Theta hat into T_{sigma_F/6} x D(J_0, s_2) x B_{r_z/4} in D_1 prime”.

The repair at PreparedBasic.lean:429-486 establishes, for an arbitrary complex point of the signed prepared domain, all of:

1. Rescaling into strip `sigma/72` and the half slow box.
2. Psi into strip `sigma/12` and the full slow box.
3. Polar image into `WorkingDom (sigma/6) s2 (rz/4)`.
4. The same image in `D1' = WorkingDom (sigma/6) (s1/2) (rz/2)`.
5. Fast.map of that image into `D1 = WorkingDom sigma s1 rz`.

The proof keeps J unchanged through the polar map, yielding the literal s2 action radius. From the source estimate `norm(p11PolPt) <= 4*sqrt eps`, it derives the stronger oscillator radius using `256*eps < rz^2`. This is proved for complex inputs, rather than only a rescaled real input as in audit 1. `P11PreparedDomSpec` at :520 exports these exact memberships. The expected-type and projection probes verify that the new result really includes the s2/rz/4 clause.

At :588-634, `p11_prepared_basic_dom` chooses the minimum of `u/2`, `eps1`, the selected slow eps2, `exp(-1)/MF`, and `rz^2/257`. This last term replaces the old `rz^2/65`; positivity and the strict 256 inequality are proved internally. Thus the repair adds no external smallness premise and no dependence of eps3 on c or W. `p11_prepared_basic` at :638 projects its original basic-spec conclusion from this stronger theorem. Audit 1's stale nonexistent docstring reference is removed.

The carrier is exactly the signed `complexStrip (sigma/72) × actionNbhd preparedBox 1`. As in audit 1, this does not claim holomorphy on every point of the larger blueprint E. This signed carrier contains all smaller action neighbourhoods appearing in the prepared interface, including the 3/4 frequency tube and 1/4 thickening. No consumer needs the larger E for the selected clauses. The physical Hamiltonian export is the exact real identity in the signed specification; it does not purport to make the real physical chart complex-valued. The source-form complex composition is the composition of the original `hf2` and `hid` clauses, used in `chain_eq` (:347-352, :414), with domain membership proved rather than assumed. The new domain exports pay the previously missing complex geometric obligation.

## Declaration review

All names below are in `KAM.Planetary`; line numbers are in `KAM/Planetary/Preparation/PreparedBasic.lean`.

| Node / purpose | Declaration | Line | Verdict | Reason |
|---|---|---:|---|---|
| pr-basic construction | `p11PreparedCoreOf` | 39 | PASS | Explicit N, P, chart chain, and caller-supplied W; no fallback. |
| pr-basic construction | `p11PreparedCore` | 50 | PASS | Specializes the construction to the selected signed stage outputs. |
| geometry | `p11RescaleReal` | 55 | PASS | Intended total real affine rescaling. |
| geometry | `p11Rescale_real` | 59 | PASS | Exact compatibility with real inclusion. |
| geometry | `p11Box_isOpen` | 73 | PASS | Finite intersection of open coordinate discs; empty-radius cases valid. |
| geometry | `p11Box_mono` | 80 | PASS | Literal coordinatewise radius monotonicity. |
| geometry | `p11_actionNbhd_norm_lt` | 85 | PASS | Signed unit action neighbourhood gives coordinate norms below 3/2. |
| pr-basic first arrow | `p11Rescale_mem_box` | 98 | PASS | Half slow box follows from pi*eps <= s2 and 3 < pi. |
| geometry | `p11Rescale_differentiable` | 125 | PASS | Globally complex differentiable affine map. |
| pr-basic first arrow | `p11Rescale_mem_dom` | 133 | PASS | Correct strip sigma/72 = sigma/12/6 and half-box radii. |
| pr-basic holomorphy | `p11PreparedCoreOf_N_differentiableOn` | 143 | PASS | Source h0/g2 holomorphy composed with the proved rescaling inclusion. |
| pr-basic holomorphy | `p11PreparedCoreOf_P_differentiableOn` | 166 | PASS | Source f3 holomorphy composed with the rescaling. |
| pr-basic periodicity | `p11PreparedCoreOf_P_periodic` | 178 | PASS | Period-one coordinate shifts, as in the selected signed clause. |
| arithmetic | `p11_im_div_ofReal` | 191 | PASS | Complex division identity; valid also for zero denominator. |
| pr-basic reality | `p11PreparedCoreOf_rescale_real_mem` | 195 | PASS | Real affine image in the required slow domain. |
| pr-basic reality | `p11PreparedCoreOf_N_real` | 205 | PASS | Source h0/g2 real on the real slice; real division. |
| pr-basic reality | `p11PreparedCoreOf_P_real` | 225 | PASS | Source f3 RealOn transferred by real rescaling. |
| pr-basic reality | `p11PreparedCoreOf_NP_real` | 237 | PASS | Sum of the two real quantities. |
| pr-a norm bridge | `p11_norm_le_of_wbound_open` | 255 | PASS | Local open action ball supplies Weighted.InClass and WBound; applies sup_le_wbound. |
| stepP:p11:pr-a | `p11PreparedCoreOf_P_bound` | 278 | PASS | Correct pointwise supremum bound, exponent, log power and division by positive eps. |
| pr-basic polar reality | `p11_slowBox_re_pos` | 310 | PASS | Oscillator-action real parts exceed pi*eps on V2. |
| pr-basic Hamiltonian identity | `p11PreparedCoreOf_chain_eq` | 326 | PASS | Source identities composed through the real chart; exact signed physical identity. |
| pr-basic complex chain | `p11PreparedCoreOf_chain_dom` | 429 | PASS | All five complex domain arrows; literal s2 and rz/4 bound, then D1-prime and D1. |
| selected signed clauses | `P11PreparedBasicSpec` | 496 | PASS | Retained signed clauses verbatim modulo whitespace and omitted unused lets. |
| pr-basic complex chain | `P11PreparedDomSpec` | 520 | PASS | Explicit complex pointwise domain-chain proposition with no bundled assumptions. |
| source chart projection | `p11_secular_ham_chart` | 542 | PASS | Extracts the original chart identity from SecularSpec. |
| conditional assembly | `p11_prepared_basic_of_spec` | 553 | PASS | Distinct conditional helper; source specs and smallness discharged by the final theorem. |
| pr-basic / pr-a assembly | `p11_prepared_basic_dom` | 588 | PASS | eps3 before eps/c/W; all source specs and 256*eps < rz^2 derived internally. |
| pr-basic / pr-a assembly | `p11_prepared_basic` | 638 | PASS | Same expected public type as before; projects the basic spec from the stronger theorem. |

## Definitions and premises

The five definitions in scope are intended total constructions, not proof-bearing substitutes:

- `p11PreparedCoreOf`: literal affine pullbacks defining N and P divided by eps; real chart chain through Fast.map/polar/Psi; `checkW` is exactly W. There is no conditional fallback. Its real-part projection is justified on the theorem's real domain by source reality.
- `p11PreparedCore`: specialization to the imported selected secular/fast/slow data. The existence proof obtains the source specifications of those very selections on the small-eps interval, so no default branch is used by the result.
- `p11RescaleReal`: literal real affine rescaling on the whole carrier.
- `P11PreparedBasicSpec`: conjunction of the selected signed clauses, with unused frequency/patch lets removed; not an input assumption to the final theorem.
- `P11PreparedDomSpec`: explicit complex domain conclusions; no output data bundled as a premise.

The generic per-clause lemmas use the relevant source holomorphy, periodicity, reality, bounds and chart identities. The conditional assembly has a distinct `_of_spec` name and is not substituted for the unconditional source result. The final public existence theorems assume only D and `1 <= nu`. Their order is `exists eps3 > 0; forall eps > 0, eps <= eps3; forall c >= p11SlowConstant D nu; forall W`. The arbitrary W is stronger uniformity and supports later assembly.

`pr-a` uses an open action ball to instantiate the original weighted norm's sup bound, not an alternate norm. Division is by positive eps. The arithmetic identity is `eps^(nu+3/2)*eps = eps^nu*eps^(5/2)`. At :576-580 the resulting c2 bound is enlarged to c using the nonnegative rpow factors, with log nonnegativity derived from source smallness. No hard step is imported as an extra conclusion-shaped hypothesis.

## Interface and axiom probes

The temporary probe `.lake/abi-scratch/P11AP8aAudit2.lean` imported only the audited module. It contained:

- A fresh renamed copy of signed `P11PreparedSpec`; equality with the imported specification by `rfl`.
- Projection of all retained clauses, including the final physical identity: destructure the 14 conjuncts as `a,b,d,e,f,g,i,j,k,l,m,o,p,q`, return `a,b,d,e,f,g,i,j,q`.
- Explicit expected types for both `p11_prepared_basic` and `p11_prepared_basic_dom`, preserving every binder, eps3 dependence, threshold and W quantifier.
- Projection from `P11PreparedDomSpec` to the complex polar-image conclusion with literal s2 and rz/4.
- `#print axioms` for every one of the 29 public declarations, including all definitions.

A separate source comparison removed precisely the five deferred frequency/jet/scalar conjuncts from the signed spec and compared the retained body with BasicSpec, removing only whitespace. Output:

```text
Retained signed clauses equal modulo whitespace: True
Public declarations: 29 file lines: 649 max width: 100
```

These checks establish fidelity to the given PreparedData interface, not a second audit of that module. No signed name is redefined by PreparedBasic.

## Validation commands and results

All Lean/Lake, kernel and lint commands ran serially, with `LEAN_NUM_THREADS=1` and `nice -n 5`. Lint was serialized as well because its ABI check invokes Lean. Default elaboration resource limits were used throughout.

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap8a KAM.Planetary.Preparation.PreparedBasic
[inp-gate] slot 1 acquired 01:33:40 for KAM.Planetary.Preparation.PreparedBasic
Build completed successfully (9419 jobs).
exit 0
```

PreparedBasic warnings: deprecated `dif_pos` at 598:32, 623:8, 629:8, recommending `dite_eq_left`. Replayed dependencies also emit existing unused-variable/simp/deprecation warnings. No elaboration failure occurred.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AP8aAudit2.lean
exit 0
```

All examples elaborated without diagnostics. Exact axiom output:

```text
'KAM.Planetary.p11PreparedCoreOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11RescaleReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Rescale_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Box_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Box_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_actionNbhd_norm_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Rescale_mem_box' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Rescale_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Rescale_mem_dom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCoreOf_N_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCoreOf_P_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCoreOf_P_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_im_div_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCoreOf_rescale_real_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCoreOf_N_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCoreOf_P_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCoreOf_NP_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_norm_le_of_wbound_open' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCoreOf_P_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slowBox_re_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCoreOf_chain_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCoreOf_chain_dom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11PreparedBasicSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11PreparedDomSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_secular_ham_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prepared_basic_of_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prepared_basic_dom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prepared_basic' depends on axioms: [propext, Classical.choice, Quot.sound]

```

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.PreparedBasic
replaying KAM.Planetary.Preparation.PreparedBasic
exit 0
```

Only one new in-scope module exists, so this single kernel invocation covers the assigned package module.

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1192 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole lint failure is the stale generated `KAM.lean`, explicitly allowed by the audit brief. No root regeneration was performed; all substantive source, module, frozen-anchor and ABI checks pass.

Additional read-only checks:

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(empty stdout; multiple-merge-base warning on stderr)
exit 0

git diff --check inp...HEAD
(empty stdout; same warning)
exit 0
```

Source-mask scan: no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace` or `set_option` in the audited code. All 29 short names checked against other KAM source declaration names: no clash. The only namespace is KAM.Planetary; no harmful root shadow or new global instance. Module header, copyright, public imports, docstring and exposed public noncomputable section are present. File length 649, maximum Unicode line width 100. Recursive import scan: 373 KAM modules, no Provider module and no frozen theorem module; consequently no DRAFT_SORRY theorem is imported. Frozen definition interfaces remain given and protected.

## Notes, errata and limits

No pinned-source mathematical defect was established. No mathematical deviation was introduced by this audit. Two documentation notes remain:

1. The handoff describes the older 548-line implementation, `rz^2/65` cutoff and absence of a separate complex export. Current HEAD has 649 lines, the stronger domain theorem and `rz^2/257` cutoff. This report and the inspected repair commit supersede those descriptions.
2. PreparedBasic.lean:427 says “and `Theta-hat` maps it into `D_1`”. In its actual statement (:449-450), the final map is Fast.map (Phi^1); the polar/Theta-hat image lies in D1-prime. This is a docstring map-label error, not a false Lean conclusion: the formulas distinguish both stages correctly. Correcting that sentence is documentation upkeep, not a prerequisite to the proved radius chain.

The PASS is confined to the P8a clauses and the repaired domain chain over the signed prepared carrier, relative to the supplied stage interfaces. It does not certify PreparedData separately, complete P8b/P8c/P8e, prove the full signed `prepared`/`amount`, or seal P-FIXED or any campaign theorem.
