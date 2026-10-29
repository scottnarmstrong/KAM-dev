# E11 independent package audit 1

Verdict: **PASS WITH NOTES** for `KAM.Planetary.stopped` (ordinary library result ready for E12 consumption). No frozen anchor is proved or sealed by E11 itself. This audit does not certify E12 or `planetaryExponentialSafety`.

Audited 2026-10-29 in `/root/code/KAM-inp-p14-e11`, HEAD `87b04747904bf61ceb7123db851fd2e06e44c81f`, compared with `inp` at `23a055ed6eaa23e4cc5d0d57c6f3c7c42cabdd32` using the full `git diff inp...HEAD`. The diff contains only the 377-line module and the handoff. The handoff's `df9039a2` identifies the proof commit; current HEAD additionally records the audit request.

Scope: only `KAM/Planetary/Exponential/Stopped.lean`. Read AGENTS, PLAN, DECISIONS, the package audit brief, handoff/AUDIT FOCUS, P14 design (including N2 and Appendix A), signed `/root/code/KAM-inp/.drafts/design/P14Signatures.lean:363`, blueprint `blueprint-P/parts/p14a-amd-expsafe.tex:260–290`, track P statement's AMD/EXP sections, the frozen N root and relevant definitions. Dependency statements were inspected to check application, without reauditing their proofs. The user's exact report destination overrides the generic brief's main-worktree destination.

## Declaration and node review

All names below have prefix `KAM.Planetary`; line numbers refer to the audited module.

| Node / role | Declaration or proof location | Verdict | Reason |
|---|---|---|---|
| N domains | `fastBox_eq_pi` (48) | PASS | Literal equality with the product of open intervals, arbitrary real enlargement. |
| N domains | `isOpen_fastBox` (53) | PASS | Finite product topology, no positivity or admissibility premise needed. |
| N domains | `convex_fastBox` (57) | PASS | Product of convex intervals; also valid for empty boxes. |
| N domains | `isOpen_slowBall` (61) | PASS | Strict sublevel of the continuous quadratic sum, all n and A. |
| N domains / st-sol | `isOpen_workingCylinder` (64) | PASS | Intersection of the exact fast/slow preimages; ambient Pi/product max norms. |
| st-thr exponents | `planetaryTimeExponent_eq_partial` (75) | PASS | Same n fast actions, no replacement by 2n. |
| st-thr exponents | `planetaryDriftExponent_eq_partial` (79) | PASS | Exact drift exponent after algebraic normalization. |
| st-thr exponents | `planetaryDriftExponent_pos` (85) | PASS | Stronger than needed: every natural n. |
| st-core fast | `stopped_fast_erosion` (94) | PASS | Closed max-norm ball lies strictly in the enlarged open action box when epsilon < kappa. |
| st-core slow | `stopped_slow_erosion` (110) | PASS | Actual Cauchy–Schwarz proof on Fin n + Fin n; factor sqrt(2n) and closed-ball endpoints correct. The helper takes the sufficient sqrt inequality, derived in the caller. |
| st-sol sign | `stopped_hamiltonian_neg` (180) | PASS | Literal H(-h,-P) = -H(h,P), all inputs; no sign or time normalization lost. |
| st-sol forward | `stopped_isSolutionOn_forward` (192) | PASS | Restricts the given chart solution to [0,r], proves differentiability via open-domain field equality. |
| st-sol backward | `stopped_isSolutionOn_reverse` (215) | PASS | Uses y(-s), derivative -X_H, differentiability of -H, and the exact negative Hamiltonian. |
| bpP:p14:stopped | `stopped` (245) | PASS | Telescope byte-identical to signed source and design; fresh signature/application probes elaborate. |
| st-thr | `stopped` (252–278) | PASS | Two literal frozen N applications, exact domains and all required h/-h clauses discharged. |
| st-seg | `stopped` (308–323) | PASS | E9 lift preserves physical actions/AMD; outer region implies working-cylinder membership. |
| st-core | `stopped` (324–337) | PASS | Initial fast erosion and pointwise slow erosion derived from the tested segment. |
| st-phys | `stopped` (339–345) | PASS | Coordinate norm <= Pi max norm; same delta, including equality at the drift threshold. |
| st-bwd | `stopped` (351–364) | PASS | C=-l>0 only when t<0; tests -t within the precise N window and uses -P's normalized perturbation proof. |
| st-fwd | `stopped` (366–373) | PASS | C=r>0 only when t>0; tests t within min(r,N horizon), with slow erosion only through t. |

## Exact N-root invoice and quantifiers

At lines 253–259, `enlarge` supplies kappa,e,A and `perturbation` supplies rho,B0,P, with rho>0, rho<=kappa, B0>=1, both normalized perturbation predicates and the real trace identity. `h_data` supplies the collar and g,v,M with positivity and all analytic/definiteness clauses. The complex bound is the corrected **sum** of diagonal contributions, not the previously rejected maximum: `KeplerData.lean:238–262`.

Both calls (261–275) use n fast actions and k=n slow pairs, hn:2<=n and hk:1<=n; G=`fastBox B kappa`, G'=`fastBox B (2*kappa)`, D=`slowBall n A`; open G/G', convex G/G', open D; the same rho,g,v; rho>0; positive complex Hessian bound; and the closed-ball collar. For h the remaining arguments are exactly `hhol hC2 hreal hHess hdef`. For -h they are the three `keplerDataNeg_*` analytic/reality proofs, `hHess'`, and `hdefn`. The separately extracted M' is propositionally the same prescribed sum (`keplerDataNeg_hess_norm_le`, lines 407–419), so it introduces no wider dependence. No N hypothesis is left as an assumption of `stopped`.

The root's threshold is uniform in arbitrary normalized P, duration and curve. Although the chosen perturbation witness is already available, the two root calls do not take P; their thresholds retain that uniformity. B0 and nu0 are produced before mu,T,delta,z0 (line 293 versus 294). The finite minimum includes 1, both N thresholds and kappa^(1/b),epsD^(1/b). Positivity of b and epsD is proved; rpow inversion derives the strict erosion radii. No mu-, datum- or curve-dependent constants escape.

`StoppedActionBound` is unfolded literally: it assumes an arbitrary physical solution and outer-region membership only on its tested [l,r]. `hslow` derives erosion pointwise from physicalAMD<outerAMD, without using an N drift conclusion or assuming confinement on [-T,T]. Each N call restricts this established fact to [0,t] or the reversed [0,-t]. The exact horizon `T <= nu^-1 * exp(nu^(-a))`, nu=B0*mu, is preserved (346–347). At t=0 the action difference vanishes. One-sided intervals l=0 or r=0 cause no positive-duration obligation on the unused side; endpoint queries are included with <=, and HasDerivAt remains two-sided.

The helper premises are source data or local typing/solution facts. The forward/reverse helpers transport a supplied chart solution between identified systems; their names and uses remain distinct from the stopped estimate. No helper assumes a drift bound, whole-window slow confinement or other unpaid hard step.

## Definitions and quarantine

There are **no new def, abbrev or structure declarations** in E11. Local `set` expressions X,D,a,b,c,epsD,nu0,nu denote the literal finite vectors, square roots, exponents, gap and scaling in the proof; no fallback or junk object is used. The existing `fastBox`, `slowBall`, `workingCylinder`, `innerCore`, `IsSolutionOn`, `IsPartialPerturbation`, `HasDefiniteFastPart`, `degenerateHamiltonian` and `StoppedActionBound` retain their original carriers and meanings.

The sole frozen theorem reached by recursively tracing the ordinary KAM imports before crossing a theorem-anchor boundary is `KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev`; manifest entry `nekhoroshev.d25.partialConvex_nekhoroshev.v1` is **SEALED** (manifest line 9020). No direct/bypassing provider import or DRAFT_SORRY theorem import was found. Its provider is reached through the sealed anchor's authorized import. This is the released N2 interface; E11 does not bypass quarantine.

## Independent checks

All Lean/Lake invocations were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`; no budget override, library clean, cache fetch or package mutation was performed.

1. Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-e11 KAM.Planetary.Exponential.Stopped
```

Exit **0**; final output: `Build completed successfully (9310 jobs).` Replayed upstream warnings include N, Kepler, chart, complex-tube and Hamiltonian modules; none originate in Stopped.lean.

2. Scratch probe `.lake/abi-scratch/E11Audit.lean`, importing only the audited module, contained the exact signed telescope under a fresh theorem `e11Signed`, with body `by exact KAM.Planetary.stopped hn B hB`; also `example : type_of% @e11Signed := @KAM.Planetary.stopped` and #print axioms for every public theorem. No signed sorry-bearing file was imported. This is the ordinary-library analogue of the brief's provider/seal probes; no E11 frozen provider exists.

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/E11Audit.lean
```

Exit **0**, no warnings/errors. Separate Python extraction of text between `theorem stopped ` and `:=` reported `SIGNED TELESCOPE BYTE IDENTICAL: True` and `DESIGN TELESCOPE BYTE IDENTICAL: True`. Exact axiom output:

```text
'KAM.Planetary.fastBox_eq_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_fastBox' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.convex_fastBox' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_slowBall' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_workingCylinder' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.planetaryTimeExponent_eq_partial' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.planetaryDriftExponent_eq_partial' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.planetaryDriftExponent_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stopped_fast_erosion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stopped_slow_erosion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stopped_hamiltonian_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stopped_isSolutionOn_forward' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stopped_isSolutionOn_reverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stopped' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Exponential.Stopped
```

Exit **0**; output: `replaying KAM.Planetary.Exponential.Stopped`. E11 is a single lemma module, with no package provider module to add.

4. Lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the permitted stale generated-root exception. Full output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1337 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Frozen-anchor guard and all 144 frozen ABI hashes pass; no other lint failure.

5. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0. `git diff --check inp...HEAD`: empty, exit 0. Static scans found no forbidden proof escape, native_decide, resource option or EuclideanSpace. Module conventions pass; 377 total lines, maximum 98 Unicode columns. Project/Mathlib declaration-name scan found no collision for the 13 specific helper names and no full-name collision for `KAM.Planetary.stopped`.

## Notes, defects and limitations

- Expected generated-root lint exception: leave KAM.lean untouched; regeneration belongs to integration.
- Handoff line 20 says: “Short names grep-checked: none used elsewhere in KAM.” Literally false for `stopped`: `KAM/Nekhoroshev/Averaging/Stopped.lean:283` declares `KAM.Nekhoroshev.stopped`. Different namespaces make this nonblocking; no unqualified-use ambiguity was found in E11. The handoff should qualify its claim.
- The slow helper's sqrt premise is a sufficient geometric condition, not an added premise of the signed result; line 330 derives it from nu^b<epsD. The inverse-exponent notation is mathematically identical to 1/b. These are internal presentations, not statement deviations.
- No new suspected pinned-source defect or blueprint contradiction found. The earlier curried-Hessian maximum defect is already repaired by the sum bound used here. This was a Lean package/design audit, not a fresh re-audit of Nek77 or the sealed N proof.
- Only this report was added to tracked workspace content; scratch probes and temporary audit logs were removed after recording their output. No source, frozen file, manifest, generated root, README or git state was changed by the auditor.
