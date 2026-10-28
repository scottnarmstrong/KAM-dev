# Independent P12-A package audit 1

**Overall verdict: PASS WITH NOTES.** The five public declarations in `KAM/Planetary/PlanarAssembly/Geometry.lean` match their designated signatures and implement the scoped blueprint geometry. No mathematical or signature defect was found. This infrastructure package supplies no provider and seals no frozen anchor; per-anchor seal readiness is **N/A**. In particular this report does not promote P-G, P-PLANAR, P-FIXED or the later assembly packages.

## Scope, authority and immutable inputs

Date: 2026-10-28. Worktree: `/root/code/KAM-inp-p12a`. Audited HEAD: `3e1ba0afa6cce3ffdbbd50bcf58e4830557a799e`. Observed comparison ref `inp`: `1424468242d8358689f707ca21cc21b0f1a8c9dd`; merge base: `1f9fe4d119e56bd960a52ae5ab677f2522f4a352`. `git diff inp...HEAD` contains exactly one new file, Geometry (327 lines). During verification the shared `inp` ref advanced to `0d0459067371b06163dac863ebbc269c47b67987`. A fresh `git diff inp...HEAD` still contains only the same 327-line Geometry addition, with the same merge base. The protected-path comparison `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. The pre-existing untracked `P12-A-handoff.md` was read and left untouched.

Authority: user instructions and exact report destination; AGENTS.md, PLAN.md, DECISIONS.md (including D20); package audit brief `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`; P12-A handoff AUDIT FOCUS; design row P12-A and its node table; design audits 1 and 2; standalone signatures; Track P statement conventions; blueprint Part 12 and graph packet. The user's explicit worktree report destination overrides the brief's generic main-worktree destination. Only this report and temporary `.lake/abi-scratch/` probes are audit-owned writes; no source or git state is changed.

| Input | SHA256 |
|---|---|
| `KAM/Planetary/PlanarAssembly/Geometry.lean` | `42b3b51e71d472da0ab28d616e1c33250d284cd27a13b10e1cb0df0e050ce9aa` |
| `/root/code/KAM-inp/.drafts/design/P1213Signatures.lean` | `1c09a31d1e920153f88136ea4e5fe8998c19e6e63e99ac711b3defd1cc53b447` |
| `docs/tracks/P/design/P1213-LEAN-DESIGN.md` | `da905471b106707950e1de2c433228a74a967117f81e07cd767a1c7ffea05768` |
| `blueprint-P/parts/p12-planar-assembly.tex` | `83eee5fc9d881bf115be39e811ffc58cc206d45355d7956599115c9c7e0965db` |
| `manifest/frozen-anchors.json` | `5d8d31f1cc70c3cc67375ab28562e4fd4280215c7455dd329004c4dcd7a2f6fa` |

Focused tier-2 review using the lean-statement-audit and manuscript-audit protocols: independent reconstruction from the blueprint, complete new-public-declaration inventory, full scoped proof reading, separate adversarial edge-case pass, then mechanical verification. No repair or delegation was performed. The existing P7-6 audit is provenance evidence, supplemented here by reading the consumed circular identity and product facts and fresh axiom checks; the rest of upstream mathematics is not re-audited in full.

## Declaration and node ledger

Namespace abbreviation PA = `KAM.Planetary.PlanarAssembly`. All locators below refer to the pinned HEAD and blueprint hash above.

| Node / role | Declaration / implementation locator | Verdict | Evidence |
|---|---|---|---|
| Kepler action-only object; p7 product-chart(b), p12 fast-diffeo | `PA.kepler_h`, Geometry:37–38 | PASS | Literal restriction of existing `hProd` via frozen `assemble`; complete signature body matches. General n retained. |
| `bpP:p12:sec-set#data` | `PA.action_center`, Geometry:40–41 | PASS | Exact `m i * sqrt(G*m0*a i)` and frozen fast/slow/assemble conventions. |
| `stepP:p12:ft-cpt`, defining Q0 | `PA.compact_cell`, Geometry:44–47 | PASS | Closed fast-angle cell, inclusive action tolerance, and Gamma bound; no extra predicate. |
| `stepP:p12:ft-cpt`, compactness | `PA.compact_cell_isCompact`, Geometry:91–136 | PASS | Exact unrestricted signature; closed subset of explicit product of finite interval boxes. |
| `bpP:p12:f-unif` | Mathlib `IsCompact.uniformContinuousOn_of_continuous`, Geometry:236–240 | PASS | Compactness and continuity on the same cell are supplied as proof terms. |
| `stepP:p12:ft-uc` | inside `PA.forward_tube`, Geometry:220–246 | PASS | Positive fixed-domain margin and uniform continuity; delta chosen before arbitrary w. |
| `stepP:p12:ft-cmp` | inside `PA.forward_tube`, Geometry:247–322 | PASS | Integer floor reduction, preserved slow/action blocks, circular comparison and chart periodicity. |
| `bpP:p12:forward-tube` | `PA.forward_tube`, Geometry:209–219 | PASS | Complete exact telescope and conclusion, positive delta, explicit quarter-action bound, domain, same-angle strict norm estimate and tube membership. |

The inventory contains exactly three public definitions and two public theorems, plus 12 private proof helpers. There are no new abbrevs, structures, instances, provider declarations or other public theorem surfaces. P12-B/Data signatures and scratch Tube prelude definitions are correctly absent.

## Binder and constant audit

The source at Part 12:15 fixes positive G,m0 and masses; Part 12:33 says “Let a_i>0 ... and zeta>0” and chooses delta “depending only on (G,m0,m,a,zeta)”. Each ordinary data binder is TYPING; positivity hypotheses are SOURCE or STANDING. No project-owned assumption bundle or typeclass hides a logical premise. The universal point and two guards below occur *inside the conclusion*, after delta is chosen, and are included explicitly to audit their scope.

| Theorem | Binder | Bin | Source / explanation |
|---|---|---|---|
| compact_cell_isCompact | G : real | TYPING | Literal compact-cell data, Part 12:37 |
| compact_cell_isCompact | m0 : real | TYPING | Same |
| compact_cell_isCompact | m : Fin 2 → real | TYPING | Same |
| compact_cell_isCompact | a : Fin 2 → real | TYPING | Same |
| compact_cell_isCompact | delta : real | TYPING | No positivity assumed; stronger domain than the source's positive instance |
| forward_tube | G : real | TYPING | Part 12:15,33 |
| forward_tube | m0 : real | TYPING | Same |
| forward_tube | m : Fin 2 → real | TYPING | Same |
| forward_tube | a : Fin 2 → real | TYPING | Same |
| forward_tube | hG : 0 < G | STANDING | Part 12:15 |
| forward_tube | hm0 : 0 < m0 | STANDING | Part 12:15 |
| forward_tube | hm : ∀ i, 0 < m i | STANDING | Part 12:15; expands pointwise positive masses only |
| forward_tube | ha : ∀ i, 0 < a i | SOURCE | Part 12:33; expands pointwise positive axes only |
| forward_tube | zeta : real | TYPING | Part 12:33 |
| forward_tube | hzeta : 0 < zeta | SOURCE | Part 12:33 |
| forward_tube, conclusion | w : Phase 4 | TYPING | Part 12:33, arbitrary R8 point |
| forward_tube, conclusion | ∀ i, abs(fast w.2 i − center i) ≤ delta | SOURCE | Part 12:33 action guard; no hidden clauses |
| forward_tube, conclusion | ∀ i, Gamma(planetBlock w i) ≤ delta | SOURCE | Part 12:33 slow-radius guard; no hidden clauses |

Counts, including the three scoped conclusion binders: SOURCE 4, STANDING 3, TYPING 11, RULED 0, EXCESS 0. For the outer theorem telescopes alone: SOURCE 2, STANDING 3, TYPING 10, RULED 0, EXCESS 0. No instance binder, separation hypothesis, chart-regularity premise, compactness premise, continuity modulus, or conclusion-shaped input is added.

Delta depends only on the five stated physical data and zeta, not on w, fast angles or coupling. Its upper bounds imply delta ≤ min(center 0,center 1)/4. The frozen `Phase 4` is the product of Pi max-norm spaces, exactly the blueprint's max norm, and both `2+2` and `2*2` reduce to 4. The circular parameter is fast angle/(2*pi); no physical-time or frequency conversion is asserted here.

## Definition classification

All three are **literal definitions**, not characterization-defined choices.

| Definition | Body and complete carrier audit |
|---|---|
| kepler_h | Existing total hProd applied to assemble(I,0,0,0). Unfolding gives `-sum_i kappa^2*m_i^3/(2*I_i^2)` on the complete carrier. The inherited total division at zero is the approved source convention (Part 12:55), never a new fallback. |
| action_center | Literal mass times real square root of G*m0*a, on the complete real carrier. Physical uses prove positivity before requiring positive centers. No choice or valid-locus-only replacement. |
| compact_cell | Literal conjunction of the three closed coordinate constraints. For negative delta it is empty because Gamma is nonnegative; compactness still holds. No domain restriction is silently inserted. |

For each of the three definitions separately:

```text
BODY_MATCH: OK
PUBLIC_CARRIER: OK
WELL_DEFINEDNESS: N/A_LITERAL
CHARACTERIZATION: N/A_LITERAL
CHOICE_INDEPENDENCE: N/A
DEFINITION_VERDICT: PASS
```

The definitions introduce no arbitrary selected witness, new zero extension, result package or deferred characterization. Exposed bodies are enabled by `@[expose] public noncomputable section`.

## Proof and dependency review; refutation pass

Compactness (Geometry:49–136): coordinate evaluations and Gamma are continuous, so the cell is closed. Membership supplies nonnegative delta; `|x|,|y| ≤ 1+delta` follows from `(x²+y²)/2 ≤ delta`. The explicit box radius `2*pi+1+delta+sum |center_i|+delta` bounds all four blocks. Finite interval boxes are compact; their closed subset is compact. The membership-based argument correctly handles an empty cell when delta is negative, with no positivity premise added to the theorem.

Forward tube (Geometry:140–322): `delta0 = min(center 0,center 1)/4 > 0`; the action guard gives Lambda_i ≥ 3*center_i/4, whereas Gamma_i ≤ center_i/4, hence the actual strict product-chart domain. Analyticity of the real product chart supplies continuity on the same compact cell. The Mathlib uniform-continuity theorem yields delta1 for zeta; choosing `delta = min delta0 (min (delta1/2) (delta1²/4))` gives both strict action and strict slow-coordinate comparison bounds. Nothing is assumed about an unproved P12-B derivative or Birkhoff map.

For arbitrary angles, `k_i = floor(lambda_i/(2*pi))`, `w' = w-fastShift k`. `planetBlock_shift` proves exactly that actions and slow coordinates are unchanged, and floor inequalities place fast angles in `[0,2*pi]`. Both w' and the zero-oscillator circular comparison point w0 are in the same compact cell. The helpers prove distance < delta1 in the actual product/Pi max metric. Product-chart periodicity is applied at proved domain points, once for w' and once for w0. The delivered P7-6 `circularPoint_eq_poincareProd` identifies the exact frozen circular point, with the original fast angle divided by 2*pi. The final existential tube witness is that same angle vector.

Adversarial checks considered: negative/zero delta; unbounded fast angles; strict versus weak domain inequalities; choice of modulus before w; wrong zero-oscillator block order; missing 2*pi; loss of strictness at delta1²/4; replacing frozen fastShift or circularTube; consuming the converse tube theorem instead of the circular identity. Each is refuted by the explicit arguments above. No tentative mathematical finding remains.

Recursive project-import inspection: 66 local project modules, 49 frozen imports, all 49 manifest state SEALED; no provider module and no frozen theorem module. The actual frozen Phase/Fast/Slow/Assemble/FastShift/CircularPoint/CircularTube bodies were read. Thus there is no imported DRAFT_SORRY or provider-quarantine exception. The P7-6 delivery required by the design is present as the actual owner import; no signature stub or scratch prelude is substituted.

## Fresh verification

All Lean/Lake invocations owned by this audit ran sequentially with `LEAN_NUM_THREADS=1` and `nice -n 5` (the build wrapper applies nice). No clean, package/cache operation, full-library rebuild, heartbeat override or source modification was used. Other users' jobs on the shared host were not controlled by this audit.

1. Targeted build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p12a KAM.Planetary.PlanarAssembly.Geometry
```

Exit **0**. The gate waited for a slot, then printed:

```text
[inp-gate] slot 1 acquired 13:39:20 for KAM.Planetary.PlanarAssembly.Geometry
Build completed successfully (9112 jobs).
```

Replayed dependency warnings: unused variables in `Kepler/Energy.lean:106`, `Poincare/Chart.lean:212,247`, `Kepler/Mass.lean:147,157,500,524`. Geometry emitted no warning. The handoff's “only warning ... Mass:524” is not the complete warning list from this independent replay; all observed warnings are inherited dependency warnings.

2. Exact definitions, theorem applications and axiom closure:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P12AAudit1.lean
```

Exit **0**, no errors or warnings. A mechanical extraction compared complete definition commands and complete theorem headers against the standalone signature file; all five match after whitespace normalization. The probe independently transcribed all three definition bodies under fresh names and proved equality of the complete functions by `rfl`. It copied both complete theorem telescopes and applied the real exports with exactly their explicit arguments:

```lean
exact compact_cell_isCompact G m0 m a delta
exact forward_tube G m0 m a hG hm0 hm ha zeta hzeta
```

No signature sorry body or provider was imported. Provider/frozen `type_of%` and seal-body probes are N/A because this package has no provider or frozen theorem implementation.

The probe ran `#print axioms` for all five public declarations and all four consumed project theorem exports. Every output was exactly the named declaration followed by:

```text
depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exports checked: `PA.kepler_h`, `PA.action_center`, `PA.compact_cell`, `PA.compact_cell_isCompact`, `PA.forward_tube`, `KAM.Planetary.circularPoint_eq_poincareProd`, `KAM.Planetary.analyticOnNhd_poincareProd`, `KAM.Planetary.poincareProd_lattice`, `KAM.Planetary.planetBlock_shift`. No sorryAx or project axiom appears.

3. Kernel replay:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarAssembly.Geometry
```

Exit **0**. Complete output:

```text
replaying KAM.Planetary.PlanarAssembly.Geometry
```

4. Repository source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, with the complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (697 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The only failure is the generated root, expressly excepted by the package brief. No forbidden-pattern, long-line, oversize-file or other lint diagnostic appears. The generated root was not edited.

5. Scoped static checks: Geometry has **327 physical lines**, maximum width **97**, zero lines over 100. It contains the copyright header, `module`, public imports, module docstring, public section and exposed definitions. Scans find zero sorry/admit/axiom/unsafe/opaque, EuclideanSpace or resource overrides. The three public definition bodies and two full theorem signatures match the supplied signature artifact; all 12 other declarations are private proof helpers.

## Findings and closeout

- **N1 — permitted generated-root hygiene note.** Lint reports “KAM.lean is out of date; run scripts/gen_root_imports.py”. The brief expressly permits this condition and rule 10 forbids an auditor from editing the generated root. The orchestrator should regenerate it during integration. This is the reason for package PASS WITH NOTES rather than an unqualified repository-hygiene PASS.
- **N2 — handoff warning inventory.** The targeted replay reports additional inherited warnings beyond Mass:524, listed above. This does not affect Geometry's statements, proof closure or kernel replay. No repair of dependency files is part of this audit.
- **No mathematical finding or suspected source erratum.** No source contradiction, unauthorized premise, meaning-changing definition, EuclideanSpace use, resource override, provider import or frozen-file deviation was found in scope. No deviation was introduced. External papers and later P12/P13 packages were not audited.
- **Closeout:** all five new public declarations and all six P12-A node-table rows are classified; complete signatures and literal bodies pass; the scoped proofs were read and adversarially checked; build, exact applications, standard-only axiom closure and kernel replay pass. Repository lint has the expressly permitted generated-root exception. No pending proof check or tentative mathematical finding remains. Frozen-anchor seal verdicts remain N/A.
- Final input-hash checks preserve the Geometry and standalone-signature hashes above. Protected-path diff is empty; both `git diff --check inp...HEAD` and `git diff --check` pass. The report was also checked directly for trailing whitespace and balanced fences because it is untracked. The audit scratch probe was deleted. The only persistent audit-owned artifact is this report; the pre-existing handoff remains untouched.
