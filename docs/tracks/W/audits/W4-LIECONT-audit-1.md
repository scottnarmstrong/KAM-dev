# W4-LIECONT independent package audit 1

Overall verdict: **PASS WITH NOTES** for the scoped missing continuity / degree-at-most-two clause of `bpW:w4:lie` (i). No mathematical blocker or rule 6 violation found. This is an infrastructure audit, not a frozen-anchor seal or closure of the whole W4 node.

## Audited revision and scope

- Worktree: `/root/code/KAM-inp-wpq` (physical workspace alias `/mnt/HC_Volume_106379410/kam-w/KAM-inp-wpq`).
- HEAD: `ee1991b47acf3196646e74dd5a3ee8f9ba521078`.
- `inp` at inspection: `5090562d4826c933407f5140aa2ea3e2fb32f5bc`.
- Comparison: `git diff inp...HEAD`; new module `KAM/Wave/Homological/CompleteLieCont.lean`, 260 lines, SHA256 `2320177d1c5b8c514922043639aa36eaa006c3aa25f1a757df75b0b5a1247b10`.
- The complete branch diff also contains the 138-line producer handoff and one generated import in `KAM/Root/Wave.lean`. No other implementation changes.
- Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the named package brief and producer handoff. The generic brief's `docs/tracks/W/statement.md` does not exist; the actual track statement is `docs/tracks/W/W-STATEMENTS.md`, which was inspected.
- Compared the literal blueprint statement at `blueprint-W/parts/w4-homological.tex:502–515` and continuity proof at lines 533–537, the Taylor definition at lines 142–165, frequency hypotheses at lines 167–176, and the W5 generalization at `blueprint-W/parts/w5-kamstep.tex:137–168`.
- No frozen provider/anchor pair is assigned to this package; the brief's provider/type and seal-body probes are therefore inapplicable.

## Declaration verdicts

Names below are in `KAM.Wave`; `CQ` abbreviates the namespace `IsHomContQuadPoly`, not a different Lean declaration. Line numbers refer to the new module.

| Node / role | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| Polynomial definition | `IsHomContQuadPoly` (44) | PASS | Constant plus continuous complex-linear and continuous complex-bilinear diagonal terms; exact intended ordinary total degree ≤ 2. |
| Joint continuity | `CQ.contQuad_continuous` (51) | PASS | Evaluates bounded bilinear map on the diagonal. |
| Fixed-first-slot continuity | `CQ.contQuad_continuous_slice` (57) | PASS | Restricts along the continuous map `x ↦ (y,x)`. |
| Extensional closure | `CQ.contQuad_congr` (62) | PASS | Pointwise equality changes no function. |
| Degree zero | `CQ.contQuad_const` (65) | PASS | Explicit witnesses `c,0,0`. |
| Degree one | `CQ.contQuad_clm` (67) | PASS | Explicit composed continuous linear map. |
| Degree two | `CQ.contQuad_bilin` (71) | PASS | `bilinearComp` supplies the required continuous bilinear witness. |
| Addition | `CQ.contQuad_add` (77) | PASS | Adds witnesses componentwise. |
| Scalar multiplication | `CQ.contQuad_const_mul` (83) | PASS | Scales witnesses componentwise. |
| Negation | `CQ.contQuad_neg` (88) | PASS | Multiplication by −1. |
| Subtraction | `CQ.contQuad_sub` (91) | PASS | Addition and negation. |
| Finite sums | `CQ.contQuad_sum` (95) | PASS | Finite induction using addition; no infinite-degree assertion. |
| Polynomial domain | `HomPolyDom` (109) | PASS | Product of action variables and two independent normal representatives. |
| Action projection | `homPolyPrY` (112) | PASS | Canonical continuous linear projection. |
| Normal projection | `homPolyPrZ` (115) | PASS | Canonical composed continuous linear projection. |
| Conjugate-normal projection | `homPolyPrZb` (119) | PASS | Canonical composed continuous linear projection; this is an independent complex slot. |
| Projection identity | `homPolyPrY_apply` (122) | PASS | Definitional equality. |
| Projection identity | `homPolyPrZ_apply` (123) | PASS | Definitional equality. |
| Projection identity | `homPolyPrZb_apply` (124) | PASS | Definitional equality. |
| Linear pairing piece | `homPairRep_contQuad_gen` (132) | PASS | `homPairL2` applied to the bounded weighted diagonal. |
| Quadratic pairing piece | `homPairRep_op_contQuad_gen` (136) | PASS | Composes the bounded operator, weighted diagonal and bilinear pairing. |
| Angle-derivative piece | `homRtheta_contQuad_gen` (142) | PASS | Constant, linear action terms, two linear normal pairings and three quadratic pairings. |
| Conditional infrastructure | `homLieN_contQuad_of_bound_gen` (163) | PASS | Explicitly distinct conditional name; frequency bound and carrier are discharged in the source export. |
| `bpW:w4:lie` (i), general smoothing | `homLemma_lie_i_contPoly_gen` (203) | PASS | Source frequencies and parameter membership produce the carrier and linear-growth bound; explicit `1 ≤ p+pb` pairing condition. |
| `bpW:w4:lie` (i), original W4 | `homLemma_lie_i_contPoly` (233) | PASS | Specializes `pb=p+1`; nonnegative `p` automatically supplies the pairing condition. |

## Definition classification and statement fidelity

All five new definitions/abbreviations are faithful on their entire stated carriers. `IsHomContQuadPoly` is a semantic polynomial predicate with witnesses `c : ℂ`, `L : E →L[ℂ] ℂ`, and `B : E →L[ℂ] E →L[ℂ] ℂ`, satisfying equality for **every** input. These are fixed witnesses for the whole function, not witnesses chosen separately at each input. Hence the predicate cannot hide arbitrary functions. Complex bilinearity, rather than a Hermitian pairing, gives the intended polynomial in the independent complex variables `(y,z,zbar)`. Symmetry need not be required of `B`: its diagonal is quadratic, and replacing it by its symmetric part preserves that diagonal. The zero polynomial and lower degrees are correctly included. No completeness assumption is needed for this finite polynomial definition.

`HomPolyDom` is exactly `(Fin 2 → ℂ) × (HomL2 × HomL2)` with the usual product norm and topology. The three projection definitions have the literal slot behavior stated by their `rfl` lemmas. There are no choose-or-default objects, totalized sums or fallback branches in the new definitions.

The normal variables use the existing weighted-coordinate model, not unweighted physical coordinates. `HomL2` is complex ℓ², with true normal coordinates `z_j = zhat_j / homWt a p j`, and `homWt a p j = ellWeight a p (j+2) > 0` (`Index.lean:39–63`, `CompleteLie.lean:47`). Weight multiplication and division are linear inverses and identify the weighted norm with the ℓ² norm. The representative product thus has precisely the topology and polynomial structure of `ℂ² × (ℓ^N_{a,p})²`. In pairings, the diagonal factor is `1/(homWt a p j * homWt a pb j)` (`NormalOps.lean:48,106`). The new proofs preserve it. No change of carrier or normalizer is hidden by the parameter-free abbreviation `HomPolyDom`.

For each fixed `θ`, the proof supplies a continuous polynomial in **all** three slots; this is stronger than the requested continuity only in `(z,zbar)`. Both actual source objects occur in the conclusion: `homLieN_gen` and the independently defined `homWeakBracketN_gen`. The weak bracket is not replaced by an ordinary derivative of the generally divergent normal form. Its polynomial and continuity assertions follow from the existing pointwise identity `homWeakBracketN_eq_neg_lieN_gen` (`CompleteEquation.lean:59–81`). No guard `(G)` is assumed or needed.

Premises of the original W4 export are typing data, `HomFreqHyp`, `ξ ∈ Par`, `0 ≤ a`, `0 ≤ p`, and `F : HomTaylor a p s`. `HomTaylor` stores the source analytic, periodic, bounded components and operator data. There is no Melnikov or field-bound assumption. `HomFreqHyp` uses the weaker square-root tail of W5; the original W4 `HomFreqHyp1` implies it through the existing `HomFreqHyp1.toHyp`. This is a valid strengthening. Dropping `θ ∈ T_s` and strip positivity gives an algebraic extension: at every fixed `θ`, even where the existing total `fderiv` does not represent an analytic source derivative, its coefficient values still form a finite continuous quadratic polynomial. On the source strip the statement has exactly the intended meaning; no joint continuity in `θ` is claimed by this extension.

The general export additionally requires `p ≤ pb` and `1 ≤ p+pb`. These are explicit pairing-domain conditions, not hypotheses asserting the target continuity or polynomial conclusion. The W5 proof itself uses `(p-1)+p_+ ≥ 0` and fixes the wave consumer at `p=1` (`w5-kamstep.tex:150–152`); its range `p_+ ∈ [p+1/2,p+1]` then satisfies these conditions. This audit does not certify a general-smoothing theorem for arbitrary nonnegative `p` outside that condition. For original W4, `pb=p+1` discharges both conditions from `p ≥ 0`; there is no extra source premise in the W4 export.

## Proof and rule 6 review

The conditional helper is correctly quarantined by its distinct name and documentation. Its `hΩ : ∀ j, |W j| ≤ K0*(j+2)` is an explicit sufficient bound for a general sequence `W`, and `hC` is summability carrier evidence for the existing source object, not the target regularity packaged as an assumption.

The headline proves `0 ≤ 1+M0` from `h.consts_nonneg`, derives `hΩ` as `homOmega_le h hξ` (`Lie.lean:42–60`), and derives `hC` as `homOmegaCarrier_of_bound` (`LemmaOneAll.lean:176–182`). Thus neither of the helper's substantive inputs is left unpaid at the source export. The carrier is a proposition; proof irrelevance covers alternative evidence for that same carrier.

The analytic step is paid by `homDiagW_gen` and `homPairOmega_eq_clm_gen` (`LemmaOneAll.lean:145–159`): the Ω pairing becomes `homPairL2 (D x) u` for a bounded diagonal `D`. In the helper, `x = c+A v` and `u` is linear in `v`; expanding gives a linear term and a bilinear term with actual continuous-map witnesses. The angle contribution is a finite sum of already constructed polynomial pieces. Combining these with the exact `(2π)⁻¹`, `−i`, `+i` coefficients reproduces `homLieN_gen_eq`; negation gives the weak bracket. The proof never assumes continuity or polynomiality of either source object.

An import-closure scan found 82 KAM modules, zero providers, and seven frozen definition modules: `ComplexStrip`, `OmegaZero`, `Coeff`, `EllWeight`, `Lam`, `SineMode`, `WaveSpace`. All seven are `SEALED` in the manifest. No `DRAFT_SORRY` frozen theorem is imported. Independent axiom output below also excludes `sorryAx`.

## Checks

All Lean/Lake invocations in this audit, including the lint wrapper's internal ABI probe, were inside:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 <command>
```

They ran serially. No resource overrides, clean, cache fetch or dependency update was used.

1. Targeted build (exact invocation):

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-wpq KAM.Wave.Homological.CompleteLieCont
```

Exit **0**. Final output: `Build completed successfully (3307 jobs).` This was an incremental targeted build using the existing snapshot, not a scratch library rebuild. Replayed warnings came from landed `PPlusOne.lean`; no new-module warning was reported. Full output: `/tmp/W4-LIECONT-audit-build.log`.

2. Axiom probe: generated `.lake/abi-scratch/W4LieContAudit.lean`, importing only `KAM.Wave.Homological.CompleteLieCont` and issuing `#print axioms` for all 20 new public theorems. Exact invocation:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean .lake/abi-scratch/W4LieContAudit.lean
```

Exit **0**. Every one of the 20 declarations in the table (theorem rows) reported exactly `[propext, Classical.choice, Quot.sound]`. In particular:

```text
'KAM.Wave.homLieN_contQuad_of_bound_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLemma_lie_i_contPoly_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.homLemma_lie_i_contPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full 20-line output: `/tmp/W4-LIECONT-audit-axioms.log`. Scratch probe removed after checking.

3. Lint (only through the required wrapper):

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpq
```

Exit **0**. Exact output:

```text
check_lean_modules: PASS (3855 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

Full output: `/tmp/W4-LIECONT-audit-lint.log`.

4. Kernel replay and name checks: the user explicitly states these were already run by the launcher and permits omitting redundant replay. Their original output and exit codes are unavailable in this audit's context. No launcher exit code is fabricated here. Replay and name checks were not rerun; they are launcher-supplied checks, not independently observed passes in this report. The independent build, full theorem axiom check and literal proof/statement review above are current observations.

5. `git diff --check inp...HEAD`: exit **0**, no output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, **0 bytes**. New module: **260 lines**, maximum line length **99** characters; copyright, `module`, public interface import, module docstring, exposed public noncomputable section present. No forbidden proof escape or resource override was found. No production source was changed by the auditor.

## Notes, uncertainties, errata and deviations

- **N1 (nonblocking, generated root):** the branch changes `KAM/Root/Wave.lean` by one import of the new module. The producer explicitly reports generation via `scripts/gen_root_imports.py`. This is consistent with root-generation policy, but the generic brief's protected-path command does not include root parts. The literal root-part delta has been inspected and recorded rather than silently treated as an empty protected diff. The auditor did not regenerate or edit roots.
- **N2 (scope):** this closes the requested continuity/polynomial clause only. Existing convergence, Ω-carrier estimates, coefficient identities, guarded derivatives, the rest of W4 and the final PDE theorem are not independently re-audited or newly closed here. General-`pb` coverage is exactly the explicit pairing domain discussed above.
- No suspected pinned-source or blueprint defect was found in the audited clause. No statement repair or implementation deviation was introduced. Stronger joint slot continuity, weaker frequency hypotheses, and the algebraic extension to every `θ` are accurately disclosed above.
- The only retained repository edit by the auditor is this report. Temporary probe files are deleted. No state-changing git command was used.
