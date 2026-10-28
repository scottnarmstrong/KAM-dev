# Independent delta audit W-BP0-2
PASS WITH NOTES

Audited `/root/code/KAM-w`, branch `w`, HEAD `dbec57c1e641c3afe991e41960e067e1aaf2a408`, on 2026-10-28, following `.drafts/briefs/W-BP0-delta2.md`. Scope: the complete `19da5b5..HEAD` delta, audit 1's W-A1–W-A5 and W-S1–W-S2, the revised headline, and regression spot checks. The Revision 1 handoff was treated as claims. All five requested corrections pass; both new errata are confirmed. This is a source/design verdict, not a proof of W-NLW2 or a Lean certification. Only this report was edited; no commit was made.

## Per-item verdicts

### W-A1 — PASS: the false mass threshold is removed

`docs/tracks/W/errata-check-W0.md:134–144` now correctly computes the squared norm ratio as a weighted average of `2j/sqrt(j²+m)`. Its supremum is 2 for every fixed positive mass, since `j/sqrt(j²+m) → 1`. Thus the operator norm is exactly `sqrt(2)`, and the printed norm-one estimate fails for every such mass. In particular `(m,j)=(3,2)` gives `4/sqrt(7)>1`. The same correction appears in `blueprint-W/parts/w0-normalization.tex:159–161` and `.drafts/handoff-W-BP0-r1.md:130–131` (also its N-1 summary). The P96-W p. 280 image does print the norm-one claim. The corrected majorant proof at `w0-normalization.tex:132–148` remains valid; no constant was lost from the cubic estimate.

### W-A2 — PASS: family injectivity is correctly stated and source-supported

`blueprint-W/parts/w-headline.tex:61–63` quantifies over both parameters and both angle representatives. Equality of phase-space points implies equality of parameters and equality of angles modulo `Z²`. This is precisely injectivity of the induced map on `Γ × T²`, hence distinct parameters yield disjoint tori. Item (3), with the analytic embedding definition at lines 22–26, supplies the individual immersion/embedding claim; injectivity alone is not being used to prove immersion.

I inspected the pinned P96-W images, printed pp. 272–273 and 288–289. The source gives one embedding on the entire union of parameter tori, not merely a separately chosen embedding on each torus. On p. 289 Remark 1, that embedding can include the parametrization making each torus flow linear. To see the implication explicitly, write the family map as `K_I(θ)=Ψ(v_I(θ))`, including the injective normal-form and physical-coordinate changes as necessary. Injectivity of `Ψ` forces `v_I(θ)=v_I'(θ')`. Taking the two modal actions gives `I=I'`; positivity of the two actions then gives `θ−θ'∈Z²`. A common action rescaling, angle sign reversal, and period-one conversion preserve this implication. No assumption that a Diophantine frequency distinguishes different parameters is needed. Shell assembly must preserve this single-family injectivity, rather than merely construct individually embedded tori.

`w-headline.tex:7–9` now explicitly calls W-NLW2 a declared weakening, not the full specialized Main Theorem. Lines 91–100 explicitly defer Lipschitz regularity on the family itself, alongside Whitney regularity and stability; the omission is no longer described only as omission of an extension off the family. Compared with audit 1 item 9, the declared weakenings are now accounted for: family Lipschitz/Whitney regularity, stability, Cantor versus Borel parameter set, and higher-order power closeness versus little-o closeness; the cubic specialization, selected modes, weights and period convention are also declared. The extension omission remains explicit at lines 82–87. Leading-order-only frequency asymptotics are separately explicit at lines 75–78. There is no remaining undeclared family-disjointness omission.

Two qualifications do not block this source/design correction. First, `w-headline.tex:79–81` says injectivity “is proved in W8,” but `blueprint-W/PLAN.md:43,95–98` correctly makes W8 planned: read this as the assigned future proof obligation, not an existing proof receipt. Second, the source's Lipschitz statement is in Cartesian coordinates on the union of linear tori. It must not be interpreted as a uniform bi-Lipschitz estimate in the unweighted product metric on `Γ × T²` as actions approach zero; the square-root action chart already prevents that for linear tori. The parenthetical at lines 97–98 is in an expressly unasserted conclusion and introduces no false requirement into W-NLW2. The D30 staging here is the brief's orchestrator ruling for owner review, not a new owner approval by this auditor.

### W-A3 — PASS: all requested parameter ranges are present

`blueprint-W/PLAN.md:77` restricts the original multiplier estimate to `r≥0` and gives the all-real-r bound `(1+m)^(max(r,0)/2)`. Indeed the norm is `sup_j (lambda_j/j)^r`, equal to `(1+m)^(r/2)` for nonnegative r and 1 for negative r. Lines 79 and 81 respectively supply `s>1/2` for summability and `a≥0,p≥1/2` for the trilinear theorem. The latter makes the algebra exponent `s=p+1/2≥1`, as used in `w0-normalization.tex:146`. No endpoint summability error was introduced.

### W-A4 — PASS: executable invocation and isolation limitation are documented

`scripts/wave/w0_checks.py:10–15` now supplies the repo-root command required by this delta brief and explains why plain `python3 -I` cannot find the user-installed sympy. The documented explicit user-site fallback accurately describes an environment workaround, not installation into the isolated interpreter. Independent `python3 -I -c 'import importlib.util; print(importlib.util.find_spec("sympy"))'` printed `None`. The actual unedited script was rerun from the repository root; its result is recorded below. The diff changes only this usage docstring, not the checks or their thresholds.

### W-A5 — PASS: expansion is distinguished from a source defect

`blueprint-W/parts/w0-normalization.tex:211–216,426–428` and `blueprint-W/PLAN.md:67–69` now label Lemma 1 as expansion/strengthening. The inspected P96-W p. 278 image explicitly invokes convergence in complex neighbourhoods, termwise first and second time derivatives, and completeness. Calling the blueprint's C¹-curve formulation a stronger reconstruction result is appropriate. Sine completeness remains an identified external fact, and analytic all-time reconstruction remains W2. The local sign defect is recorded separately as N-4.

### W-S1 / N-4 — PASS: CONFIRMED sign typo

`docs/tracks/W/errata-check-W0.md:152–157` accurately transcribes the P96-W p. 278 image: the second line of the `u_tt` display contains `lambda_j² q_j − sqrt(lambda_j)〈f(u),phi_j〉` inside the parentheses. From p. 277 (6) and p. 278 (7), differentiation gives instead `q̈_j=−lambda_j²q_j−sqrt(lambda_j)〈f(u),phi_j〉`. The next source line already has the negative `A phi_j` term. This confirms a local missing minus sign. The blueprint's force and PDE proof at `w0-normalization.tex:194–201` retains the correct sign. No additional repair was introduced by this audit.

### W-S2 / N-5 — PASS: CONFIRMED factor-two typo

`docs/tracks/W/errata-check-W0.md:159–165` agrees with the KP96 author v2.1 p. 13 image, whose first proof display prints `∂G/∂q̄_j = ∫ f(|u|²)u phi_j`. The p. 11 image gives `G=(1/2)∫g(|Sq|²)` and equation (6), `q̇_j=2i∂H/∂q̄_j`. With real sine basis functions, `∂|u|²/∂q̄_j=u phi_j`, so the displayed derivative needs the factor `1/2`. Equivalently, differentiation of p. 13 (7), `G=(1/4)∫|u|⁴`, yields `(1/2)∫|u|²u phi_j`. The p. 11 Lemma 1 computation is consistent with this corrected derivative through the factor 2 in the dynamics. The error is local to the gradient constant; it does not invalidate the qualitative smoothing claim.

### Regression spot check — PASS WITH NOTES

The complete textual diff changes only the five reviewed areas and their planning/ledger descriptions. The convention file and the central quartic/nonresonance/nondegeneracy/Duffing proofs are unchanged. No `KAM/` or `manifest/` path changed in `19da5b5..HEAD`. The PDE proof and cubic majorant were spot-checked directly, including their unchanged signs, summability range, and `sqrt(2)` factors. The rerun below supplements these paper checks; finite scans are not proofs of all indices or all masses.

One handoff discrepancy remains: `.drafts/handoff-W-BP0-r1.md:149` says the rebuilt PDF was not committed, but `git diff --stat 19da5b5 HEAD` includes `blueprint-W/blueprint.pdf` (623300 to 636665 bytes). The current PDF has 13 pages and extracted text includes item (6) and the Declared weakenings remark. This is an artifact/handoff note, not a mathematical regression. I did not alter or rebuild it.

## Checks and limits

- `python3 scripts/wave/w0_checks.py` from the repo root: exit **0**, all nine sections ran, final output **`ALL CHECKS PASS`**. Exact sine-integral mismatches: `[]`; quadrature maximum error: `1.7e-16`; determinant: `−63/(64*pi²*(m+1)*(m+4))`; printed/corrected quartic ratio: `16`. A3 scan minima at masses `0.1,1,10,43`: `1.181e-01,1.044e-01,2.304e-02,1.095e-02`; nontrivial nonresonance scan minimum at mass `0.01`: `4.105e-07`; random cubic ratio maximum: `2.9836`, below `C=8.668505`. The smallest-amplitude Duffing ratios at masses `0.1,1,10` were `0.99976,0.99987,0.99998`.
- `LEAN_NUM_THREADS=1 scripts/lint_sources.sh`: exit **1**. Output included `check_lean_modules: PASS (417 Lean files, 0 comparator configurations)` and `FROZEN-ANCHOR GUARD OK`; the ABI stage then reported `.lake/abi-scratch/tmpyk2qdi_s.lean:1:0: error: unknown module prefix 'KAM'`, with no `KAM.olean` on its search path. This reproduces audit 1's build-artifact limitation; it is not a full lint PASS. No library build was attempted to change this no-Lean audit's scope.
- `git diff --check`: exit **0**, no output. The report was also checked with `git diff --no-index --check /dev/null /root/code/KAM-w/docs/tracks/W/audits/W-BP0-audit-2.md`: exit **0**, no output.
- Initial `git status --short` was empty. Final status showed only `?? docs/tracks/W/audits/W-BP0-audit-2.md`; `git diff --name-only` was empty. The branch and HEAD remained as recorded above. No tracked production file was changed, and no commit was made.

Pinned sources were read locally in `/root/code/KAM/sources/pdf/`: `poschel1996_wave_CMH_71_269.pdf` and `kuksin_poschel1996_NLS_author_v2_1.pdf`. Existing page images in `.drafts/audit-img/` were inspected without creating or changing image files: `w5,w6,w10,w11,w13,w21,w22,kp11,kp13.png` (P96-W pp. 272,273,277,278,280,288,289; KP96 pp. 11,13). Text extraction from the pinned PDFs corroborated the family and KP96 displays.

What this delta audit could not certify: the KP96 journal printing (only the author version was checked), byte-for-byte PDF/TeX correspondence, full source proofs of later KAM/measure/shell machinery, global compatibility of an eventual implementation's shell maps, or any future W1–W8 formalization. W-NLW2 remains proposed; source support for injectivity is not completion of W8. No targeted Lean build or `#print axioms` applies to this no-Lean package; no Lean theorem or axiom claim is made. The full lint result is distinguished from the successful W0 checks above. Apart from the corrected N-1 and confirmed N-4/N-5, no new suspected source erratum or audit-introduced mathematical deviation was found in this delta.
