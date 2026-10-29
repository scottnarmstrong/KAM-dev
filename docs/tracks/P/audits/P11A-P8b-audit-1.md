# P11A-P8b independent audit 1

Verdict: **FAIL for literal completion of `stepP:p11:pr-in`**. The 18 public theorems are
sound as stated, build at default heartbeats, pass kernel replay, and have only the three
permitted axioms. Clause (i) still lacks its epsilon-independent `c MF` normalization and
its logarithmic conclusion for the actual `G0-hat`. There is also an unresolved
constant-scope discrepancy between the graph's arbitrary-order wording and the exports'
explicit order-dependent factors. These are statement/coverage findings, not a kernel failure.

No frozen anchor is implemented by these two modules; there is no seal-ready anchor verdict.
No finding is made against the expressly deferred pr-b/pr-c/pr-d work or the separate
PreparedData audit.

## Scope and authority

- Worktree: `/root/code/KAM-inp-p11ap8b`.
- HEAD: `7023f94481d23cd6e94a56fe65e7881f27ceb698`.
- Observed `inp`: `537fc2a837002555fbe2766678b1c8454274228f`.
- Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the common package audit brief at
  `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the local P8b handoff including
  its overnight ruling and AUDIT FOCUS, track P statement, relevant P11A design/signature
  sections, blueprint preparation statements, graph pr-in record, and supporting specifications.
- The user's exact report destination overrides the common brief's MAIN-worktree destination.
- Audited production files only: `KAM/Planetary/Preparation/PreparedCauchy.lean` and
  `KAM/Planetary/Preparation/PreparedJets.lean`. Supporting imports were read to interpret
  premises and objects; their inherited proofs are not re-certified by this audit.
- `git diff inp...HEAD` was inventoried across all 15 changed files, including inherited
  P7d files and PreparedData. Git warned of multiple merge bases and selected
  `a2464f937a8b578ae414ec08331359284ec94a78`; the other merge base is
  `11a05936187b0e9191a65fbbab67b3ba7ea89048`. The requested three-dot comparison was retained.
- Design node mapping is `pr_in` local in `prepared`, Preparation/Prepared
  (design line 179); the handoff assigns only this node to the two split modules.
  The graph record starts at `docs/graph/P/DEPGRAPH.md:20615`; its conclusion is at 20624.
- These exports are unsigned helpers. None of their names occurs in Appendix A or
  `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`. There is no signed declaration in
  the audited files to compare, and no provider/frozen type or seal-body probe applies.

## Findings

### F1 — clause (i) is an intermediate bound, not the literal delivered conclusion

Blueprint `blueprint-P/parts/p11-cp09-preparation.tex:208` says:

> `|d_J^beta G0-hat| <= c MF beta! (4/s1)^|beta| <= c ell^((tau0+1)|beta|)`.

The design repeats the first inequality at line 392. The graph repeats it at 20624.
`PreparedJets.lean:554-563` instead exports

```
||partialVec beta (J => polarAverage Fast.G (J,rho)) J||
  <= beta! * (MF + eta1(eps)) / (s1/4)^|beta|.
```

The differentiated object is correct: `P11SlowSpecOf`'s second conjunct identifies h0
with `C.h + eps * p11PolarAverage Fast.G` on V. The radius s1/4, factorial, and J domain
are correct, and the rho domain is larger than the source's stated disc. However,
`MF + eta1(eps)` is not an epsilon-independent constant times MF as exported.
`p11_prin_eta1_le` at line 244 only gives `eta1 <= k eps ell^(2 tau+1)`.
This is not yet the uniform prefactor required by (i). The only exported logarithmic
constant-term bound, `p11_prin_C_jet_log` at line 474, differentiates `C.C`, not
`p11PolarAverage Fast.G`. The latter also contains the linear Omega/rho and Z terms;
replacing it by C.C would change the object and does not discharge (i).

Exact unpaid bridge: establish an epsilon-independent bound
`MF + eta1(eps) <= K * MF` on a proved numeric epsilon range, then export the resulting
G0-hat bound and its logarithmic form using `p11_prin_s1_inv`. For each fixed finite
order cutoff, absorb its factorial/order factors into a constant fixed before eps.
The existing eta1 estimate and e4 suggest a routine proof after shrinking the threshold;
this audit does not claim that the desired inequality is false. The required exported
conclusion is absent. This is within pr-in(i), not an objection to deferring pr-b/pr-c/pr-d.
Do not repair it by assuming a derivative estimate or replacing G0-hat with C.C.

### F2 — literal arbitrary-order constant scope is not resolved

The graph at 20623 says "arbitrary J-multi-indices alpha,beta and rho-multi-index gamma";
20624 writes the final estimates with a single suppressed c, and 20625 says
`CONSTANT_SCOPE: none`. Design line 392 has the same suppressed-constant form.
The actual exports retain:

- `p11_prin_g2_jet_log`, lines 101-113:
  `c * (4/c0)^|alpha| * 4^|gamma|`, besides alpha!, gamma! and the correct eps/log powers;
- `p11_prin_Z_jet`, lines 275-288:
  `alpha! * c * (1+k) * (4*k)^|alpha|`, whereas the graph's final (ii) omits alpha!;
- `p11_prin_C_jet_log`, lines 474-486: `(4/c0)^|beta|`, for C.C only.

All existential c0/k are chosen before eps, A and the derivative indices; their declared
scope is honest. Their explicit powers nevertheless cannot be suppressed into one
constant independent of all arbitrary orders. For a fixed finite cutoff they can be
absorbed into a constant depending on that cutoff, as the later prepared consumers need.
The blueprint's own sharp Cauchy expression in (ii) still displays alpha!, making the
subsequent all-order suppressed-c reading particularly problematic.

Under the audit's literal-conclusion requirement this is an unresolved contract match,
not permission to silently reinterpret c. Either the owner/orchestrator should explicitly
record order-dependent constants, or a fixed-order specialization with the required
uniform constants should be exported. The sharp estimates remain accepted. No claim of
an all-order uniform estimate, or of completed consumer application, is certified here.

## Declaration-by-declaration results

All names below are in `KAM.Planetary`; line numbers refer to the named audited file.
PASS means the stated helper is correct; it does not erase F1/F2 at the graph-node level.

| Node / role | Declaration and line | Verdict | Reason |
|---|---|---|---|
| pr-in, whole slice | combined exports | FAIL | F1; F2 requires constant-scope clarification. |
| polydisc, one coordinate | PreparedCauchy:31 `p11PolyStep_iterate_bound` | PASS | One-variable circle Cauchy; positive coordinate radius, closed-disc inclusion and bound. |
| polydisc, distinct coordinate runs | PreparedCauchy:72 `p11PolyRuns_bound` | PASS | Reverse-list induction; Nodup prevents reusing a frozen coordinate; factorials/radii multiply. |
| polydisc multi-index estimate | PreparedCauchy:120 `p11PartialVec_norm_le_poly` | PASS | Converts fixed-order partials to runs and products over Fin n. |
| domain helper, private | PreparedJets:33 `p11Box_isOpen_aux` | PASS | Finite intersection of strict coordinate inequalities. |
| product helper, private | PreparedJets:39 `prin_prod_append` | PASS | Fin product splits over append. |
| radii helper, private | PreparedJets:43 `prin_poly_prod` | PASS | Product of coordinate radii becomes r1^sum(alpha) r2^sum(gamma). |
| pr-in(iii), sharp | PreparedJets:51 `p11_prin_g2_jet` | PASS | Correct object, alpha! gamma!, s2/4 and eps/4 radii, original sup bound. |
| pr-in(iii), log | PreparedJets:101 `p11_prin_g2_jet_log` | PASS WITH NOTES | Correct eps^3/eps^sum(gamma) and log exponent; F2 explicit order factors. |
| K1 growth | PreparedJets:158 `p11_prin_K1_le` | PASS | MF >= 1 reduces log(1/(eps MF)) to log(1/eps). |
| inverse s1 | PreparedJets:170 `p11_prin_s1_inv` | PASS | Constant independent of eps and derivative orders; correct tau+1 power. |
| inverse alpha1 | PreparedJets:190 `p11_prin_alpha1_inv` | PASS | Correct tau power and fixed constants. |
| inverse d1 | PreparedJets:214 `p11_prin_d1_inv` | PASS | Reciprocal minimum bounded by sum; log >= 1 handles the fixed term. |
| eta1 growth | PreparedJets:244 `p11_prin_eta1_le` | PASS | eps ell^(2 tau+1); not the missing uniform G0-hat normalization. |
| pr-in(ii), log | PreparedJets:275 `p11_prin_Z_jet` | PASS WITH NOTES | Uses the genuine upstream Z-derivative clause; exponent correct; F2. |
| coth helper, private | PreparedJets:322 `prin_coth_ge_one` | PASS | Positive sinh and cosh > sinh. |
| constant coefficient bound | PreparedJets:328 `p11_prin_C_bound` | PASS | Fast mean at z=0 identifies C.C; normalized torus average preserves bound. |
| slice helper, private | PreparedJets:358 `prin_slice_differentiable` | PASS | Affine append map; no analytic conclusion assumed. |
| constant coefficient holomorphy | PreparedJets:367 `p11_prin_C_diff` | PASS | Solves actual h0 identity on rho=2 pi eps slice; Z-domain controlled numerically. |
| constant coefficient Cauchy | PreparedJets:444 `p11_prin_C_jet` | PASS | Actual C.C, radius s2/4; auxiliary result, not G0-hat. |
| constant coefficient log Cauchy | PreparedJets:474 `p11_prin_C_jet_log` | PASS | Actual C.C; does not complete pr-in(i). |
| F bound | PreparedJets:521 `p11_prin_F_bound` | PASS | coth(pi sigma)^n >= 1, no normalization lost. |
| fast-mean bound | PreparedJets:532 `p11_prin_fastMean_bound` | PASS | Real angle slice inside working domain; both phase blocks controlled by product norm. |
| pr-in(i), G0-hat sharp input | PreparedJets:554 `p11_prin_G0_jet` | PASS WITH NOTES | Correct object/radius but retains MF+eta1; no final log export, F1. |

## Definitions, hypotheses and proof inspection

Neither audited file introduces any def, abbrev, structure, instance, notation, selector,
or fallback. Definition classification is therefore empty. Local `set` abbreviations in
proofs are arithmetic abbreviations, not new public mathematical objects.

Existing `p11PartialVec` is the ordered fold of coordinate fderiv applications on the Pi
carrier. The Cauchy proof justifies their use by holomorphy on an open neighborhood; it
does not exploit the total fderiv's values off its differentiability set. Existing
`p11PolarAverage` is the actual normalized torus integral after the complex square-root
polar substitution; imported holomorphy and norm bounds handle its entire asserted disc.
The singleton Fin 1 scalar packaging has exactly the scalar norm. No Euclidean/Pi norm
identification occurs.

For mixed g2 jets, coordinate distances are bounded by s2/4 + s2/4 < s2/2 in J
(the center inequality is strict), and 5 eps/4 + eps/4 = 3 eps/2 < pi eps/2 in rho.
This verifies the actual disc containment, not just the source's domain-table assertion.
For G0-hat the closed s1/4 disc about a point strictly inside the s1/4 ball lies in
s1/2. The general polydisc proof preserves previously differentiated coordinates at
the center, applies one-variable Cauchy on the next circle, and uses differentiability
of all previous runs. There is no missing mixed-derivative commutation assumption.

`P11SlowSpecOf`, `P11FastSpec`, and `P11SecularSpec` are existing upstream stage/source
interfaces, expressly allowed for these distinctly named parametric helpers by the
handoff. Z's original sharp derivative bound is upstream `as-osc` data, not newly assumed
under a renamed conclusion. No helper claims to construct a slow or fast stage from
these premises. Closing prepared itself remains outside this audit.

Additional premises are numeric positivity/nonnegativity, nu >= 1, eps MF <= exp(-1),
the stated point/radius domains, and 2 pi eps < pi rz^2/16 where needed. `0 <= c`
permits multiplying the genuine upstream bound; the selected source c2 >= 1 supplies it.
The rho-disc premise is a domain condition, not literally a smallness condition on eps
alone. No new derivative/frequency/jet conclusion is assumed.

## Hygiene and exact independent checks

Every Lean/Lake invocation below was sequential, with LEAN_NUM_THREADS=1 and nice -n 5.
No resource override, clean/update/cache fetch, library rebuild, or source repair was used.
The compile-gate build was targeted; replayed dependency warnings were nonfatal.

1. Targeted build:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap8b KAM.Planetary.Preparation.PreparedCauchy KAM.Planetary.Preparation.PreparedJets
```

Exit 0. Output began with slot 1 acquired and ended:

```
Build completed successfully (9420 jobs).
```

PreparedJets replay warnings: unused hεM (159), unused simp arguments (349,351),
unnecessary simpa (363), ineffective push_cast (435), unused hs1 (534).
These do not invalidate elaboration or the source lint result.

2. One kernel replay invocation:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.PreparedCauchy KAM.Planetary.Preparation.PreparedJets
```

Exit 0; complete output:

```
replaying KAM.Planetary.Preparation.PreparedJets
replaying KAM.Planetary.Preparation.PreparedCauchy
```

3. A scratch probe imported the two audited modules and ran `#print axioms` for all
18 new public theorems:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AP8bAxioms.lean
```

Exit 0; complete output:

```
'KAM.Planetary.p11PolyStep_iterate_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolyRuns_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PartialVec_norm_le_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_g2_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_g2_jet_log' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_K1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_s1_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_alpha1_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_d1_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_eta1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_Z_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_C_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_C_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_C_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_C_jet_log' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_F_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_fastMean_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_prin_G0_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
```

4. Source lint, run after the axiom probe completed:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1; complete output:

```
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1193 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

This is exactly the generated-root exception authorized by the brief. KAM.lean was not
regenerated. There were no other source-lint failures.

5. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0, empty diff
(apart from Git's multiple-merge-base warning). `git diff --check inp...HEAD`: exit 0,
no whitespace diagnostics, same merge-base warning.

6. Static inventory: PreparedCauchy has 137 lines, maximum 98 characters;
PreparedJets has 605 lines, maximum 99 characters. Both have the copyright header,
module command, public imports, module docstring and public noncomputable section.
No prohibited proof escape, EuclideanSpace, resource override, new public short-name
collision, or harmful root shadow was found. All public names are inside KAM.Planetary
and use the p11 prefix. Five private helpers do not export short names.

7. Recursive local import inventory: 64 imported frozen modules, all matched to
manifest entries with state SEALED and kind definition; no imported frozen theorem,
DRAFT_SORRY module, or provider. No provider type/anchor-body probe is applicable.

8. The only repository write is this report. The named scratch probe was removed after
successful elaboration; no tracked production, generated or protected file was modified.

## Suspected defects, deviations and limitations

- F1 is a delivery/completeness gap, not a suspected mathematical falsehood.
- F2 is a suspected blueprint/graph constant-scope defect or ambiguity, with the exact
  locators and quoted wording above. A single c for unbounded derivative orders is not
  justified by the displayed Cauchy estimates. Finite-order consumers can absorb the
  factors, but that scope must be explicit; this audit does not silently repair it.
- No defect in an original pinned publication was established. The comparison here is
  against the supplied local blueprint/design/graph, not a fresh examination of CP09's PDF.
- No change to a frozen statement, signature, graph, source, normalizer or consumer was
  introduced. No audit of PreparedData or deferred prepared assembly is claimed.
- For acceptance, deliver pr-in(i)'s actual G0-hat normalization/log estimate and resolve
  the order scope of the suppressed constants. The validated helper proofs can be retained.
