# P-SEC independent audit 1

Verdict: **PASS WITH NOTES** for this definition/identification package. Both
`bpP:p11:sec-D#data` and `bpP:p11:sec-E#data` are **definition-confirmed** under
D31, and their new identification theorems are **PROVED**. The package supplies
the missing source objects identified in P-GRAPH-CLOSE-audit-1:55–56. There is
no new frozen theorem or provider export to seal. Provider/frozen type matching
and a frozen seal-body probe are therefore not applicable to this scope.

Audited HEAD: `c0f7485d846f7ca8bde78b8570ac1493f95c935b` (`inp-psec`).
Comparison: `git diff inp...HEAD`, including the complete three new modules and
handoff. The diff has four files, 867 inserted lines; no existing Lean declaration
changes. Only this report is written outside `.lake/abi-scratch/`. The user's
explicit worktree report destination overrides the generic brief's main-worktree
destination. No source, graph, manifest, generated file, or git state was changed.

Reviewed authority: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md (especially D31),
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, P-SEC-handoff.md,
P-GRAPH-CLOSE-audit-1.md, docs/tracks/P/statement.md,
blueprint-P/parts/p11-cp09-preparation.tex:145–153,189–194 and the corresponding
records at docs/graph/P/DEPGRAPH.md:21254,21284. The graph currently retains its
older NOT_STARTED notes; this report supplies audit evidence, not a graph edit.

| Node | Verdict | Definition-node conclusion |
|---|---|---|
| bpP:p11:sec-D#data | PASS WITH NOTES | Definition-confirmed; new source/implementation identifications PROVED under the accepted local guards. |
| bpP:p11:sec-E#data | PASS WITH NOTES | Definition-confirmed; full complex pullback, domain inclusion/table and normalized frequency formulas PROVED under the accepted local guards. |

The notes concern the permitted generated-root lint exception and the scope of
conditional specifications, not a failed proof.

## Fidelity and definition classification

All 14 new definitions are exposed literal expressions on their carriers. There
are no new structures, abbreviations, arbitrary choices, selectors, or fallback
branches. `Complex.sqrt`, the Bochner integral and division retain their ordinary
Lean totalizations outside the source regime; the proofs use the specified
source domains and eps>0. In particular, the raw mean is actually the integral
over the real unit cube (`KAM/Strip/Averages.lean:32`); its volume is one, and
period-one angles account for every 2pi in Pi and Omega-tilde.

The definitions are: sigma3; polar shell; Pi; second angle projection; G-hat;
raw G-hat_0; source h0; source f2; alpha21; alpha22; rho-tilde_0; H2; H-hat;
and the continuous-linear first action projection. Their individual whole-carrier
classification and all 40 public theorem checks appear below. All declaration
names have prefix `KAM.Planetary.`. D/E locators abbreviate
`KAM/Planetary/Preparation/SecDSource.lean` and `SecESource.lean`; F abbreviates
`SecEFreq.lean`.

| Node | Declaration | Locator | Verdict | Classification / reason |
|---|---|---|---|---|
| sec-D | `p11Sigma3` | D:41 | definition-confirmed | Literal sigma_F/12. |
| sec-D | `p11PolarShell` | D:44 | definition-confirmed | Exact open complex shell; coordinate sup norm and complex radial modulus. |
| sec-D | `mem_p11PolarShell` | D:48 | PROVED | Definitional membership, with no added premises. |
| sec-D | `p11PolarShell_eq_prod` | D:52 | PROVED | Definitional product of the strip and radial shell. |
| sec-D | `p11PolarShell_isOpen` | D:56 | PROVED | Finite intersections of open coordinate constraints. |
| sec-D | `p11PolarShell_re_gt` | D:70 | PROVED | Re rho_j > pi eps; positivity follows in the source regime eps>0. |
| sec-D | `p11PolarShell_norm_lt` | D:78 | PROVED | Triangle inequality gives the source 3 pi eps radial bound. |
| sec-D | `p11Pi` | D:89 | definition-confirmed | Literal principal square root, period-one sine/cosine polar map. |
| sec-D | `p11SlowZeta` | D:94 | definition-confirmed | Literal second angle-block projection. |
| sec-D | `p11PolPt_eq_pi` | D:97 | PROVED | Implementation fast block equals the literal Pi. |
| sec-D | `p11PolarC_eq_pi` | D:102 | PROVED | Full complex chart equals (id,Pi), without projection to reals. |
| sec-D | `p11Pi_norm_le` | D:108 | PROVED | Exact source sqrt(3 eps) exp(pi sigma_F/3) bound; hSigma>=0 is standing data. |
| sec-D | `p11GHat` | D:139 | definition-confirmed | Literal G(J,Pi(zeta,rho)). |
| sec-D | `p11GHat0` | D:142 | definition-confirmed | Raw normalized torus integral; no selected continuation replaces the integral. |
| sec-D | `p11GHat0_eq_polarAverage` | D:146 | PROVED | rfl identification with the implementation average. |
| sec-D | `p11SourceH0` | D:150 | definition-confirmed | Literal h-tilde + eps times raw average. |
| sec-D | `p11SourceF2` | D:155 | definition-confirmed | Literal eps(G-hat minus its mean) + f1 composed with (id,Pi). |
| sec-D | `p11SlowH0_eq_source_iff` | D:161 | PROVED | Free-Z equality characterized, rather than presumed; eps nonzero is necessary for cancellation. |
| sec-D | `p11SlowF2_eq_source_iff` | D:172 | PROVED | Same exact characterization for f2; no conclusion-shaped premise. |
| sec-D | `p11GHat0_eq_sec_add_Z` | D:188 | PROVED | Proved local polar-average output identifies the implemented correction. |
| sec-D | `p11SlowH0_eq_source` | D:197 | PROVED | Discharges free-Z obstruction on the averaging box. |
| sec-D | `p11SlowF2_eq_source` | D:207 | PROVED | Discharges free-Z obstruction at every angle, provided the action lies in the box. |
| sec-D | `P11SlowSpecOf.h0_eq_source` | D:216 | PROVED | D31 specification gives source h0 on all V2. |
| sec-D | `P11SlowSpecOf.f2_eq_source` | D:224 | PROVED | Combines slow and fast specifications on all T_sigma3 x V2; genuine smallness only. |
| sec-D | `p11SlowData_h0_f2_eq_source` | D:257 | PROVED | Signed chosen datum: existence guard eliminates the default branch and proves both identities. |
| sec-D | `p11Alpha21` | D:279 | definition-confirmed | Literal gamma0 K2^(-tau0)/4. |
| sec-D | `p11Alpha22` | D:283 | definition-confirmed | Literal eps gamma0 K2^(-tau0)/4. |
| sec-D | `p11_slow_divisor_alpha` | D:288 | PROVED | Algebraic pure-slow/mixed case identification; arbitrary decidable proposition generalizes the case split. |
| sec-D | `p11K2_s2_eq` | D:295 | PROVED | Both source formulas hold by rfl, with unchanged dependence on nu and eps. |
| sec-D | `p11_exp_K2` | D:302 | PROVED | Exact exponential identity, under positive sigma and eps; valid for every real nu (stronger). |
| sec-E | `p11RhoTilde0` | E:41 | definition-confirmed | Literal constant vector 2 pi eps. |
| sec-E | `p11SlowCenter_eq` | E:43 | PROVED | rfl identifies the two action centers. |
| sec-E | `p11Rescale_fst` | E:47 | PROVED | Angles unchanged. |
| sec-E | `p11Rescale_snd` | E:51 | PROVED | Actions are center plus eps times both action blocks. |
| sec-E | `p11Rescale_shift` | E:60 | PROVED | Commutes with all complex angle shifts (stronger than lattice shifts). |
| sec-E | `p11Rescale_hasFDerivAt` | E:66 | PROVED | Full complex derivative is diag(id,eps id). |
| sec-E | `p11Rescale_symplFormC` | E:82 | PROVED | Full complex symplectic pullback equals eps times the form. |
| sec-E | `p11Rescale_sub_center` | E:94 | PROVED | Exact centered-action identity. |
| sec-E | `p11_norm_eps_smul_apply` | E:98 | PROVED | Scalar norm identity for eps>0. |
| sec-E | `p11Rescale_mem_half` | E:103 | PROVED | Full complex action polydisc maps into V2/2 if 2 eps <= s2/2. |
| sec-E | `p11Sigma3_div_six` | E:124 | PROVED | Exact source strip width sigma_F/72. |
| sec-E | `p11Rescale_mapsTo_half` | E:128 | PROVED | Full E maps into T_sigma3/6 x V2/2. |
| sec-E | `p11H2` | E:139 | definition-confirmed | Literal complex composition WorkingH o Fast.map o PolarC o Psi. |
| sec-E | `p11HHat` | E:144 | definition-confirmed | Literal H2 o A_eps divided by eps. |
| sec-E | `p11PreparedCoreOf_NP` | E:149 | PROVED | Both implementation fields are the source N/P formulas, by rfl. |
| sec-E | `P11SlowSpecOf.hHat_eq` | E:158 | PROVED | Full complex H2 and H-hat identities on every z in E; no real-part or restricted real locus. |
| sec-E | `p11Rescale_cauchy_box` | E:183 | PROVED | Both 5 eps/4 bounds and the full complex Cauchy-box inclusion; needs exactly 5 eps<s2. |
| sec-D | `P11SlowSpecOf.Z_eq_source` | F:34 | PROVED | Chosen Z equals G-hat_0 minus secular constant/linear part on V2. |
| sec-E | `p11SlowJL` | F:46 | definition-confirmed | Literal continuous complex-linear first action-block projection. |
| sec-E | `p11SlowJL_apply` | F:49 | PROVED | Definitional projection identification. |
| sec-E | `p11SlowJL_single_castAdd` | F:51 | PROVED | First-block coordinate vector projects to the corresponding coordinate vector. |
| sec-E | `p11SlowJL_single_natAdd` | F:56 | PROVED | Second-block coordinate vector projects to zero. |
| sec-E | `P11SlowSpecOf.preparedFreq_eq` | F:62 | PROVED | Chain rule cancels eps from rescaling against 1/eps; full complex action polydisc. |
| sec-E | `P11SlowSpecOf.freq_source` | F:103 | PROVED | Both source frequency blocks, with Omega/(2 pi) and outer eps in the second block; all complex actions of E. |

## Guards, complex domain and normalization

The unsigned specifications are the already proved output contracts of fast/slow
averaging, accepted as local guards by D31. They are not newly introduced fields
assuming this package's missing identities. The two `_eq_source_iff` theorems
expose the obstruction for arbitrary Z; subsequent theorems discharge it, and
`Z_eq_source` identifies the chosen correction. The signed h0/f2 theorem uses
`exists A, P11SlowSpec ... A` to select the successful branch, never the default.
`SlowSigned.lean:90–99` proves the relevant local existence; no global correctness
of a fallback value is claimed.

`P11SlowSpecOf.hHat_eq` uses precisely the original complex identity on
T_sigma3 x V2, the MapsTo property of Psi from the half domain, and the slow
conjugation identity. `p11Rescale_mapsTo_half` supplies the missing domain step
for every complex z in E when `2 eps <= s2/2`. Both asserted equalities have
codomain Complex. Neither the real `chain` nor `Complex.re` appears in the new
H2/H-hat expressions. `p11WorkingH` is the source Hamiltonian in its holomorphic
secular chart; an additional global physical complexification is not claimed.
The arbitrary real map W affects only the unrelated `checkW` field; N, P and
their complex gradient are definitionally independent of W.

The frequency proof establishes differentiability before using fderiv: h0/g2
on their open boxes, the raw mean locally via the h0 identity and eps nonzero,
and Z on its stated holomorphic domain. The first block is omega + eps*dJ G0
+ dJ g2. The second is eps*(Omega/(2pi) + drho Z + eps^(-1)*drho g2).
Thus neither an eps nor a 2pi is dropped. The statements cover the full complex
action polydisc of E; angles do not enter N.

`eps*MF <= exp(-1)` and `64 eps < rz^2` are genuine small-eps restrictions already
used by the averaging construction, not desired conclusions. The latter uses
an existing safe-domain estimate into B_(rz/2); it is not asserted equivalent
to the blueprint's sharper explicit Pi-shell inclusion in B_(rz/4). Such
restrictions can be obtained by shrinking the source's data-dependent eps2.
`nu >= 1` is not needed for the algebraic identities; allowing arbitrary nu
there is a stronger statement. The domain table's `5 eps < s2` is the printed
source condition. Its theorem actually covers every complex action with
coordinate norms <5/4, which includes the required K_eps+3*vartheta points.

Existing context, not new implementation: E and the mapping iff are already
literal in SecEDefs.lean:25–37,41–112; the prepared box is literal in
SlowData.lean:34. KAM datum constants and earlier analytic continuation/Cauchy
estimates are inherited from the existing preparation/selection modules. This
report audits the requested missing objects in the three new modules; it does
not independently re-audit every inherited preparation theorem. Shell
holomorphy is consistent with the proved positive-real-part bound and the
existing complex polar differentiability theorem
`SlowAverageDom.lean:42`; the new shell norm bound is exactly the printed bound.

## Independent checks

All Lean/Lake commands below were run serially, with `LEAN_NUM_THREADS=1` and
`nice -n 5` (the compile-gate script applies nice itself). No resource override,
cache fetch, clean, package mutation, or root regeneration was used.

1. Targeted build:

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-psec KAM.Planetary.Preparation.SecEFreq
[inp-gate] slot 1 acquired 16:36:57 for KAM.Planetary.Preparation.SecEFreq
Build completed successfully (9423 jobs).
exit 0
```

SecEFreq imports both other new modules; this checks all three. Replayed
warnings concern inherited modules (unused binders/simp arguments and deprecated
names), not the three new files. No default-heartbeat failure occurred.

2. Kernel replay, one invocation:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.SecDSource KAM.Planetary.Preparation.SecESource KAM.Planetary.Preparation.SecEFreq
replaying KAM.Planetary.Preparation.SecEFreq
replaying KAM.Planetary.Preparation.SecESource
replaying KAM.Planetary.Preparation.SecDSource
exit 0
```

3. Scratch elaboration and axioms:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/PsecAudit.lean
```

The probe prints axioms for every new public theorem (40), checks the literal
shell and expanded H-hat composition by rfl, and elaborates a fresh anonymous
copy of the full complex H2/H-hat statement using
`by exact P11SlowSpecOf.hHat_eq hA heps h2 W hz`. No frozen seal is involved.
Probe exit 0; all rfl and fresh-statement checks succeeded. Exact axiom output:

```text
'KAM.Planetary.mem_p11PolarShell' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolarShell_eq_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolarShell_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolarShell_re_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolarShell_norm_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolPt_eq_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolarC_eq_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Pi_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11GHat0_eq_polarAverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowH0_eq_source_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowF2_eq_source_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11GHat0_eq_sec_add_Z' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowH0_eq_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowF2_eq_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11SlowSpecOf.h0_eq_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11SlowSpecOf.f2_eq_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowData_h0_f2_eq_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slow_divisor_alpha' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11K2_s2_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_exp_K2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowCenter_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Rescale_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Rescale_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Rescale_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Rescale_hasFDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Rescale_symplFormC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Rescale_sub_center' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_norm_eps_smul_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Rescale_mem_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Sigma3_div_six' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Rescale_mapsTo_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PreparedCoreOf_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11SlowSpecOf.hHat_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Rescale_cauchy_box' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11SlowSpecOf.Z_eq_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowJL_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowJL_single_castAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowJL_single_natAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11SlowSpecOf.preparedFreq_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11SlowSpecOf.freq_source' depends on axioms: [propext, Classical.choice, Quot.sound]
```

4. Names, source hygiene and protected paths:

```text
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-psec KAM.Planetary.Preparation.SecDSource KAM.Planetary.Preparation.SecESource KAM.Planetary.Preparation.SecEFreq
short-name check OK (no reused public short name)
exit 0

git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(no output; exit 0)
git diff --check inp...HEAD
(no output; exit 0)
```

The name check covers KAM and Mathlib, including dotted declaration suffixes.
Independent source scan found none of sorry/admit/axiom/unsafe/opaque,
native_decide, EuclideanSpace or set_option. Every new file has the copyright,
module, public imports, module docstring and exposed public section.
D: 316 lines, maximum 98 characters; E: 209 lines, maximum 99; F: 248 lines,
maximum 100. The handoff's F line count of 247 is a harmless receipt discrepancy.

Import traversal: 377 KAM modules, zero provider imports, 64 frozen definition
anchors, all state SEALED in the current manifest; no frozen theorem imports
and no DRAFT_SORRY imports. Relevant frozen strip and physical-chart definitions
were read as context. There is no circular dependence on a frozen headline.

5. Lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1342 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1 (only the explicitly permitted generated-root exception)
```

## Uncertainties, errata and deviations

No suspected pinned-source defect or new mathematical deviation found in the
three audited modules. No weakened conclusion, widened constant dependence,
meaning-changing carrier, or unapproved conclusion-shaped premise found.
The explicit smallness conditions and conditional choice guards remain visible;
this verdict does not turn them into unconditional correctness of selected
records for arbitrary parameter values. No graph record or frozen anchor is
sealed by this audit. The generated-root exception is left for the orchestrator,
as explicitly permitted by the brief and required by rule 10.
