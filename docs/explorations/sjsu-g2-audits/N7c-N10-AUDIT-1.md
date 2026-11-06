Audited HEAD (`git rev-parse HEAD`): `288ed55b0e9b5a95429bab48c2479c90c74b930f`; package commit: `0610ff2ad`; reflow-v2 SHA256: `KAM/EffectiveStability/Tube/Engine/Deriv.lean` = `abad30036949416396042272c86e4f61c76fa8efebf8ad090d31e456f9328af8`; `KAM/EffectiveStability/Tube/Engine/DOpd.lean` = `b13dedaca4b7ba8fbcc39f0d13b9f9ac4fd05690ea8d8c4c9995250846494547`; `KAM/EffectiveStability/Tube/Engine/Regroup.lean` = `6a1203a1227419b65a1b7aeea61b9b7a20bcb6c69fe2a35aefb431e8187117c4`; `KAM/EffectiveStability/Tube/Engine/LitCert.lean` = `81b9413c6e35a9683dfe4e8f41504e6729b08b7362c58c4c02ece422115dfd31`; `KAM/EffectiveStability/Tube/Engine/Bracket.lean` = `21e298afbb0f0501f8cad73b25fdc9b218838c388d8b9e5634cff9c96a7b1a01`; `KAM/EffectiveStability/Tube/Engine/Drop.lean` = `c7a19956fc59ea0def4873091b51e985e1ab2fa3f15eff6438e89d96a1b1e124`.

# N7-Engine part 3 and N10-Drop, combined audit 1

**Verdict: PASS WITH NOTES.** No mathematical defect, conclusion-shaped hypothesis, or mismatch
with N9's `hG`/`hDrop` was found. All six targeted builds, all 55 theorem axiom queries, exact
N9 consumer composition and 19 small kernel counterchecks passed. The notes concern
incomplete/stale documentation and compiler hygiene. Repository lint failed during a concurrent
out-of-scope generated-file scan; this is not a green repository landing gate.

## Scope and pinned inputs

Focused refute-first audit (tier 2) under `.drafts/g2/AUDIT-PKG-brief.md`, the N7/N10 briefs,
and N9 targets (B)(ii)/DROP. Read AGENTS, PLAN, DECISIONS, WORKER-RULES, the route/gate text,
`ApproxIntegral`, the two handoffs and the three requested previous audits. The authoritative
source-facing contract for this audit is the exact generic N9 consumer, not a frozen T2-CONF
headline. Earlier audits are context; their passing verdicts do not certify these new files.

Only the six first-line Engine files are audited packages. Inspected dependencies include
`Trig/Poly`, `Trig/Product`, packed injectivity/load/norm interfaces, `Engine/Input`, `Sparse`,
`Step`, `L1`, `BTerm`, and `Check/BracketBound`. Their use is checked at the application sites;
this is not a fresh full audit of those packages. Generated H/Br/Small data and the Python
producer are excluded, including N10's `emit.py` fix. No production value of G, DROP or eta,
production resource claim, completed N7 ledger, or final confinement theorem is certified.
The optional Small/Br application build is not needed for this generic acceptance.

Permission envelope: only this report plus the audit protocol's explicitly required scratch
under `.drafts/g2/scratch/audit/n7c-n10-audit-1/`; serialized `g2lake` commands; no source,
handoff, frozen-file, manifest or generated-root repairs, commits, pushes or branch changes.
Existing unrelated shared-worktree changes are preserved. No subagents were used.

At entry HEAD was `0610ff2adcd78ff1d649b52346d0adda7f5ec343`. The initial six files matched
that package commit. Initial Deriv SHA256 was
`b5ad95afe67a05a75abaaf0ef686c202f7c2d2adf7ac20847b9a7cc99ce9ef64`, Regroup was
`836240594ce37924d6687f11ec91a15d254dc9b9670bb858aa285b788dbdec66`;
the other four hashes equal the first line. A separate worker then reflowed precisely Deriv's
three known lines and Regroup's one known line. The complete diff changes whitespace only;
no declaration, import, hypothesis, definition body token, or proof token changes. The
reflow was committed separately as `288ed55b0`. The
first-line reflow-v2 hashes identify the reviewed final bytes; all line references below use
that snapshot. Deriv/Regroup now have 299/223 lines rather than 297/222.

## Findings and refutation

**N1 — Incomplete N7 DRAFT handoff receipts (documentation).**
`docs/explorations/sjsu-g2-handoffs/N7-Engine.md:45–47`, quote under Checks:
“(to be filled with the build outputs, `#print axioms`, timings)”. This does not meet the
package handoff checklist. The document explicitly says DRAFT, so this is an incomplete
receipt inventory, not an asserted successful production verification. Independent
refutation: inspected the whole handoff for a later receipt section; none supplies the
missing outputs. This auditor's checks below establish only the six generic modules.
Suggested fix: fill in actual commands, outputs, axioms and measured timings at the
appropriate package/production milestones, preserving the DRAFT boundary until then.
Status: confirmed documentation note; no mathematical blocker.

**N2 — The DROP module's sum-order description is stale (documentation).**
`Drop.lean:21`, quote: “`dropSum`: `Σ dropT` over the terms, as nested sums in the order of
`bterms`”. The implementation at 58–62 instead uses axis, F entry, kind, H entry, shift;
`bterms` uses axis, F entry, H entry, kind, shift. Independent refutation: compared both
loop nests and checked the proof of `dropSum_eq` (95–106), which explicitly commutes the
H/kind sums. Thus equality is proved, and the handoff correctly discloses the factoring;
only the module's order claim is wrong. Suggested fix: say “factored nested sums equal to
`Σ dropT` over `bterms`”, matching the accurate definition docstring at 54–55.
Status: confirmed documentation note; no change to the theorem or check is needed.

**N3 — Nonblocking compiler hygiene.** The build logs replay 23 deprecated-name diagnostics:
Deriv's `if_pos`/`if_neg` at 77,79,103,106,109,249,250,252,291,292,294; Regroup's at
200,202 (twice),203 (twice),206 (twice),216 (three times),218; and DOpd's `if_true` at 186.
DOpd:74, quote `cases p <;> simp [psgn] <;> ring`, additionally emits three diagnostics
about redundant `<;>`, a no-op `ring`, and an unexecuted tactic. These are cosmetic warnings,
not failed proof obligations. Refutation: all targeted commands returned 0; their exact
source locations and messages are preserved in the logs. Suggested optional cleanup: use
`ite_eq_left`/`ite_eq_right`/`ite_true` and remove the redundant final tactic. No diagnostics
are attributed to LitCert, Bracket or Drop themselves. No resource option was introduced.

**Known width note — resolved in reflow-v2.** The four launch-listed lines were reflowed by
another worker. Direct final scan finds no overlong line in any of the six files. This auditor
made no repair. There is no suspected mathematical erratum in a pinned source, and no
mathematical deviation introduced by this audit.

## Statement and proof checks

| Surface | Contract and disposition |
|---|---|
| `packSum_dlist` (`Deriv:152–156`) | Exact packed derivative of the same semantic list, with column/stride/length and signed offset bounds. PASS. |
| `LitD.dwf/dmx/dsym/dopd_eval`, `SpD.deriv_eval` | Preserve layout, parity, scale and actual angle derivative. PASS. |
| `fCheck_sound` (`LitCert:52–66`) | Literal slots equal the sparse dense slots; same C, parity and rational scale. PASS. |
| `dCheck_sound` (`LitCert:75–95`) | Literal slots equal the original literal's derivative list; same C/scale and opposite parity. PASS. |
| `sum_filter_mon` (`Regroup:163–219`) | Exact filtered sum equals the cheap candidate sum, including list multiplicities and removal of zero coefficients only. PASS. |
| `brl_sound` (`Bracket:166–289`) | Absolute value of the exact signed sum of products, bounded after cancellation. PASS. |
| `brAll_sound` (`Bracket:328–343`) | Every p of total degree at most L, every angle; RHS G at the same triple. Exactly N9 hG after the proved truncSet bridge. PASS. |
| `dropSum_eq`, `mdeg_mon_eq` (`Drop:95–120`) | Factored arithmetic equals the full term sum; nonzero terms have degree d−1. PASS. |
| `dropCheck_sound` (`Drop:217–239`) | Exactly N9 hDrop with muF/monOf, the same g/k, box, cutoff, coefficient, monomial and absolute-value placement. PASS. |

**Derivative masks and signs.** In `Trig/Poly`, even parity evaluates cos and odd parity
evaluates −sin, and `psgn false=+1`, `psgn true=−1`. Independently,
`d cos(k·phi)/dphi_a = k_a*(-sin(k·phi))`, while
`d(-sin(k·phi))/dphi_a = -k_a*cos(k·phi)`.
For k=(1,−2), cosine has partials −sin and +2sin; negative sine has partials −cos and +2cos.
This agrees with `dlist`, `SpD.deriv`, `LitD.dopd_eval` and `derivZ`, with no 2*pi factor
(radian angles) and no division by an action.

`Deriv:113–136,152–295`: column index is `i % S`, row index is `i / S`, both centred at C.
The column mask has full w-bit digits only at `c+S*r`; the row mask covers exactly the
first `2*C+1` columns. `2*C+1<=S` excludes mask overlap. The offset includes all layout
slots, including padding, and is removed under the same mask. `hb` and `l+1<=w` put
every offset digit `d_i+2^l` in `[0,2^w)`, proving nonnegativity before `.toNat` and
excluding carry contamination in the AND operation. Padding coefficients vanish by colsOk;
the last row ends at `Layout.len`. Short lists are extended only by zeros. C=0, zero
modes, negative modes, lower signed endpoints and the upper allowed endpoint are covered.

The packed derivative identity itself is an integer polynomial equality and need not claim
that its output slots fit a decoder. `LitD.dmx` proves the bound C*2^(b−1);
`dCheck` separately requires output/source derivative slots to fit the common packing
before applying injectivity. Thus multiplication by a frequency cannot silently overflow
into an accepted different derivative literal. `SpD.list_deriv` distributes over duplicate
sparse entries and changes neither their coordinates nor their scale. Reflection gives
`k -> -k`, so the derivative flips the symmetry parity, including zero padding.

**Literal copies and overflow.** `LitCert:39–95`: `fCheck` checks literal and sparse
well-formedness, C/parity/q equality, positive b, strict b<w, `2*l1E<2^w`, and exact packed
equality. Each sparse slot has absolute value at most l1E, even with duplicate/cancelling
entries. Both sides then satisfy `SlotsBounded w` (`2*abs slot<2^w`) and have the same
length. `dCheck` additionally checks both literal guards, matching strides and widths,
positive digit widths, output b_d<w_d, `2*(C*2^(b−1))<2^w`, opposite parity, equal scale,
and equality to the packed derivative. Neither checker infers list equality from an
unguarded integer coincidence. `BrD.ok_of` transports these proved representation facts
from narrow Pc/Pcd to Pb/Pd using the same strides and digit widths; w affects packing,
not the semantic decoded slots. Both Fin 2 directions are supplied via the full [0,1] list.

**Exact products and packed l1.** `Bracket:92–124,178–289`: `brTerm` has semantic weight
rho=coef, zero input errors and zero shift. The integer multiplier includes the odd*odd
sign `psgn(parA && parB)`. `prodCheck` rechecks the exact rational scale equation,
operand half-widths, XOR output parity, and `2*(Ca+Cb)<S`. It never trusts `.num` or
`ratGcd` to have divided exactly; a bad common scale makes the equation fail. Zero or
negative scales are safe because the equation and final absolute value remain present.
Only the H side needs symmetry for the invoked convolution identity; H symmetry is
checked, and its derivative symmetry is proved from the certified derivative list.

The proof first obtains zero-error equality between the actual sum of products and
`Q*evalK (Term.comb ts)`. It then bounds the l1 of this combined list. There is no
termwise triangle bound substituting for the cancellation-sensitive kept coefficient.
`brBX` is a bound on each combined slot from `abs(c)*2^sh*na*mxb` summed over terms;
`2*brBX<2^w` ensures signed packing injectivity. `l1Ok` further supplies positive N,
`l+2<=w`, `N*2^l<2^w` and `loadOk`, so the packed absolute-value sum cannot overflow.
`l1P_eq_of_le` attaches that computed norm to precisely `Term.comb`, padding only zeros.
The fixed `w−16` load level is guarded by those checks even for small w. Empty term lists
require `0<=G`. Empty/zero/cancelling products are not excluded by an unjustified Q>0
assumption and cannot bypass soundness.

**Regrouping and consumer hG.** `Regroup:96–160,163–219`: nonzero coefficient implies
that the shifted total exponent is at least one. Thus natural subtraction in `BT.mon`
can be inverted: `e=p+e_axis−mu_i` together with the componentwise tvalid guard. The guard
prevents underflow in the candidate triple; membership in Hl is checked by inH. Hl.Nodup
is necessary because the cheap list selects e once; Fl may have duplicates, whose
multiplicities are preserved. The hypothesis `F b=0` when coef=0 is discharged by the
actual `coef*val` summand. No nonzero contribution is dropped. `sum_map_filter_ite`, the
two loop commutations and the nodup singleton sum preserve the exact total.

`monsUpTo` lists triples by total degree, not a coordinatewise box. `monOf_triple`
identifies the three components with the same Fin 3 monomial. Consequently
`mem_truncSet_iff` supplies precisely the hp premise of `brAll_sound`, and the exported
bound has N9's absolute value outside the filtered sum of `coef*val`, for every phi.
The sparse F evaluation is independent of packing width w0; H evaluations are transported
with `P0.S=Pb.S` and `P0.b=Pb.b`. No additional normalization or metric is introduced.

**DROP and consumer hDrop.** `Drop:35–67,114–239`: for nonzero coef,
`mdeg(mon)=dropDeg−1`, and the dropped test `L<mdeg(mon)` is equivalent to
`L+2<=dropDeg`. Zero coefficients are handled separately, avoiding invalid degree
subtraction at degree zero. `abs_umon_le` holds at zero and negative u and at r=0.
The check explicitly requires r>=0, also ensuring dropT>=0 for discarded/zero terms.
Kind false uses `|g|<=|qF|*l1E` and `|partial k|<=|qH|*C*nH`; kind true uses the sparse
derivative's `|qF|*l1E` and the undifferentiated H norm `|qH|*nH`. The H derivative
estimate obtains its stride, padding, length and l1 premises from `ok`/`l1Check`.
No missing derivative factor, scale or action power is absorbed into D.

`dropT_eq` and `dropSum_eq` justify the loop rearrangement and factoring exactly over Q.
The proof takes the absolute value of the filtered full sum, bounds each term, casts the
rational nested sum to R, and uses the actual Boolean inequality. It assumes neither a
dropped-bracket bound nor the eventual eta. The retained `_hb` binder is unused but
matches the requested signature. D need not be separately assumed nonnegative: the
checked nonnegative sum is at most D. Repeated Hl entries are allowed here because the
full sums retain them; only the kept regrouping needs Hl.Nodup.

## Hypothesis audit

All data, parameters, indices, points and functions have the carriers in the brief:
Fin 3 actions, Fin 2 angles, natural triples, integer mantissas and rational scales/budgets.
The premise inventory below expands the only proof-field bundle, `BrD.Ok`.
These are generic checker implications, not claimed unconditional source theorems.

| Export | Logical inputs, expanded | Classification / discharge |
|---|---|---|
| `packSum_dlist` | hKS; hlw; hZ; hc; hlen; hb | Checkable layout, width, representation, padding, length, signed-slot facts. |
| `fCheck_sound` | h | One finite Boolean check with precisely the guards listed above. |
| `dCheck_sound` | h | One finite Boolean derivative-copy check with precisely the guards listed above. |
| `sum_filter_mon` | hnd; hin; hF | Structural unique H indices; exact Boolean membership; zero-coefficient summand vanishing. Last is proved for its actual consumer. |
| `brl_sound` | hchk; hmem; hD; hS0; hb0 | Numerical check; selected terms' membership; expanded structural certificates below; equal semantic stride/digit width. |
| `brAll_sound` | hall; hnd; hin; hD; hS0; hb0; hp | Finite per-triple checks; unique H indices; exact membership; structural certificates; equal semantic strides/digit widths; total-degree range. |
| `dropCheck_sound` | hchk; _hb; hF; hH; hS0; hb0; hu | Rational/checkable sum inequality and r>=0; positive b; sparse structural checks; literal and l1 checks; parameter identification; closed box. |
| `BrD.ok_of` | hcS; hcb; hcdS; hcdb; hb; hbd; hw; hS; hf; hdf; hh; hdh | Parameter equalities/positive digit widths and actual fCheck/dCheck/ok/symmetry checks. No BrD.Ok or analytic bound is assumed. |

For `BrD.Ok` (`Bracket:56–75`), every field is accounted for:

| Field | Meaning |
|---|---|
| hb | Positive plain digit width. |
| hbd | Positive derivative digit width. |
| hw | Same target packing widths. |
| hS | Same target strides. |
| fok | Plain F literal well-formedness. |
| fl | Exact F slot equality, C equality, parity equality and scale equality. |
| dfok | Both derivative F literals well-formed. |
| dfl | Both derivative F slot equalities to dlist, C equality, parity flip and scale equality. |
| hok | H literal well-formedness and compact symmetry check. |
| dhok | Both derivative H literals well-formed. |
| dhl | Both derivative H slot equalities to dlist, C equality, parity flip and scale equality. |

The fl/dfl/dhl equations are representation properties certified by the preceding checkers,
not estimates of a bracket or the package's output. `BrD.ok_of` supplies them without
assuming them; this rules out disguising an hG conclusion in a bundle. All logical inputs
are source-contract structural/numerical premises; STANDING/RULED/EXCESS counts are zero.
No conclusion-shaped hG, hDrop, rate or confinement premise is introduced. There is no
Complex.arg branch claim or use of polar coordinates at zero action in these generic files;
all their finite angle polynomials are globally differentiable and periodic as appropriate.

## Verification receipts

Every build was one target per command, invoked serially as
`.drafts/g2/g2lake build KAM.EffectiveStability.Tube.Engine.<Module>`. The prescribed wrapper's
lock, nice 5, memory cap and configured thread setting were left unchanged. There was no
bare build, direct lake/lean call, clean, resource override, Mathlib rebuild or full-library
rebuild. These are warm/cached/replayed build receipts, not clean-build performance claims.

| Module | Exit | Exact final output |
|---|---:|---|
| Deriv | 0 | `Build completed successfully (2935 jobs).` |
| DOpd | 0 | `Build completed successfully (2937 jobs).` |
| Regroup | 0 | `Build completed successfully (2921 jobs).` |
| LitCert | 0 | `Build completed successfully (2938 jobs).` |
| Bracket | 0 | `Build completed successfully (2948 jobs).` |
| Drop | 0 | `Build completed successfully (2949 jobs).` |

Full logs are `Deriv.out`, `DOpd.out`, `Regroup.out`, `LitCert.out`, `Bracket.out`, `Drop.out`
in the audit scratch directory. Reported job counts include cached dependencies. The long
wall times were waits on other workers' builds; they do not measure these core proofs.
No default-heartbeat failure or other in-scope design signal occurred.

Ran the exact command
`.drafts/g2/g2lake env lean .drafts/g2/scratch/audit/n7c-n10-audit-1/Audit.lean`:
**exit 0**, 5.69 seconds including wrapper overhead, no errors or warnings. `Audit.out`
contains all 55 exported theorem axiom queries: 49 use
`[propext, Classical.choice, Quot.sound]`, four use `[propext]`, and two use
`[propext, Quot.sound]`. There is no sorryAx, project axiom or native-reduction axiom.
In particular `packSum_dlist`, all literal/sparse derivative results, both literal-copy
soundness results, `sum_filter_mon`, `brl_sound`, `brAll_sound`, `BrD.ok_of`, `dropSum_eq`,
`mdeg_mon_eq` and `dropCheck_sound` have only the allowed foundations.

The same successful scratch file checks N9's exact hG type over truncSet and directly
applies both outputs in `reducedBracket_bound_of_drop`. Its 19 `decide +kernel` fixtures
check asymmetric row/column signs, both parities, padding, C=0 and signed endpoints;
certified sparse copies with duplicate/cancelling entries and exact derivative literals;
rejection of wrong derivative axis, scale, parity or width and negative DROP radius;
an empty zero-radius DROP; and a one-product bound 18 accepted / 17 rejected, followed
by two nonzero products cancelling to the accepted bound 0. No generated data or
producer is imported by these fixtures.

Probe SHA256:
`489dd0de831416cc2a929bf74c50784057dbba1109099899dd96c40f9029b7f3`.
The optional generated Small/Br smoke build was not run by this auditor.

Independent arithmetic refutation script `refute.py` does not import the producer. It compares
masks with direct signed slot multiplication in 4,636 endpoint/padding/parity cases and
compares regrouped nonzero-term multisets at 125 triples, preserving duplicate F entries.
It also checks the nonzero-term degree and DROP cutoff equivalences. Output:

```text
DERIV_MASK_EDGE_CASES_PASS 4636
REGROUP_MULTISET_AND_DROP_DEGREE_PASS 125
```

These finite checks complement the universal Lean proofs; they do not replace them.
The scratch `Audit.lean` additionally copies N9's hG type and applies both checked outputs
to `reducedBracket_bound_of_drop` itself. Remaining certificate/decomposition/ERR/TAIL
premises in that composition are exactly N9's existing inputs, not claimed paid here.

Final scoped code scan: no sorry/admit/axiom/unsafe/opaque/set_option/EuclideanSpace,
native_decide or sorryAx; no provider, draft-anchor, application, generated-root or root-part
imports. Every file has its copyright, module, public imports, module docstring and exposed
public section. Counts Deriv/DOpd/Regroup/LitCert/Bracket/Drop are
299/213/223/99/405/243, all <=1500, with zero lines >100 characters.

Ran `.drafts/g2/lint_noabi.sh` once (as the worker amendment requires): **exit 1**.
It terminated before the later repository/module/test/frozen-guard checks, with exactly:

```text
Traceback (most recent call last):
  File "<string>", line 34, in <module>
FileNotFoundError: [Errno 2] No such file or directory: '/mnt/HC_Volume_106379410/kam-sjsu-g2/KAM/EffectiveStability/SJSU/Ledger/H/Check21.lean'
```

This is a concurrent generated-file scan failure outside the audited package, not a diagnostic
against any of the six files. No later guard success is inferred from this aborted run.
The generated tree was left untouched. Full output is `lint.out` in audit scratch.
`abi_hashes` is skipped explicitly under WORKER-RULES' 15:25 amendment; the full
`scripts/lint_sources.sh` was not used because it calls lake outside g2lake. Repository lint
is **not green**. The separate scoped scan above does not claim otherwise.

Context hashes: `Check/BracketBound.lean` =
`9b02ad2504627e8819edd158440c36cf6aee01f1dff2fca06efbda5bab7bdf1e`;
`Trig/Poly.lean` = `5b7aa531b933b76ad6adf93db9ea1e6d71ae3fba87ec81c84edcb335041cbdd1`;
`Engine/BTerm.lean` = `7f4b2a0e6dd74bdef4e04504c968265cded7ff3e6c60403f0d3f017d71328131`.
These identify the inspected definitions/consumer, not additional package verdicts. The inspected
N7 DRAFT handoff hash is `9855e989568b344e60a5246db53b42e39f3bb8daecabf4f299938ff3188469d5`;
N10 handoff hash is `a20eb6117f5cc40139b6cc114e5a6447f09e5dc3cf9a380541eea5d53d422baa`.
N1 refers to that N7 handoff snapshot, independently of any subsequent production update.
Final integrity gate at HEAD `288ed55b0e9b5a95429bab48c2479c90c74b930f`: all six
files match the first-line hashes and the reviewed reflow commit. The tracked scoped
`git diff` is empty. A concurrently created untracked `Engine/BrChunk.lean` is outside
this six-file snapshot and was not changed or audited. The consumer/context hashes above
also remain unchanged. Scratch receipts are `snapshot.json`, `reflow.diff`,
`final-integrity.json`, `builds.json`, `probe-result.json` and the stated logs.
Only this report and the permitted audit scratch were written by this auditor; all audit
builds and the probe have exited. No source, handoff, generated or frozen file was repaired.

## Closeout boundary

All in-scope statements/proof arguments, sign and packed-arithmetic guards, required module
builds, axiom checks and exact N9 consumption checks pass. The documentation/compiler notes
remain; the four known width violations are resolved by the separately reviewed reflow.
Repository lint is not green because of the recorded generated-file scan failure.
No production data/producer acceptance, numeric eta or final T2-CONF closure follows from
this generic package verdict. No source repair or mathematical deviation was introduced.

READY g2-audit-n7c-1
