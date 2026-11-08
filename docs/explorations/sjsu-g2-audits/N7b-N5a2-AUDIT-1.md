Audited initial HEAD `80916aa6b05813dc4338e5aaf3af3ed41cbc3043`; reviewed final HEAD `792f86167d1e2cf8488a936898e8e9d1fb932a51` (`git rev-parse HEAD`); package commits `c457b148478945b5a13d795b4169b52a9e9ae9f8`, `b15dedbe8837604c00527d5a1ef263897e4da171`; frozen-v1 SHA256: `KAM/EffectiveStability/Tube/Engine/Exact.lean` = `e24e859b30208b868cc7b9300c9a7e8e4f1ecc1e9dc71a74ec9998909c326f4a`; `KAM/EffectiveStability/Tube/Engine/Block.lean` = `cd6a7e1f8b00dc0b0511b1cb5969c4df6ef00ca7b275a8f6549edde222c5ee47`; `KAM/EffectiveStability/Tube/Engine/Witness.lean` = `afc65622ce7df8472efa9e03920eee16fc1febecc87205d903d290057e3c8455`; `KAM/EffectiveStability/Tube/Engine/Horner.lean` = `50ee2158e1a06841bded4e019dd7012e15ce489f53dd74cbb48dd83a0ce4de84`; `KAM/EffectiveStability/Tube/Engine/Powers.lean` = `1fb867387a456617cfdf9c82cd720796b08e7e3254c184b2719f116c85d9d502`; `KAM/EffectiveStability/Tube/Poly/HtDense.lean` = `97647e40191cc79b9e5295da7cc191995dafcf1f3c03ab4b7e2cfc414401008b`; `KAM/EffectiveStability/Tube/Poly/HtBridge.lean` = `65a4dc378afa69f40a3051a67a266a403c740e0c496b4abfc579926062c854a3`; `KAM/EffectiveStability/SJSU/Ham/HtBridge.lean` = `6eb38b6130de91abf644c06053ec9bc5c8222d75bb47613ee5eb02add5ac7773`; reflow-v2 SHA256 (changed files only): `KAM/EffectiveStability/Tube/Engine/Exact.lean` = `498ee91f44858e5fb0bf86975f343a10de356fe650234aec0025a28c0e647971`; `KAM/EffectiveStability/Tube/Engine/Block.lean` = `ca43ecd423267fb47fe640e86202d29294fd5d280d9bd6b1e1941fbc4e70081c`; `KAM/EffectiveStability/Tube/Engine/Horner.lean` = `026ead2514296865ac21407527123f6d6f8c826708de6aeea7481d8c76defe32`; `KAM/EffectiveStability/Tube/Engine/Powers.lean` = `74999ef7b5d2b9f67cee5cee641fce67fd1ead5d485b729149a1562cdd984d78`.

**Verdict: PASS WITH NOTES — N7-Engine part 2 and N5a-2 HtBridge (generic), audit 1.**

The exact-input, witness, Horner and power certificates are sound within their stated interfaces. The generic bridge identifies the certified Horner function with N5a's actual `hCoef`, including signed generalized binomial coefficients and negative half-powers under `B > 0`. No mathematical blocker or conclusion-shaped extra premise was found. The notes concern the unfinished contextual handoff and the repository lint gate. This report does not certify the production ledger, bracket bounds, or T2-CONF closure.

**Scope, authority and snapshot.** Focused tier-2 refute-first audit following `.drafts/g2/AUDIT-PKG-brief.md`, both named package briefs, AGENTS, PLAN, DECISIONS, WORKER-RULES, the interim N7 handoff and N7-N8-AUDIT-1. N5a's `Tube/Poly/HTilde.lean` and N4's `Witness/HalfPow.lean` supply the literal coefficient/exponent definitions. No frozen anchor is being sealed here: the audited exports are ordinary checker infrastructure and a generic source bridge. The source/statement methodology is applied to these actual exports, without substituting a similarly named frozen theorem.

The user authorizes this report and the protocol's temporary axiom probe; all lake/lean invocations use `g2lake`, one module/process at a time. No source, handoff, generated root, manifest or git-history change was made by this auditor. No delegation, production run, broad build, clean, or network lookup was used. Audit evidence is under `.drafts/g2/scratch/audit/n7b-n5a2-audit-1/`.

The initial eight source files matched their respective package commits. During the audit, another worker reflowed nine overlong lines in Exact/Block/Horner/Powers. The entire diff was reviewed: after deleting whitespace, each file is byte-identical to its package version. Reflow-v2 landed as commit `792f86167`; it changes no identifiers, terms, binders, signs, imports or claims. Both sets of hashes are on the first line. Line references below use frozen-v1 unless explicitly marked v2. The final width scan and four reflow builds use v2; the other four source files remain unchanged.

Excluded exactly as requested: uncommitted Engine Bracket, DOpd, Regroup, Deriv and Drop; other new Engine work; SJSU/Ledger/H and Small; SJSU/Ham/HtBridgeInst; producer correctness and production performance. Imported part-1 infrastructure was inspected at the point of use, in light of the prior audit; this is not a repeat audit of its entire data/producer surface.

**Findings and dispositions.**

1. **N1 — Contextual N5a-2 handoff remains a template (documentation, nonblocking for this generic scope).** At the inspected handoff `docs/explorations/sjsu-g2-handoffs/N5a2-HtBridge.md:6,11–14,79–80`, the literal text is `**Status:** INSTANCE_STATUS`, `HTDENSE_LINES`, `HTBRIDGE_LINES`, `SJSUHT_LINES`, `INST_LINES`, and `CHECKS_PLACEHOLDER`. Lines 14 and 56 also list the instance file/theorem, which this launch expressly excludes. Consequently this document is not a finished check receipt and cannot establish instance completion. Suggested fix: fill the generic status, actual line counts, build/axiom receipts, and clearly label the instance as a separate deliverable until independently checked. Refutation: matched the placeholder tokens literally, compared its advertised exports with the committed generic files and the explicit exclusion, and independently ran all required generic checks below. This is a confirmed documentation incompleteness, not evidence against the proved generic identities. No assertion is made here about the excluded instance's actual status. Inspected handoff SHA256: `0bbeb5c891567888b02d83e047cf10898864ae6adb6690d6550bb33a375bb5fd`.

2. **N2 — Known width lint is resolved by the separately reviewed reflow.** Original locations: `Engine/Exact:227`; `Block:78,96,126`; `Horner:118,135,218,219`; `Powers:155`. Representative text: `decide (m.1 + m.2.1 + m.2.2 ≤ D.M) && litCheck ...` (Horner:135). These nine lines violated the 100-character rule but did not alter theorem meaning. Suggested fix was line reflow only. The separate worker supplied precisely that fix; all eight final scoped files now have zero overlong lines. Status: resolved in reflow-v2; not an open mathematical finding. Deprecated `if_pos`/`if_neg` and the unused simp argument in Witness:272 remain compiler warnings, not proof failures; replacing them is optional cleanup outside this audit's write authority.

Repository lint disposition is recorded separately below. No suspected defect in a pinned mathematical source was found; N1/N2 concern local documentation/style. No mathematical deviation or repair was introduced.

N5a source-definition SHA256 (`KAM/EffectiveStability/Tube/Poly/HTilde.lean`): `ca3bfd7407c72dd586e1bf2abad568a94f5cee213f3772036635fc4eb281afac`; N4 exponent/cast source SHA256 (`KAM/EffectiveStability/Tube/Witness/HalfPow.lean`): `665b8aa8c619b6d605768390fdb015592a348a8d5b97d9163ede7570198da84e`. These are contextual source anchors, not additional audited packages.

**Exact inputs and rounding: PASS.**

- `Exact:30–88,160–175,226–279`: `input_sound` compares the full exact rational dense series with the actual decoded literal. Each discrepancy is `c_i - q*(digit_i - 2^(b-1))`. The check requires the full `(2C+1)^2` input length, even parity, literal well-formedness, and both coordinate-weighted error sums. Thus `zipWith` cannot silently discard unpaired coefficients. `length_compactDigits`, `getD_compactDigits`, and `evalK_litList` identify the same digits and modes in the semantic sum.
- Balanced `treeSumG 64` is proved equal to `List.sum` for every fuel/list, including fuel zero; insufficient balancing fuel never truncates a sum. It is only an evaluation-depth device.
- The checker does not trust a producer's description of rounding. It measures the actual signed discrepancy and its two derivative weights exactly in ℚ, then casts to ℝ. Any chosen rounding/truncation rule must pass those comparisons. No unproved nearest-rounding or half-ulp claim is used. Negative scales and signed mantissas are handled by the discrepancy and absolute values.
- `Block:37–86`, through `Step.prod_sound` and `out_sound`: `comb_cert` attaches `Term.combZ` to the semantic combination before using its packed l1 claim. `2*BX < 2^w` supplies signed-slot boundedness; `l1Ok` and `l1P_eq_of_le` identify the computed norm, with only zero padding added.
- For output literal comparison, the exact packed difference is `αX*Xz - αO*2^(w*shift)*O.Z`, with `αX > 0`, `O.q*αX = Q*αO`, and a signed-slot overflow guard. Its l1 bounds include every changed or dropped slot. The error normalization is `|Q|/αX`; the derivative estimate uses the full product half-width `Cp`. `lit_cert` adds product error `E` and output-difference error `F` in both components. Zero or negative `Q` does not bypass the scale equation or absolute-value bounds.

**Horner blocks and signs: PASS.**

- `Horner:72–135,177–279`: U uses T with `Pt 2`; V uses U with `Pt 1`; h uses V with `Pt 0`. Tags select precisely the same indices in the true functions and the certificate operands. Layout checks are retained at each step: U has half-width `CT+CP`, V multiplies that by a `CP` operand, and the final h check requires its V operands on `CP`. A different output layout makes the next Boolean check fail; it is not silently reinterpreted.
- `cOf` extracts a rational numerator but is not trusted as a division theorem. Every resulting integer multiplier must satisfy `ρ*qA*qB*psgn(parA && parB) = Q*c*2^sh` in `prodCheck`. A nonintegral ratio with the wrong numerator fails this exact equation. Signed binomial factors therefore retain their signs. Product error contributions use `|ρ|`.
- `vBlock_sound` requires `m3≤M` through the check and `m2<M+1-m3`; hence `m2+m3≤M`. Membership in `uIdx` supplies the bound on `n3`; `n2s`/`n1s` supply the other bounds. Every consumed exponent `n_j-2m_j` lies in the certified power interval. Natural subtraction in loop lengths is guarded; exponent subtraction is in ℤ throughout.
- Empty U/V/h groups are skipped structurally. A V certificate is claimed only for `vIdx≠[]`, and `HCert_of` only for `hIdx≠[]`. `hBlock_sound` may also certify an empty exact sum if its check passes. No certificate of an arbitrary skipped output literal is claimed. Missing lookup parameters use defaults but still undergo the same check; defaults supply no theorem assumption.
- Certificate premises are about earlier operands: T/powers feed U/V; V/powers feed h. The scratch composition applies `TCerts_of`, `PCerts_of`, `VCerts_of`, then `hBlock_sound` and the source bridge. The composed result assumes checks/data facts, not the desired h certificate.

Independent hand computation: `gbQ 1 2 = (1/2)*(-1/2)/2 = -1/8`, `gbQ 1 3 = 1/16`, and `gbQ 2 2 = 0`; zero coefficients are dropped, negative ones are retained. For `cos(φ₀-2φ₁)`, the partials are `-sin(φ₀-2φ₁)` and `2 sin(φ₀-2φ₁)`. The library convention `trig false = cos`, `trig true = -sin`, `psgn false=1`, `psgn true=-1` agrees with `pderiv_evalR`; no `2π` belongs in these radian-angle derivatives. The rational binomial cases were also checked by kernel reduction in the scratch probe.

**Witnesses and power blocks: PASS.**

- `Block:100–138`: the centre index is `C+S*C` in the expanded layout and `C+(2C+1)*C` in compact storage. `2*c0-l1` is a valid lower bound even if the central coefficient is negative (`c0≤|c0|`); it is not incorrectly treated as equality.
- `Witness:52–154`: `sqrt_sound` forms the true residual by combining the input B error with the checked `W*W` residual. The check budgets `ρ-eB₀`, `ρ'-eB₁`, so the combined errors are at most `ρ,ρ'`. Strict `σ₀>0`, the lower bound `Bt≥σ₀²`, and `W≥w₀≥0` select the positive square-root branch. Multiplying the literal lower bounds requires positive rational scales and checks them explicitly. The real and rational error expressions match, including `(ρ'+2*e₀*ω₁)/(2*σ₀)`.
- `Witness:166–257`: the inverse residual compares `W*Y` with an independently certified constant-one literal, adding its input error. The proof carries `Bt≥σ₀²` and the sqrt certificate into N4's `invSqrt_witness`; it does not assume an inverse certificate. The derivative bound retains both the residual-derivative term divided by `σ₀` and the value-residual term divided by `σ₀²`.
- `Powers:104–215`: `pBase` establishes powers `0,2,1,-1` from exact one/B inputs and the two residual checks. `PCert_of` derives `Bt>0` from `σ₀>0` and `Bt≥σ₀²` before invoking `sqrtPow_add`. Hence `zpow_add₀` is used only with a nonzero square root.
- Positive recurrence: `k=(k-2)+2` for `k≥3`. Negative base: `-2=(-1)+(-1)`. Negative recurrence: `-k=-(k-2)+(-2)` for `k≥3`. Both induction arguments decrease by two with all Nat/Int casts justified; there is no accidental natural truncation in a negative exponent. The exported range is exactly `[-(2M+1),Nmax]`, for `j<3`, including endpoints, small `M` and small `Nmax`. The check's unconditional `-2` step can be stronger than necessary when `M=0`, but does not weaken or falsify the conclusion.
- `powOk_cert`'s `hid` is an explicitly named internal algebraic product identity, not the certificate conclusion. All its calls in `PCert_of` prove `hid` from the exponent arithmetic and the positivity already derived from `pBase`. The final `PCerts_of` has only the Boolean per-mode check as its logical premise.

**Regrouping and source coefficient fidelity: PASS.**

`Poly/HtBridge:131–163` exports the brief's target (1) with the same parameter order, types, hypotheses, indices and RHS. Its only textual binder-name change is `hnd` to `_hnd`. An exact-type scratch `example` containing the brief's full statement is discharged by `HData.Ht_eq_sum D Tt Pt hnd hb m φ`. No weaker replacement statement is used. `Nodup` is retained but unused because list regrouping preserves multiplicity.

`Ut_eq` removes only a zero `gbQ` factor or a bound failure excluded by `hb`; `Vt_eq` and `Ht_eq_range` remove only zero factors/empty sums. Regrouping by bounded `n1`, then `n2`, expands back to the same complete list. It neither assumes symmetry nor changes a factor two or the P0/P1/P2 order.

`Poly/HtBridge:185–198,311–347` proves target (2) against N5a's actual `hCoef` in `HTilde:70–75`, not a fresh alias. `gbQ_eq_gbinom` uses N4's rational-cast theorem and the exact denominator `m!`. `rpow_half_sub (hpos φ j)` converts integer powers of the positive square root to `B^(n/2-m)`; this is not asserted for zero or negative B. The proof expands `Fin 3` in order `![n1,n2,n3]`, uses the specified T/B data equalities, and then passes from the duplicate-free group list to `expSet rows`. `hns` supplies every row exponent; additional groups contribute zero because their `Tn` sum is empty. Duplicate Hamiltonian rows remain in `Tn`; only the outer exponent-group index is deduplicated.

**Dense indexing and SJSU facts: PASS.**

- `Exact:93–129`; `HtDense:30–73`: with `K=2C+1`, slot `c+K*r` decodes to `(c-C,r-C)`, with column first. `inBox` prevents negative coordinates from being clipped by `.toNat`; `boxIdx_lt` and `boxKey_boxIdx` prove range and inverse on that domain. Hand checks at `C=2`: slot 3 is `(1,-2)`, slot 21 is `(-1,2)`, slots 0/24 are `(-2,-2)/(2,2)`. The `C=0` centre is slot 0. These asymmetric and endpoint cases also passed kernel checks.
- `pDense` sums all entries with the same slot, so duplicates/cancellation are preserved. `scatter` has a different contract: strict `incFrom` and an upper bound on all indices. `sum_scatter` proves no pair is skipped under that contract; duplicate slots fail the strict-order check rather than disappear from a proved equality. The scratch check exercises both duplicate accumulation and duplicate rejection.
- `HtBridge:201–227`: `rowCoefQ` is exactly `c/(10^E*N^(|b|+|b'|))` and casts to N5a's real row coefficient. `tTerms` uses the actual `rowMode=(b₀-b'₀,b₁-b'₁)`, with no reversal, conjugation or extra cosine normalization. `Tn_eq_denseCos` preserves every row and its coefficient, including repeated modes.
- `HtBridge:231–283`: `bPairs` places `Ibar_j` at the centre and `-modeK_j*σ` at each mode. For mode `(1,-2)` the three coefficients are `(-σ,2σ,-σ)`, since the third mode is `-1-(-2)=1`. This agrees independently with the gradient of `-σ sin(φ₀-2φ₁)` in the reduced-angle convention. There is no extra half-mode factor. A zero mode or repeated mode that duplicates the centre/slot makes `incFrom` fail; no unconditional scatter theorem hides this restriction.
- `SJSU/Ham/HtBridge:30–106`: actual kernel checks establish a strictly positive B margin, box inclusion `CP=30`, and sorted B pairs; the real cosine bound then proves `sjsuB_pos` for every angle. All six row exponents are bounded by 9 using the nine homogeneous Hw degree facts, implying row differences in `[-9,9]`; `sjsuTn_eq_denseCos` uses `CT=9`. These are concrete source-data facts with no assumed conclusions. Equality to the separately emitted N7 ledger remains an excluded instance obligation.

Literal-definition audit for `denseCos`, `Bt`, `Tt`, `Pt`, `gbQ`, `Ut/Vt/Ht`, `ofTriple/tripleExp`, `pDense/scatter`, `tTerms` and `bPairs`: `BODY_MATCH: OK; PUBLIC_CARRIER: OK; WELL_DEFINEDNESS: N/A_LITERAL; CHARACTERIZATION: N/A_LITERAL; CHOICE_INDEPENDENCE: N/A; DEFINITION_VERDICT: PASS`. They are the displayed finite formulas/algorithms, with no arbitrary choice or invented replacement object. `HData` is plain ledger data with no proof fields. The source-identification theorem retains the source's `B>0` domain; these results make no claim about `Complex.arg`, polar differentiability at zero action, or a global Hamiltonian reconstruction.

**Binder audit.** SOURCE here refers to the explicitly specified generic checker/bridge contract; these helpers are implications from certified input stages, not frozen unconditional source theorems. All logical input bundles are expanded below. There are no hidden instance premises in the five focus exports. Each row below accounts for one outer binder; counts are `(SOURCE,STANDING,TYPING,RULED,EXCESS)`.

| Export | Binder | Bin / authority |
|---|---|---|
| `Ht_eq_sum` | `D : HData` | TYPING, target (1) |
| same | `Tt` | TYPING, target (1) true row functions |
| same | `Pt` | TYPING, target (1) true power functions |
| same | `_hnd : D.ns.Nodup` | SOURCE, target (1) |
| same | `hb` | SOURCE, all three exponent bounds in target (1) |
| same | `m` | TYPING, exponent triple |
| same | `φ` | TYPING, `Fin 2 → ℝ` |
| `Ht_eq_hCoef` | `D` | TYPING, generic ledger |
| same | `E` | TYPING, coefficient scale exponent |
| same | `N` | TYPING, coefficient denominator parameter |
| same | `rows` | TYPING, N5a row data |
| same | `B` | TYPING, N5a centre family |
| same | `hnd` | SOURCE, duplicate-free group index for list-to-Finset conversion |
| same | `hb` | SOURCE, target (1)'s three bounds |
| same | `hT` | SOURCE, target (2)'s allowed T data identification |
| same | `hB` | SOURCE, target (2)'s allowed B data identification |
| same | `hpos` | SOURCE, target (2), `∀φ j, B φ j>0` |
| same | `hns` | SOURCE, structural row-exponent coverage |
| same | `m` | TYPING, exponent triple |
| same | `φ` | TYPING, reduced-angle point |
| `vBlock_sound` | `D` | TYPING, generic ledger |
| same | `Tt` | TYPING, true row functions |
| same | `Pt` | TYPING, true power functions |
| same | `n1` | TYPING, block index |
| same | `m3` | TYPING, block index |
| same | `uprm` | TYPING, numerical parameters |
| same | `vprm` | TYPING, numerical parameters |
| same | `h` | SOURCE, check `vBlock=true` |
| same | `hT` | SOURCE, certified previous input stage, expanded below |
| same | `hP` | SOURCE, certified previous power stage, expanded below |
| same | `m2` | TYPING, output index |
| same | `hm2` | SOURCE, checked block's output range |
| same | `hv` | SOURCE, nonempty selected structural group |
| `hBlock_sound` | `D` | TYPING, generic ledger |
| same | `Tt` | TYPING, true row functions |
| same | `Pt` | TYPING, true power functions |
| same | `m` | TYPING, output index |
| same | `o` | TYPING, numerical parameters |
| same | `h` | SOURCE, check `hBlock=true` |
| same | `hV` | SOURCE, certified previous V stage, expanded below |
| same | `hP` | SOURCE, certified previous power stage, expanded below |
| `PCerts_of` | `D` | TYPING, generic ledger |
| same | `s` | TYPING, square-root check parameters |
| same | `i` | TYPING, inverse check parameters |
| same | `pp` | TYPING, power-product check parameters |
| same | `h` | SOURCE, `∀j<3, pAll=true`; finite rational/structural checks |

Outer binder counts are respectively `(2,0,5,0,0)`, `(6,0,7,0,0)`, `(5,0,8,0,0)`, `(3,0,5,0,0)`, `(1,0,4,0,0)`. No EXCESS premise is hidden in `HData` or a certificate alias.

The shared certificate expansion below applies separately to `hT`, `hP`, and `hV`; it inventories every semantic field rather than treating `Cert` as an uninterpreted standing assumption.

| Expanded field / binder | Exact obligation | Bin / producer |
|---|---|---|
| `TCerts`: `n` | exponent triple | TYPING |
| `TCerts`: membership antecedent | `n∈D.ns` | SOURCE structural selector |
| `PCerts`: `j`, `k` | natural mode and integer exponent | TYPING, each |
| `PCerts`: `j<3` | mode range | SOURCE structural selector |
| `PCerts`: lower endpoint | `-(2M+1)≤k` | SOURCE structural selector |
| `PCerts`: upper endpoint | `k≤Nmax` | SOURCE structural selector |
| `VCerts`: `n1`, `m2`, `m3` | natural indices | TYPING, each |
| `VCerts`: first-index membership | `n1∈n1s` | SOURCE structural selector |
| `VCerts`: degree range | `m2+m3≤M` | SOURCE structural selector |
| `VCerts`: nonempty group | `vIdx≠[]` | SOURCE structural selector |
| each `Cert.wf.pack` | `packSum w o.l=o.Z` | SOURCE input representation |
| each `Cert.wf.cols` | `colsOk ...=true` | SOURCE input representation |
| each `Cert.wf.len` | `o.l.length≤Layout.len ...` | SOURCE input representation |
| each `Cert.close` first conjunct | true input function differentiable | SOURCE input certificate |
| each `Cert.close` second conjunct | literal function differentiable | SOURCE input certificate |
| each `Cert.close` third conjunct | `∀φ, |f φ-o.eval φ|≤e₀` | SOURCE input certificate |
| each `Cert.close` fourth conjunct | `∀φ a, |∂a f-∂a o.eval|≤e₁` | SOURCE input certificate |
| each `Cert.l1le` | `l1 o.l≤n` | SOURCE numerical input claim |
| power `Mx` | `∀x∈o.l, |x|≤2^(b-1)` | SOURCE representation bound |
| power symmetry | `symOk o.par o.l=true` | SOURCE representation check |
| power exact length | `o.l.length=Layout.len ...` | SOURCE representation check |

Points/directions/elements universally quantified in these fields are TYPING; their range/membership antecedents are structural selectors, not additional externally supplied estimates. The eight Cert fields are actually supplied by `TCerts_of`/`PCerts_of`/`VCerts_of` in the compiled composition. Treating them as premises of the corresponding named generic composition lemmas introduces no certificate of that lemma's own output. In particular, neither source bridge assumes `Ht=hCoef`, and `PCerts_of` assumes no PCert/C1Close result.

**Verification receipts.**

All eight targeted module builds returned 0 and printed `Build completed successfully`. Commands were exactly `.drafts/g2/g2lake build <module>`; prefix below is `KAM.EffectiveStability.`. The four reflowed files were built again after their change; those extra checks were warranted by the changed bytes. Every build was serial. The wrapper supplies the lock, nice 5, 6 GB memory cap and its configured `LEAN_NUM_THREADS=2`; the wrapper was not changed. Job counts include cached/replayed dependencies and are not fresh compilation counts or a production benchmark.

| Module | Verified exit | Successful build job count |
|---|---:|---:|
| `Tube.Engine.Exact` | 0 | 2933 |
| `Tube.Engine.Block` | 0 | 2934 |
| `Tube.Engine.Witness` | 0 | 2937 |
| `Tube.Engine.Horner` | 0 | 2935 |
| `Tube.Engine.Powers` | 0 | 2939 |
| `Tube.Poly.HtDense` | 0 | 2937 |
| `Tube.Poly.HtBridge` | 0 | 2984 |
| `SJSU.Ham.HtBridge` | 0 | 3133 |

Ran `.drafts/g2/g2lake env lean .drafts/g2/scratch/audit/n7b-n5a2-audit-1/Axioms.lean`: **exit 0**, no errors. It queried every theorem declared in the eight audited modules: **80 queries**, all within the permitted foundation set. Counts: 70 use `[propext, Classical.choice, Quot.sound]`; five use `[propext, Quot.sound]`; four use `[propext]`; `sum_pairSumG` is axiom-free. In particular `input_sound`, `comb_cert`, `lit_cert`, `sqrt_sound`, `invSqrt_sound`, `vBlock_sound`, `hBlock_sound`, `TCerts_of`, `PCert_of`, `PCerts_of`, `Ht_eq_sum`, `Ht_eq_hCoef`, all dense-series equalities, and the concrete SJSU B/T facts use only the three permitted foundations. No `sorryAx`, project axiom or native reduction axiom occurs.

The same scratch file compiled exact target-(1)/(2) applications and this term-level stage composition, with all data facts and Boolean checks explicitly supplied:

```lean
have powers := D.PCerts_of hp
have inputs := D.TCerts_of ht
have vals := D.VCerts_of D.Tt D.Pt hv inputs powers
have out := D.hBlock_sound D.Tt D.Pt hh vals powers
have heq : D.Ht D.Tt D.Pt m = fun φ => hCoef E N rows B (ofTriple m) φ :=
  funext fun φ => D.Ht_eq_hCoef E N rows B hnd hb hT hB hpos hns m φ
rw [heq] at out
exact out
```

This produces `((D.H m).opd D.P).Cert ... (fun φ => hCoef E N rows B (ofTriple m) φ) ...`, without taking a T/PCerts/VCerts/HCert result as a premise of the composition. It demonstrates generic producer-to-source attachment, not that the excluded SJSU ledger's checks have passed. The additional kernel checks for asymmetric box indices, signed/zero binomials, duplicate accumulation and strict-scatter rejection also succeeded. Probe SHA256: `939f3d84ddbc77859d9e9ddd0a05d3dbacf25627065a8515d290ec97494f481e`. Axiom output is preserved in `axioms.log`; the temporary Lean probe is removed after recording its evidence, as required by the statement-audit workflow.

Module hygiene: all eight files have copyright, `module`, `public import`, module docstring, exposed public section, and appropriate `Fin 2`/`Fin 3` real carriers. Zero `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `set_option`, `EuclideanSpace`, provider imports or generated-root imports occur in the scoped files. Final line counts in order Exact/Block/Witness/Horner/Powers/HtDense/Poly-HtBridge/SJSU-HtBridge are **284/145/308/287/220/179/351/109**, all below 1500. Final scoped overlong-line count: **0**.

Ran `.drafts/g2/lint_noabi.sh` once, to completion: **exit 1**. `abi_hashes` was skipped exactly as WORKER-RULES requires; the full `scripts/lint_sources.sh` was not invoked because that step calls lake outside `g2lake`. The actual receipt (`lint.log`) reports:

```text
Lean lines over 100 characters:
  Engine/Bracket.lean:21:101
  Engine/Deriv.lean:135:111,172:106,210:101
  Engine/Regroup.lean:195:101
FileNotFoundError: .../SJSU/Ledger/Small/Br/Check0.lean
check_lean_modules: PASS (18622 Lean files, 0 comparator configurations)
Ran 29 tests in 5.220s — OK
Ran 8 tests in 0.012s — OK
FROZEN-ANCHOR GUARD OK
```

All five reported width violations belong to excluded uncommitted files. The missing excluded Small/Br file was observed by `gen_root_imports.py --check` during the shared-worktree scan; it is not an import of any audited module. This is a recorded repository-check failure, not a package proof failure. Suggested disposition: finish the excluded files and rerun the repository landing gate after that work is stable. No generated roots or excluded source were changed by this auditor. Repository lint is **not green**; the eight audited sources pass their own final width/module/forbidden-token checks.

Final integrity gate: all eight files match the first-line reflow-v2 hashes (or unchanged frozen-v1 hashes), the scoped `git diff` is empty after the other worker's reflow commit, and only this report plus the explicitly permitted scratch evidence were written by this auditor. The transient Lean probe has been removed; no Lean process from this audit remains.

**Closeout.** All in-scope mathematical statements, source identifications, sign/rounding arguments, build checks and axiom checks pass. The documentation note remains; the known source-width note is resolved by the independently performed whitespace reflow. No hypothesis or frozen declaration was repaired. Acceptance remains limited to the eight hashed files and this generic composition: no ledger instance, bracket/rate bound, production run or final confinement theorem is promoted by this verdict.

READY g2-audit-n7b-1
