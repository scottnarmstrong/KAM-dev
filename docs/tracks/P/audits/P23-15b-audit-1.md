# P23-15b independent audit 1

Verdict: **PASS WITH NOTES** for `KAM.Planetary.osc_averaging` and
`KAM.Planetary.averaged_remainder`; **PASS WITH NOTES** for the signed `OscHyp`.
No blocking mathematical or signature finding was found in the scoped package.
This is infrastructure proof closure, not a seal of P-G, P-PLANAR, P-FIXED or another frozen anchor.
There is no provider export or frozen seal body in this package; those particular checks are
inapplicable. The corresponding fresh-name signed-statement applications were checked instead.

## Scope and authority

Audited HEAD `d6199e68457990f8cdaef41793a0bd53ae09a953` against `inp`
`312ad165a54f89ca92b3f6ae004d60658180bfce`, using the requested `git diff inp...HEAD`.
Git warns that there are multiple merge bases and selects
`31f0bfbf70c07b1eefd006237f331c00e003a0e5`; the other reported base is
`1fdb2e87e5ff70ec4742914c2e5c8cfec723f578`. This report records that exact comparison,
without silently selecting a different diff.

Read AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief, the handoff AUDIT FOCUS,
the P23 design including Revision 3 and row P23-15, the live shared
`/root/code/KAM-inp/.drafts/design/P23Signatures.lean` (the worktree has no local copy;
SHA-256 `d067d47dbabfdf4913da3e2b76886eb29598f4502ad16318d328568d82380cd3`),
Track P statement, Part 2 blueprint L198–237 and the relevant frozen definitions.
The handoff's scope restricts review to `OscillatorHyp.lean` and `OscillatorFinite*.lean`:
11 new modules, 1,914 physical lines total, largest 378. Inherited P23-13j files and
rename ports are dependencies, not independently re-audited implementations here.
The complete `osc_iter` contract was inspected at its application boundary.
Only this report is edited; temporary probes were created in this worktree's
`.lake/abi-scratch/` and removed after successful elaboration.

## Findings and proof assessment

**N1 — nonblocking ownership deviation.** Design L288 says “`OscHyp` is defined in
P23-06, not the late finite-iteration module.” The package instead adds
`OscillatorHyp.lean:28`; the scoped import graph puts this source-only record below the
finite setup without a cycle. Its fields exactly match the signed fixture after removing
whitespace. This is the prover's disclosed placement deviation, not a new premise.

**N2 — generated root.** Source lint has the brief's permitted stale `KAM.lean`
exception (exact receipt below). The root was not regenerated.

**N3 — conservative signed binders.** `averaged_remainder:157–161` retains unused `hμ`
and `hP`. The implementation needs only H's nonnegativity and bound for μ•P directly,
so μ=0 would also be permitted by the proof. The upper part of hε is not needed in
the specialization because H already supplies the cutoff budget. These are preserved signed
premises, not added proof assumptions. `osc_averaging` even permits E=0.

`OscillatorFiniteStep:39–78` supplies `gj` as the previous zero-mode increments, their
actual larger radii and proved bounds, then calls **full `osc_iter`**, not just its core.
Its returned map, gp and fp are definitionally the recursive map, next G and next F.
Conditional reality is instantiated with the carried real h/G/F facts. `oinv_all`
proves invariants and earlier-stage conclusions together; no norm, realness or transformed
Hamiltonian conclusion is smuggled into the final source premise H.

`OIter.step` contains only the explicit numerical majorant inequality. It does not contain
a bound on the actual remainder. `OStepConc` and `OInv` are internal output predicates;
they are proved by stage induction. `OscGood` packages desired schedule budgets as an
internal conditional interface, with `oscGood_single` and `oscGood_multi` proving its
existence from H and exhaustive complementary case inequalities. `MultiData` contains
positive input numbers, floor-budget inequalities and the original smallness inequality;
its fields are constructed from H at CaseA L316–317, not assumed by the signed exports.

Case A explicitly defines N as the natural floor κ/(12 log 2), proves N≥1 from its case
condition (so the blueprint's N=0 stop is unnecessary in this branch), uses the first losses
(r/8,rp/8,rq/8,s/6), then N further losses (r/(8N),rp/(8N),rq/(8N),s/(4N)). The bounds
`oscW_head`, `oscW_tail`, `multi_rsum`, `multi_stage_num`, `MultiData.hstage`, `.step_zero`,
`.step_succ`, `.small` discharge the star norm and contraction budgets. The choice
c₁=293 b E²/P improves the blueprint's 294: 2048/7<293, and (4/3)293<400.
The geometric sums and final floor inequality prove the exponential tail and all four
displacements. Case B constructs the single doubled-loss schedule and proves its contraction.
No budget override occurs; the split MultiData lemmas are present and elaborate at defaults.
The historical monolithic heartbeat failure itself was not reproduced.

`OIter.struct/ident/disp` use the actual composition, maps-to domains and four component
seminorms with the existing telescope. Lattice equivariance and reality propagate through
these same maps. `OSched.G_indep` proves independence of fast angles from literal coefficient
formulas. `OIter.gen_tail` subtracts the initial zero mode and bounds only later increments;
the final F is separately bounded by exp(-κ/6)E. `averaged_remainder` constructs
R=(g−μ P̂₀)+fs, proves zero-mode linearity, reality/class and the sum bound, and proves
exp(-(2π K s₀)/6)=ε⁵ for the signed logarithmic K. No correction term is absorbed into
the exponential tail.

The signed `OscHyp`, `osc_averaging`, and `averaged_remainder` declarations are exact
whitespace-normalized textual matches (including every binder, premise, carrier, constant,
let and conclusion). Fresh-name copies of both literal signed theorem types elaborate with
`by exact KAM.Planetary.osc_averaging H` and
`by exact KAM.Planetary.averaged_remainder hε hμ H hP`. No signature fixture with a sorry
body is imported into production or the probe. Relative to the blueprint's notation E=‖f‖, H permits any proved nonnegative upper
bound E; this is a valid stronger formulation with the same estimates and smallness.
Internal numerical helpers state their
explicit conditional inequalities; their extra numerical premises are discharged in the
construction and do not replace an unconditional blueprint result.

## Declaration-by-declaration review

Names below are fully qualified; locations are relative to this worktree. All declarations
are public in the module public section. Rows include every theorem and defined object,
not auto-generated projections/recursors.

| Node | Declaration and locator | Verdict | Reason |
|---|---|---|---|
| bpP:p2:osc-averaging / O1–O2 | `KAM.Planetary.OscHyp` (OscillatorHyp.lean:28; structure) | PASS | Exact signed source-premise record; ownership note N1. |
| bpP:p2:osc-averaging / averaged-remainder | `KAM.Planetary.oscGood_of_hyp` (OscillatorFinite.lean:40; theorem) | PASS | Exact signed export or proved assembly/coefficient helper. |
| bpP:p2:osc-averaging / averaged-remainder | `KAM.Planetary.osc_zero_mode` (OscillatorFinite.lean:48; theorem) | PASS | Exact signed export or proved assembly/coefficient helper. |
| bpP:p2:osc-averaging / averaged-remainder | `KAM.Planetary.osc_averaging` (OscillatorFinite.lean:73; theorem) | PASS | Exact signed export or proved assembly/coefficient helper. |
| bpP:p2:osc-averaging / averaged-remainder | `KAM.Planetary.coeff_const_mul_flat'` (OscillatorFinite.lean:135; theorem) | PASS | Exact signed export or proved assembly/coefficient helper. |
| bpP:p2:osc-averaging / averaged-remainder | `KAM.Planetary.coeff_smul_osc` (OscillatorFinite.lean:148; theorem) | PASS | Exact signed export or proved assembly/coefficient helper. |
| bpP:p2:osc-averaging / averaged-remainder | `KAM.Planetary.averaged_remainder` (OscillatorFinite.lean:157; theorem) | PASS | Exact signed export or proved assembly/coefficient helper. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.stepVal` (OscillatorFiniteCaseA.lean:30; def) | PASS | Numerical input bundle or proved budget/construction, discharged from OscHyp. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.multi_width_ρ` (OscillatorFiniteCaseA.lean:40; theorem) | PASS | Numerical input bundle or proved budget/construction, discharged from OscHyp. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.multi_width_σ` (OscillatorFiniteCaseA.lean:53; theorem) | PASS | Numerical input bundle or proved budget/construction, discharged from OscHyp. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.multi_Q_lower` (OscillatorFiniteCaseA.lean:73; theorem) | PASS | Numerical input bundle or proved budget/construction, discharged from OscHyp. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.MultiData` (OscillatorFiniteCaseA.lean:93; structure) | PASS | Numerical input bundle or proved budget/construction, discharged from OscHyp. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.MultiData.hb` (OscillatorFiniteCaseA.lean:111; theorem) | PASS | Numerical input bundle or proved budget/construction, discharged from OscHyp. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.MultiData.hP` (OscillatorFiniteCaseA.lean:115; theorem) | PASS | Numerical input bundle or proved budget/construction, discharged from OscHyp. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.MultiData.hN0` (OscillatorFiniteCaseA.lean:122; theorem) | PASS | Numerical input bundle or proved budget/construction, discharged from OscHyp. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.MultiData.hc0` (OscillatorFiniteCaseA.lean:124; theorem) | PASS | Numerical input bundle or proved budget/construction, discharged from OscHyp. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.MultiData.hc1` (OscillatorFiniteCaseA.lean:128; theorem) | PASS | Numerical input bundle or proved budget/construction, discharged from OscHyp. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.MultiData.hstage` (OscillatorFiniteCaseA.lean:132; theorem) | PASS | Numerical input bundle or proved budget/construction, discharged from OscHyp. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.first_facts` (OscillatorFiniteCaseA.lean:148; theorem) | PASS | Numerical input bundle or proved budget/construction, discharged from OscHyp. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.MultiData.first_facts` (OscillatorFiniteCaseA.lean:184; theorem) | PASS | Numerical input bundle or proved budget/construction, discharged from OscHyp. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.MultiData.step_zero` (OscillatorFiniteCaseA.lean:192; theorem) | PASS | Numerical input bundle or proved budget/construction, discharged from OscHyp. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.MultiData.Q_succ_pos` (OscillatorFiniteCaseA.lean:210; theorem) | PASS | Numerical input bundle or proved budget/construction, discharged from OscHyp. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.MultiData.step_succ` (OscillatorFiniteCaseA.lean:215; theorem) | PASS | Numerical input bundle or proved budget/construction, discharged from OscHyp. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.MultiData.small` (OscillatorFiniteCaseA.lean:246; theorem) | PASS | Numerical input bundle or proved budget/construction, discharged from OscHyp. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.oscGood_multi` (OscillatorFiniteCaseA.lean:280; theorem) | PASS | Numerical input bundle or proved budget/construction, discharged from OscHyp. |
| stepP:p2:oa-concl / N6 telescope | `KAM.Planetary.OSched.Ψ` (OscillatorFiniteChain.lean:30; def) | PASS | Actual-map telescope, domains, lattice, reality, identity or component seminorm. |
| stepP:p2:oa-concl / N6 telescope | `KAM.Planetary.semiF1` (OscillatorFiniteChain.lean:37; def) | PASS | Actual-map telescope, domains, lattice, reality, identity or component seminorm. |
| stepP:p2:oa-concl / N6 telescope | `KAM.Planetary.semiF2` (OscillatorFiniteChain.lean:41; def) | PASS | Actual-map telescope, domains, lattice, reality, identity or component seminorm. |
| stepP:p2:oa-concl / N6 telescope | `KAM.Planetary.semiL1` (OscillatorFiniteChain.lean:45; def) | PASS | Actual-map telescope, domains, lattice, reality, identity or component seminorm. |
| stepP:p2:oa-concl / N6 telescope | `KAM.Planetary.semiL2` (OscillatorFiniteChain.lean:49; def) | PASS | Actual-map telescope, domains, lattice, reality, identity or component seminorm. |
| stepP:p2:oa-concl / N6 telescope | `KAM.Planetary.semiF1_apply` (OscillatorFiniteChain.lean:53; theorem) | PASS | Actual-map telescope, domains, lattice, reality, identity or component seminorm. |
| stepP:p2:oa-concl / N6 telescope | `KAM.Planetary.semiF2_apply` (OscillatorFiniteChain.lean:55; theorem) | PASS | Actual-map telescope, domains, lattice, reality, identity or component seminorm. |
| stepP:p2:oa-concl / N6 telescope | `KAM.Planetary.semiL1_apply` (OscillatorFiniteChain.lean:57; theorem) | PASS | Actual-map telescope, domains, lattice, reality, identity or component seminorm. |
| stepP:p2:oa-concl / N6 telescope | `KAM.Planetary.semiL2_apply` (OscillatorFiniteChain.lean:59; theorem) | PASS | Actual-map telescope, domains, lattice, reality, identity or component seminorm. |
| stepP:p2:oa-concl / N6 telescope | `KAM.Planetary.OIter.stage_mapsTo` (OscillatorFiniteChain.lean:68; theorem) | PASS | Actual-map telescope, domains, lattice, reality, identity or component seminorm. |
| stepP:p2:oa-concl / N6 telescope | `KAM.Planetary.OIter.struct` (OscillatorFiniteChain.lean:75; theorem) | PASS | Actual-map telescope, domains, lattice, reality, identity or component seminorm. |
| stepP:p2:oa-concl / N6 telescope | `KAM.Planetary.OIter.ident` (OscillatorFiniteChain.lean:100; theorem) | PASS | Actual-map telescope, domains, lattice, reality, identity or component seminorm. |
| stepP:p2:oa-concl / N6 telescope | `KAM.Planetary.OIter.disp` (OscillatorFiniteChain.lean:113; theorem) | PASS | Actual-map telescope, domains, lattice, reality, identity or component seminorm. |
| stepP:p2:oa-concl | `KAM.Planetary.oscBound_zero` (OscillatorFiniteGen.lean:33; theorem) | PASS | Literal zero modes; later-increment sum and its bound. |
| stepP:p2:oa-concl | `KAM.Planetary.OSched.G_indep` (OscillatorFiniteGen.lean:42; theorem) | PASS | Literal zero modes; later-increment sum and its bound. |
| stepP:p2:oa-concl | `KAM.Planetary.OIter.S_final_pos` (OscillatorFiniteGen.lean:48; theorem) | PASS | Literal zero modes; later-increment sum and its bound. |
| stepP:p2:oa-concl | `KAM.Planetary.OIter.tail_sum` (OscillatorFiniteGen.lean:52; theorem) | PASS | Literal zero modes; later-increment sum and its bound. |
| stepP:p2:oa-concl | `KAM.Planetary.OIter.gen_tail` (OscillatorFiniteGen.lean:75; theorem) | PASS | Literal zero modes; later-increment sum and its bound. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.multiOSched` (OscillatorFiniteMulti.lean:30; def) | PASS | Explicit schedule, weights, geometric sequence or derived sum/gap bound. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.oscW` (OscillatorFiniteMulti.lean:34; def) | PASS | Explicit schedule, weights, geometric sequence or derived sum/gap bound. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.oEps` (OscillatorFiniteMulti.lean:39; def) | PASS | Explicit schedule, weights, geometric sequence or derived sum/gap bound. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.oEps_zero` (OscillatorFiniteMulti.lean:43; theorem) | PASS | Explicit schedule, weights, geometric sequence or derived sum/gap bound. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.oEps_succ` (OscillatorFiniteMulti.lean:45; theorem) | PASS | Explicit schedule, weights, geometric sequence or derived sum/gap bound. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.oEps_nonneg` (OscillatorFiniteMulti.lean:47; theorem) | PASS | Explicit schedule, weights, geometric sequence or derived sum/gap bound. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.oEps_tail_sum` (OscillatorFiniteMulti.lean:52; theorem) | PASS | Explicit schedule, weights, geometric sequence or derived sum/gap bound. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.oEps_n` (OscillatorFiniteMulti.lean:61; theorem) | PASS | Explicit schedule, weights, geometric sequence or derived sum/gap bound. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.oEps_disp_σ` (OscillatorFiniteMulti.lean:73; theorem) | PASS | Explicit schedule, weights, geometric sequence or derived sum/gap bound. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.oEps_disp_ρ` (OscillatorFiniteMulti.lean:96; theorem) | PASS | Explicit schedule, weights, geometric sequence or derived sum/gap bound. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.multi_R_gap` (OscillatorFiniteMulti.lean:122; theorem) | PASS | Explicit schedule, weights, geometric sequence or derived sum/gap bound. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.multi_S_gap` (OscillatorFiniteMulti.lean:131; theorem) | PASS | Explicit schedule, weights, geometric sequence or derived sum/gap bound. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.multi_R_head` (OscillatorFiniteMulti.lean:140; theorem) | PASS | Explicit schedule, weights, geometric sequence or derived sum/gap bound. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.multi_S_head` (OscillatorFiniteMulti.lean:148; theorem) | PASS | Explicit schedule, weights, geometric sequence or derived sum/gap bound. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.ratio_tail` (OscillatorFiniteMulti.lean:156; theorem) | PASS | Explicit schedule, weights, geometric sequence or derived sum/gap bound. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.ratio_head` (OscillatorFiniteMulti.lean:161; theorem) | PASS | Explicit schedule, weights, geometric sequence or derived sum/gap bound. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.oscW_tail` (OscillatorFiniteMulti.lean:172; theorem) | PASS | Explicit schedule, weights, geometric sequence or derived sum/gap bound. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.oscW_head` (OscillatorFiniteMulti.lean:186; theorem) | PASS | Explicit schedule, weights, geometric sequence or derived sum/gap bound. |
| stepP:p2:oa-iter / oa-concl | `KAM.Planetary.multi_rsum` (OscillatorFiniteMulti.lean:208; theorem) | PASS | Explicit schedule, weights, geometric sequence or derived sum/gap bound. |
| stepP:p2:oa-first / oa-iter | `KAM.Planetary.exp_one_lt_3` (OscillatorFiniteNumerics.lean:27; theorem) | PASS | Proved real inequality or explicit first-remainder formula; source constants preserved/improved. |
| stepP:p2:oa-first / oa-iter | `KAM.Planetary.inv_one_sub_le'` (OscillatorFiniteNumerics.lean:32; theorem) | PASS | Proved real inequality or explicit first-remainder formula; source constants preserved/improved. |
| stepP:p2:oa-first / oa-iter | `KAM.Planetary.osc_step_first` (OscillatorFiniteNumerics.lean:36; theorem) | PASS | Proved real inequality or explicit first-remainder formula; source constants preserved/improved. |
| stepP:p2:oa-first / oa-iter | `KAM.Planetary.osc_step_single` (OscillatorFiniteNumerics.lean:61; theorem) | PASS | Proved real inequality or explicit first-remainder formula; source constants preserved/improved. |
| stepP:p2:oa-first / oa-iter | `KAM.Planetary.osc_step_big` (OscillatorFiniteNumerics.lean:82; theorem) | PASS | Proved real inequality or explicit first-remainder formula; source constants preserved/improved. |
| stepP:p2:oa-first / oa-iter | `KAM.Planetary.firstEps` (OscillatorFiniteNumerics.lean:105; def) | PASS | Proved real inequality or explicit first-remainder formula; source constants preserved/improved. |
| stepP:p2:oa-first / oa-iter | `KAM.Planetary.firstEps_nonneg` (OscillatorFiniteNumerics.lean:107; theorem) | PASS | Proved real inequality or explicit first-remainder formula; source constants preserved/improved. |
| stepP:p2:oa-first / oa-iter | `KAM.Planetary.firstEps_le` (OscillatorFiniteNumerics.lean:111; theorem) | PASS | Proved real inequality or explicit first-remainder formula; source constants preserved/improved. |
| stepP:p2:oa-first / oa-iter | `KAM.Planetary.osc_first_le` (OscillatorFiniteNumerics.lean:119; theorem) | PASS | Proved real inequality or explicit first-remainder formula; source constants preserved/improved. |
| stepP:p2:oa-first / oa-iter | `KAM.Planetary.multi_stage_num` (OscillatorFiniteNumerics.lean:137; theorem) | PASS | Proved real inequality or explicit first-remainder formula; source constants preserved/improved. |
| stepP:p2:oa-iter | `KAM.Planetary.OSched` (OscillatorFiniteSched.lean:36; structure) | PASS | Explicit recursive objects or schedule facts; no output assumed. |
| stepP:p2:oa-iter | `KAM.Planetary.OSched.Φ0` (OscillatorFiniteSched.lean:46; def) | PASS | Explicit recursive objects or schedule facts; no output assumed. |
| stepP:p2:oa-iter | `KAM.Planetary.OSched.seq` (OscillatorFiniteSched.lean:52; def) | PASS | Explicit recursive objects or schedule facts; no output assumed. |
| stepP:p2:oa-iter | `KAM.Planetary.OSched.G` (OscillatorFiniteSched.lean:65; def) | PASS | Explicit recursive objects or schedule facts; no output assumed. |
| stepP:p2:oa-iter | `KAM.Planetary.OSched.F` (OscillatorFiniteSched.lean:67; def) | PASS | Explicit recursive objects or schedule facts; no output assumed. |
| stepP:p2:oa-iter | `KAM.Planetary.OSched.Φ` (OscillatorFiniteSched.lean:70; def) | PASS | Explicit recursive objects or schedule facts; no output assumed. |
| stepP:p2:oa-iter | `KAM.Planetary.OSched.inc` (OscillatorFiniteSched.lean:73; def) | PASS | Explicit recursive objects or schedule facts; no output assumed. |
| stepP:p2:oa-iter | `KAM.Planetary.OSched.U` (OscillatorFiniteSched.lean:76; def) | PASS | Explicit recursive objects or schedule facts; no output assumed. |
| stepP:p2:oa-iter | `KAM.Planetary.OSched.G_zero` (OscillatorFiniteSched.lean:79; theorem) | PASS | Explicit recursive objects or schedule facts; no output assumed. |
| stepP:p2:oa-iter | `KAM.Planetary.OSched.F_zero` (OscillatorFiniteSched.lean:81; theorem) | PASS | Explicit recursive objects or schedule facts; no output assumed. |
| stepP:p2:oa-iter | `KAM.Planetary.OSched.G_succ` (OscillatorFiniteSched.lean:83; theorem) | PASS | Explicit recursive objects or schedule facts; no output assumed. |
| stepP:p2:oa-iter | `KAM.Planetary.OSched.F_succ` (OscillatorFiniteSched.lean:85; theorem) | PASS | Explicit recursive objects or schedule facts; no output assumed. |
| stepP:p2:oa-iter | `KAM.Planetary.OSched.G_eq_sum` (OscillatorFiniteSched.lean:92; theorem) | PASS | Explicit recursive objects or schedule facts; no output assumed. |
| stepP:p2:oa-iter | `KAM.Planetary.OIter` (OscillatorFiniteSched.lean:103; structure) | PASS | Explicit recursive objects or schedule facts; no output assumed. |
| stepP:p2:oa-iter | `KAM.Planetary.OInv` (OscillatorFiniteSched.lean:138; def) | PASS | Explicit recursive objects or schedule facts; no output assumed. |
| stepP:p2:oa-iter | `KAM.Planetary.OStepConc` (OscillatorFiniteSched.lean:147; structure) | PASS | Explicit recursive objects or schedule facts; no output assumed. |
| stepP:p2:oa-iter | `KAM.Planetary.OIter.R_anti` (OscillatorFiniteSched.lean:186; theorem) | PASS | Explicit recursive objects or schedule facts; no output assumed. |
| stepP:p2:oa-iter | `KAM.Planetary.OIter.U_succ_subset` (OscillatorFiniteSched.lean:194; theorem) | PASS | Explicit recursive objects or schedule facts; no output assumed. |
| stepP:p2:oa-iter | `KAM.Planetary.OIter.U_sub_start` (OscillatorFiniteSched.lean:199; theorem) | PASS | Explicit recursive objects or schedule facts; no output assumed. |
| stepP:p2:oa-iter | `KAM.Planetary.OIter.U_sub_big` (OscillatorFiniteSched.lean:204; theorem) | PASS | Explicit recursive objects or schedule facts; no output assumed. |
| stepP:p2:oa-first / oa-iter | `KAM.Planetary.realOn_h_of_real` (OscillatorFiniteSetup.lean:32; theorem) | PASS | Conditional internal schedule interface; all conditions discharged downstream. |
| stepP:p2:oa-first / oa-iter | `KAM.Planetary.OscGood` (OscillatorFiniteSetup.lean:48; def) | PASS | Conditional internal schedule interface; all conditions discharged downstream. |
| stepP:p2:oa-first / oa-iter | `KAM.Planetary.oiter_of_hyp` (OscillatorFiniteSetup.lean:68; theorem) | PASS | Conditional internal schedule interface; all conditions discharged downstream. |
| stepP:p2:oa-first / oa-iter | `KAM.Planetary.osc_E_le` (OscillatorFiniteSetup.lean:97; theorem) | PASS | Conditional internal schedule interface; all conditions discharged downstream. |
| stepP:p2:oa-first, Case B | `KAM.Planetary.oscGood_single` (OscillatorFiniteSingle.lean:32; theorem) | PASS | Proved doubled-loss construction under precisely Case B. |
| stepP:p2:oa-iter | `KAM.Planetary.actionNbhd_sub` (OscillatorFiniteStep.lean:32; theorem) | PASS | Derived from full osc_iter and strong stage induction. |
| stepP:p2:oa-iter | `KAM.Planetary.oinv_zero` (OscillatorFiniteStep.lean:35; theorem) | PASS | Derived from full osc_iter and strong stage induction. |
| stepP:p2:oa-iter | `KAM.Planetary.ostep_conc` (OscillatorFiniteStep.lean:39; theorem) | PASS | Derived from full osc_iter and strong stage induction. |
| stepP:p2:oa-iter | `KAM.Planetary.oinv_succ` (OscillatorFiniteStep.lean:80; theorem) | PASS | Derived from full osc_iter and strong stage induction. |
| stepP:p2:oa-iter | `KAM.Planetary.oinv_all` (OscillatorFiniteStep.lean:85; theorem) | PASS | Derived from full osc_iter and strong stage induction. |
| stepP:p2:oa-iter | `KAM.Planetary.OIter.stage` (OscillatorFiniteStep.lean:99; theorem) | PASS | Derived from full osc_iter and strong stage induction. |

## Definition classification

- `OscHyp`: exact source/typing/positivity/nonresonance/smallness record.
- `OSched`: three literal radius schedules; only x's strip is used. Unused strip fields
  in p/q introduce no extra analytic object.
- `OSched.Φ0`, `seq`, `G`, `F`, `Φ`, `inc`, `U`, `Ψ`: actual oscillator time-one maps,
  structurally recursive Hamiltonians, literal Fourier-zero increments, stage domains and
  composition. Defined on the full carrier, with no alternative fallback relied on by proofs.
- `OIter`: source premises and explicit finite numerical budgets; `OInv`/`OStepConc`:
  inductively proved stage predicates, not source hypotheses of the exported results.
- `semiF1`, `semiF2`, `semiL1`, `semiL2`: genuine coordinate-projection seminorms on the
  whole phase space, with rfl evaluation lemmas.
- `firstEps`, `multiOSched`, `oscW`, `oEps`, `stepVal`: literal arithmetic, schedule,
  weight, geometric-majorant and step-majorant formulas. Real division is total in Lean;
  applications prove positivity of all denominators, including N in Case A.
- `OscGood`: explicit existential schedule feasibility predicate, proved from the source H.
- `MultiData`: numeric input bundle for the split default-heartbeat proof, fully constructed.

There are 24 explicit non-theorem declarations. No new instances or hidden mathematical
assumptions were found. No junk-value branch is used to obtain a substantive conclusion.

## Validation receipts

All Lean/Lake/checker invocations for this audit are sequential and use `LEAN_NUM_THREADS=1`
and `nice -n 5`; the build uses the prescribed compile gate. No source or generated file is changed.

### Targeted build

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2315b KAM.Planetary.Averaging.OscillatorFinite
```

Exit 0. Output:

```text
[inp-gate] slot 1 acquired 14:14:55 for KAM.Planetary.Averaging.OscillatorFinite
⚠ [9164/9164] Replayed KAM.Planetary.Averaging.OscillatorFinite
warning: KAM/Planetary/Averaging/OscillatorFinite.lean:159:37: Variable name `hμ` is not explicitly referenced.
warning: KAM/Planetary/Averaging/OscillatorFinite.lean:161:5: Variable name `hP` is not explicitly referenced.
Build completed successfully (9164 jobs).
```

The wrapper invokes `nice -n 5 lake build`; no full-library rebuild was requested.
The diagnostic's suggested linter option was not applied.

### Signed statements and all public theorem axioms

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2315b.lean
```

Exit 0, no errors or warnings. The scratch file imports only the proved facade, opens the
same namespaces as the signature, copies both signed types literally under fresh names,
uses the exact applications recorded above, and prints axioms for all 79 explicit public
theorems in the declaration table. All 79 records have the same allowed set. Exact output:

```text
'KAM.Planetary.oscGood_of_hyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_zero_mode' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_averaging' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.coeff_const_mul_flat'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.coeff_smul_osc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.averaged_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_width_ρ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_width_σ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_Q_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.MultiData.hb' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.MultiData.hP' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.MultiData.hN0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.MultiData.hc0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.MultiData.hc1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.MultiData.hstage' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.first_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.MultiData.first_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.MultiData.step_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.MultiData.Q_succ_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.MultiData.step_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.MultiData.small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscGood_multi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.semiF1_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.semiF2_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.semiL1_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.semiL2_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.OIter.stage_mapsTo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.OIter.struct' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.OIter.ident' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.OIter.disp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscBound_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.OSched.G_indep' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.OIter.S_final_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.OIter.tail_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.OIter.gen_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oEps_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oEps_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oEps_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oEps_tail_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oEps_n' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oEps_disp_σ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oEps_disp_ρ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_R_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_S_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_R_head' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_S_head' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ratio_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ratio_head' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscW_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscW_head' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_rsum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.exp_one_lt_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.inv_one_sub_le'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_step_first' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_step_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_step_big' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.firstEps_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.firstEps_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_first_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.multi_stage_num' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.OSched.G_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.OSched.F_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.OSched.G_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.OSched.F_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.OSched.G_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.OIter.R_anti' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.OIter.U_succ_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.OIter.U_sub_start' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.OIter.U_sub_big' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.realOn_h_of_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oiter_of_hyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_E_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscGood_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.actionNbhd_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oinv_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ostep_conc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oinv_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oinv_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.OIter.stage' depends on axioms: [propext, Classical.choice, Quot.sound]
```


### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Averaging.OscillatorHyp KAM.Planetary.Averaging.OscillatorFiniteSched KAM.Planetary.Averaging.OscillatorFiniteStep KAM.Planetary.Averaging.OscillatorFiniteChain KAM.Planetary.Averaging.OscillatorFiniteGen KAM.Planetary.Averaging.OscillatorFiniteNumerics KAM.Planetary.Averaging.OscillatorFiniteSetup KAM.Planetary.Averaging.OscillatorFiniteSingle KAM.Planetary.Averaging.OscillatorFiniteMulti KAM.Planetary.Averaging.OscillatorFiniteCaseA KAM.Planetary.Averaging.OscillatorFinite
```

One invocation, exit 0. Exact output:

```text
replaying KAM.Planetary.Averaging.OscillatorFinite
replaying KAM.Planetary.Averaging.OscillatorFiniteCaseA
replaying KAM.Planetary.Averaging.OscillatorFiniteMulti
replaying KAM.Planetary.Averaging.OscillatorFiniteSingle
replaying KAM.Planetary.Averaging.OscillatorFiniteSetup
replaying KAM.Planetary.Averaging.OscillatorFiniteNumerics
replaying KAM.Planetary.Averaging.OscillatorFiniteGen
replaying KAM.Planetary.Averaging.OscillatorFiniteChain
replaying KAM.Planetary.Averaging.OscillatorFiniteStep
replaying KAM.Planetary.Averaging.OscillatorFiniteSched
replaying KAM.Planetary.Averaging.OscillatorHyp
```

### Source lint

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1 solely for the explicitly permitted generated-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (668 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No forbidden proof escapes, resource overrides, EuclideanSpace, overlong Lean lines or
oversized files were reported. Module checks, frozen-anchor guard and elaborated ABI hashes
passed. The root was left untouched as required by the audit brief.

## Import, naming and immutable-file checks

The recursive local import closure has 118 KAM modules, no `KAM.Provider.*`, and no frozen
theorem module (hence no DRAFT_SORRY theorem dependency). Frozen dependencies are definitions:
ActionNbhd, ComplexStrip, HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine,
IsPrimaryOnStrip, IsRealOnReals, OmegaZero, SymplecticForm, and Planetary Fast/Phase/Slow.
Their literal coordinate carriers and conventions were inspected; no frozen theorem is proved here.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty (exit 0,
only the recorded merge-base warning). `git diff --check inp...HEAD` exits 0.
No resource option, EuclideanSpace or bare `fastShift` appears in the scoped modules.
The upstream map uses `oscFastShift`; the finite package uses its step map and explicit fast
lattice translations. A declaration-stem scan of all KAM source found only names in different
namespaces (`Sched` versus `OSched`, ordinary unqualified helpers versus `OIter`, `KAM.Head`, and the
unqualified TwoScale `seq`); no full public name collision was found. The imported and
built environment also accepts all 103 declarations.

## Errata, deviations and limits

No new suspected defect of the pinned mathematical sources or blueprint was found in the
scoped proof. The 293-versus-294 numerical improvement and direct proof that Case A has N≥1
are valid strengthened intermediate estimates. Source comparison here is to the specified
blueprint/contracts and their source locators; this report does not claim a new independent
PDF transcription audit or re-audit of P23-13j internals.

Disclosed deviations: OscHyp placement (N1), the fresh public coefficient helper
`coeff_const_mul_flat'` instead of editing the earlier private helper, and the focused module
split. None changes the signed interface. Lint's generated-root exception is N2. No frozen
file, manifest, generated root or README was edited. No uncertainty remains about the two
signed types or the axiom sets. Successful package checks do not establish downstream
consumer applicability or a frozen campaign headline.
