# Independent package audit 1: P5-KH

Overall verdict: **PASS WITH NOTES** for the scoped P5-KH implementation. No blocking
statement, definition, coverage or proof finding was found in `KAMInputs*.lean`.
The notes are the allowed stale generated root, nonfatal build linter suggestions, and
the bridge export/binder presentation change described below. This package supplies infrastructure; it exports no provider and
seals no frozen anchor. **P-G (`properlyDegenerateKAM`) remains DRAFT_SORRY**;
no verdict of seal-readiness is issued for P-G, P-PLANAR or P-FIXED.

## Snapshot, scope and authority

Worktree `/root/code/KAM-inp-p5kh`; HEAD
`966e014f9ca917f428e12331f0466f34fdd1d44e`; comparison ref `inp`
`b6dab3a6fc8453330a4abaa465a782e1aa713798`. `git diff inp...HEAD` contains exactly
six new Lean files, 1317 lines total. The untracked handoff existed before the audit.
The requested absolute worktree-local report destination overrides the generic brief's
main-worktree destination. No production file, frozen file, manifest or git state was edited.

Read AGENTS.md, PLAN.md, DECISIONS.md, the shared package-audit brief, P5-KH handoff,
P45 design including Revision 4, design audits 1–4, shared signatures, the assigned
blueprint lemma/proof steps, track-P statement, actual frozen P-G telescope and its
relevant frozen definitions. D20 controls the frozen contract despite historical prose
still saying approval is pending. Earlier audit receipts were context, not verification
of this implementation.

Signature authority: `/root/code/KAM-inp/.drafts/design/P45Signatures.lean`, SHA256
`586ed2e3188b154d5cc6d44d3f85b420ef85ddd7faaa2bcbb6d6ca6db7d0f304`.
The production `pg_avg` spelling is used consistently by this shared file and selected
`pgAvg`; `Averaging.lean:15` explains its rename from the design's older `avg` spelling,
to avoid colliding with the existing P2/P3 export. The selected witness is not changed.

## Literal contract and complete node coverage

The three signed definition bodies `kamH`, `kamF`, `pgKamScale` match the shared
signature formulas after whitespace normalization. The complete signed theorem headers
of `kam_hyp`, `pg_kam_hyp`, `pg_kam_dictionary` also match after whitespace normalization,
including explicit binders and their order. Fresh probes repeat their literal conclusions
and apply the actual exports. No added source premise, wider constant dependence,
weakened conclusion or different norm/carrier was found.

The unsigned helpers state their actual local claims and are not substituted for stronger
source exports. The design node table at lines 176–180 maps exactly these five graph rows
to KAMInputs, all covered:

| Assigned graph node | Established by | Verdict | Coverage |
|---|---|---|---|
| `bpP:p5:kam-hyp` | `kamH`, `kamF`, `kam_hyp`, `pg_kam_hyp`, `pgKamScale` | PASS | Actual P3 `KamHyp`, all quantitative fields and smallness. |
| `stepP:p5:kh-dom` | `actionNbhd_sub_analytic`, `kh_slow_bounds`, `kamPolar_mem`, holomorphy, periodicity and reality exports | PASS | Entire complex tube and strip; principal square-root branch justified. |
| `stepP:p5:kh-h` | `freq_kamH`, `kamH_injOn`, `kamH_hessian` | PASS | Injectivity, inverse equivalence, full and block operator bounds. |
| `stepP:p5:kh-f` | `kamF_eq`, `kamF_sup`, `kam_hyp` | PASS | Actual averaged remainder, fifth-order bound and weighted conversion. |
| `stepP:p5:kh-norm` | `mu_lt_one_of_admissible`, `pg_kam_hyp` | PASS | All positivity/order/normalization requirements, not only the analytic estimates. |

The package's additional signed dictionary has all four clauses: L, rhoHat, eHat,
and equality of dioBase with the original-frequency `pgD0`. `kam_c1` itself belongs to
P5-SCALE, not this slice; its explicit formula is used unchanged. No assigned node is
left as a signature, a premise or an assumed bundled field.

### Frequency bridge and consumer applicability

Design Appendix A at line 1443 and shared S:746 name `complexFrequency_real`.
`KAMInputsFreq.lean:116` implements its full mathematical statement as
`complexFrequency_realSlice`: for every source mu in `[0,mu0]` and every real J with
`blockFast J ∈ V`, the derived complex frequency is the real inclusion of the original
`freq H0 P0 Omega beta mu J`. There is no slow-action bound, admissibility premise,
analytic-radius premise, or assertion about arbitrary source values on the boundary.
The helper uses local equality on the open set V to compare derivatives; the slow block
uses the actual on-V jet coefficients. This is precisely the intended bridge.

Presentation deviation: the export has a fresh name, and mu and J are
implicit rather than explicit. The `@`-application probe repeats the design's explicit
telescope verbatim and succeeds. This is a mathematical contract match, not a claim that
the spelling and implicit-binder annotations are byte-identical. No production occurrence
of the old name was found; `realFreq_kamH` consumes the new bridge and
`pg_kam_dictionary` uses it at points of the checked core. The six designated package
exports keep their signed spelling and binder annotations. Thus no required consumer
has lost its needed conclusion.

### Full averaging strip and weighted estimate

Let `w = pgWidth d`, `s = sigma = w/(24*pi)`. `kamPolar_mem` uses the open
period-one strip `s+sigma = w/(12*pi)`. Scaling angles by `2*pi` gives the open
radian strip `w/6` exactly, which is the averaging domain's fast strip. Strict inequalities
remain strict: no boundary evaluation or extra strip margin is used. Slow polar components
are bounded by `sqrt(2*abs Jslow) * exp(abs Im(2*pi*theta)) < 2r`, with
`2r < pgOscRadius/2`, and positive real slow actions keep the square root holomorphic.

`kamF_eq` is the literal `(mu*pgRemainder + A.remainder)/(2*pi)` identity.
`kamF_sup` gives `(2^5*CQ+2*LP)*mu*r^5/(2*pi)` uniformly on that full open strip.
`wbound_of_sup_bound` (KAM/Weighted/SupWeighted.lean:78) requires positive s and sigma,
class membership and a uniform pointwise bound on the open strip s+sigma; it does not
require extension to its boundary or any still larger strip. Its factor is
`coth(pi*sigma)^(a+b) = coth(w/24)^(a+b)`, exactly absorbed by `kam_c1`.
P3's requested `geometricWidth(w/15+w/60)` is exactly `w/(24*pi)`.
The full averaging strip is therefore sufficient; the handoff's tight-width observation
is accurate and is not a gap.

Revision-4 reality is respected: `kamF_real` uses the extension's proved `ext_P_real`,
not equality with the arbitrary total source P outside its constrained cylinder.
`kh_real_fast` also proves the on-V premise needed for original jet identifications.
The Hamiltonian normalization and real frequency both retain one division by `2*pi`.

## Declaration-by-declaration decisions

All 63 declarations are public and in `KAM.Planetary`: 59 theorems and four definitions.
The node column names the source step or the helper's actual role, not a claim that each
helper is an independent blueprint node. File labels below abbreviate
`KAM/Planetary/PGAssembly/<label>.lean`.

| Node / role | Lean declaration and locator | Verdict | Reason |
|---|---|---|---|
| `kh-dom` | `kh_mem_dom` (KAMInputs:33) | PASS | Exact identification of weighted domain with strip and frozen action neighbourhood. |
| `kh-dom / reality` | `kh_realNbhd_of_mem` (KAMInputs:39) | PASS | Real inclusion is isometric; witness neighbourhood transfers exactly. |
| `kh-dom / kh-f` | `kamF_inClass` (KAMInputs:47) | PASS | Holomorphy and period one on every S no greater than the full strip. |
| `kam-hyp` | `kam_hyp` (KAMInputs:59) | PASS | Exact signed local estimates, all six clauses and four Hessian bounds. |
| `kam-hyp / kh-norm` | `pg_kam_hyp` (KAMInputs:110) | PASS | Exact signed delivered P3 record, including positivity, widths and smallness. |
| `KAM dictionary` | `pg_kam_dictionary` (KAMInputs:188) | PASS | All four signed equalities; original real frequency used on the checked core. |
| `kam-hyp` | `kamH` (KAMInputsBase:29) | PASS | Literal signed complexIntegrable/(2*pi). |
| `KAM scale dictionary` | `pgKamScale` (KAMInputsBase:33) | PASS | Literal signed ScaleData, with initialL rather than prematurely replacing L. |
| `kh-norm` | `mu_lt_one_of_admissible` (KAMInputsBase:39) | PASS | Derived from chosen rstar and muStar bound, not an added assumption. |
| `dictionary L` | `pgKamScale_L` (KAMInputsBase:45) | PASS | Uses C1 >= 1 and 0 < mu < 1 to evaluate initialL. |
| `dictionary cutoff` | `pgKamScale_cutoff` (KAMInputsBase:57) | PASS | r and mu cancel; real-power square is justified by r > 0. |
| `dictionary radius` | `pgKamScale_rhoHat` (KAMInputsBase:84) | PASS | Both gamma/M branches agree; same minimum as params. |
| `dictionary error` | `pgKamScale_eHat` (KAMInputsBase:103) | PASS | Exact algebraic cancellation with positive mu. |
| `kam-hyp` | `kamF` (KAMInputsF:30) | PASS | Literal signed transformed extension Hamiltonian minus kamH. |
| `kh-dom helper` | `kamPolarPt` (KAMInputsF:36) | PASS | Literal complex polar composition with 2*pi angle scaling. |
| `kh-f helper` | `kh_avg_spec` (KAMInputsF:39) | PASS | Specification of the same selected pgAvg, from proved pg_avg. |
| `kh-dom helper` | `kh_cpow_half_sq` (KAMInputsF:42) | PASS | Principal complex square root squares to x even at zero. |
| `kh-dom helper` | `kh_norm_cos_le` (KAMInputsF:46) | PASS | Global complex cosine estimate by exp(abs imaginary part). |
| `kh-dom helper` | `kh_norm_sin_le` (KAMInputsF:59) | PASS | Global complex sine estimate by exp(abs imaginary part). |
| `kh-dom helper` | `kh_exp_le_two` (KAMInputsF:72) | PASS | Elementary bound on the explicit real interval [0,1/2]. |
| `kh-dom helper` | `pgWidth_lt_half` (KAMInputsF:78) | PASS | Derived from extension delta bound. |
| `kh-dom helper` | `kamPolarPt_fst_fast` (KAMInputsF:83) | PASS | Fast position component is scaled angle. |
| `kh-dom helper` | `kamPolarPt_fst_slow` (KAMInputsF:87) | PASS | Slow position is square root times sine, consistent with assembleComplex order. |
| `kh-dom helper` | `kamPolarPt_snd_fast` (KAMInputsF:92) | PASS | Fast momentum/action unchanged. |
| `kh-dom helper` | `kamPolarPt_snd_slow` (KAMInputsF:96) | PASS | Slow momentum is square root times cosine. |
| `kh-dom` | `kh_slow_bounds` (KAMInputsF:102) | PASS | Re slow action > l1/2 and norm < r^2/2 throughout the full tube. |
| `kh-dom` | `kh_fast_bounds` (KAMInputsF:131) | PASS | Retains a checkedCore witness at the same rho. |
| `kh-dom` | `kamPolar_mem` (KAMInputsF:139) | PASS | Full open strip maps into averagingDomain; oscillator components < 2r. |
| `kh-dom helper` | `kh_ext_fast_mem` (KAMInputsF:201) | PASS | Extracts fast action extension membership from the original tube witness. |
| `kh-f` | `kamF_eq` (KAMInputsF:212) | PASS | Averaging identity and exact oscillator action recover the two remainders. |
| `kh-f` | `kamF_sup` (KAMInputsF:249) | PASS | Uniform bound with 2^5 CQ + 2 LP and the single 2*pi divisor. |
| `kh-dom helper` | `kamPolarPt_differentiableAt` (KAMInputsF:297) | PASS | Positive real slow actions keep cpow off its cut; no global smoothness claim. |
| `kh-dom` | `kamF_differentiableOn` (KAMInputsF:326) | PASS | Holomorphic on full strip/action domain via actual averaging and extension maps. |
| `frequency bridge helper` | `fderiv_complex_realSlice` (KAMInputsFreq:33) | PASS | Derivative restriction, eventual local identity and uniqueness; all helper premises explicit. |
| `domain helper` | `realInclusion_mem_actionNbhd` (KAMInputsFreq:66) | PASS | Zero-distance witness, requires only positive radius and membership. |
| `frequency bridge helper` | `complexFast_realSlice` (KAMInputsFreq:70) | PASS | H0 agrees on a real open neighbourhood inside V; derivative restriction applies. |
| `frequency bridge helper` | `jpGrad_realSlice` (KAMInputsFreq:84) | PASS | Differentiates the on-V jet identity; slow action arbitrary. |
| `complexFrequency_real` | `complexFrequency_realSlice` (KAMInputsFreq:116) | PASS | Same mathematical signed bridge; mu,J made implicit and export renamed; no added premise. |
| `kh-h` | `kamH_eq_smul` (KAMInputsKamH:28) | PASS | Global scalar identity, including points outside analytic domain. |
| `kh-h helper` | `two_pi_ne_zero_complex` (KAMInputsKamH:33) | PASS | Unconditional complex nonzero scalar; no root shadow. |
| `kh-h` | `fderiv_kamH` (KAMInputsKamH:36) | PASS | Global fderiv scalar law uses invertible scalar, valid even at nondifferentiable points. |
| `kh-h` | `freq_kamH` (KAMInputsKamH:42) | PASS | Actual NormalForm.freq is complexFrequency/(2*pi). |
| `dictionary frequency` | `realFreq_kamH` (KAMInputsKamH:47) | PASS | Real-frequency identity on V with exactly one division by 2*pi. |
| `kh-dom / kh-norm` | `kh_dyn` (KAMInputsKamH:58) | PASS | Only the required dynamic consequences of proved rstar. |
| `source parameter` | `mu_mem_Icc` (KAMInputsKamH:69) | PASS | Admissibility implies the original closed mu interval. |
| `kh-dom helper` | `norm_blockFast_sub_le_real` (KAMInputsKamH:72) | PASS | Coordinate projection contracts the existing Pi max norm. |
| `kh-dom` | `actionNbhd_sub_analytic` (KAMInputsKamH:77) | PASS | Whole complex action neighbourhood maps into analyticDomain; slow norm strictly below one. |
| `kh-dom helper` | `analytic_mem_half` (KAMInputsKamH:112) | PASS | Analytic radius implies the half extension neighbourhood. |
| `kh-dom / kh-h` | `kamH_differentiableOn` (KAMInputsKamH:116) | PASS | Actual complex integrable derivative, source mu interval and proved inclusion. |
| `kh-h` | `kamH_injOn` (KAMInputsKamH:125) | PASS | Restricts proved freq_inj; invertible scalar preserves injectivity. |
| `kh-h helper` | `pgCU_pos` (KAMInputsKamH:139) | PASS | Positive from the data-only analytic bounds. |
| `kh-h` | `kamH_hessian` (KAMInputsKamH:144) | PASS | Constructs rescaled continuous linear equivalence; bounds forward/inverse and slow/fast rows. |
| `periodicity helper` | `kh_single_castAdd_natAdd` (KAMInputsPer:29) | PASS | Fast unit vector vanishes on slow coordinates. |
| `periodicity helper` | `kh_single_natAdd_castAdd` (KAMInputsPer:37) | PASS | Slow unit vector vanishes on fast coordinates. |
| `periodicity helper` | `kh_single_natAdd_natAdd` (KAMInputsPer:45) | PASS | Slow unit-vector restriction is the original slow unit vector. |
| `periodicity helper` | `kh_single_castAdd_castAdd` (KAMInputsPer:58) | PASS | Fast unit-vector restriction is the original fast unit vector. |
| `kh-dom / periodicity` | `kamPolarPt_add_slow` (KAMInputsPer:70) | PASS | Slow angle unit shift is exactly a full trig period. |
| `kh-dom / periodicity` | `kamPolarPt_add_fast` (KAMInputsPer:95) | PASS | Fast angle unit shift becomes the frozen 2*pi fastShift. |
| `kh-dom / kh-f` | `kamF_periodic` (KAMInputsPer:114) | PASS | All a+b angles; uses averaging equivariance and extension periodicity. |
| `reality helper` | `jetPolynomial_realSlice` (KAMInputsPer:147) | PASS | Actual original secular polynomial only on V; no exterior source equality. |
| `kh-dom / reality` | `kh_real_fast` (KAMInputsPer:158) | PASS | The real rho-neighbourhood remains in V by innerCore and rho < sqrt r. |
| `kh-dom / reality` | `kamH_real` (KAMInputsPer:173) | PASS | Exhibits the real value using H0 and on-V jet identities. |
| `kh-dom / reality` | `kamF_real` (KAMInputsPer:188) | PASS | Uses polar real bridge, selected map real trace and ext_P_real on its proper domain. |

## Definitions and premise classification

| Definition | Whole-carrier classification | Verdict |
|---|---|---|
| `kamH` | Literal total complex integrable Hamiltonian divided by nonzero 2*pi. No analytic property asserted off its domain. | PASS |
| `kamF` | Literal total selected averaging map composed with the signed polar formula, extension Hamiltonian divided by 2*pi, minus kamH. Its analytic/real estimates have explicit domains. | PASS |
| `pgKamScale` | Literal ScaleData formula, initialL retained; total real division outside positive mu is inherited Lean arithmetic, not used as a positive-parameter theorem. | PASS |
| `kamPolarPt` | Literal total oscillatorPolarComplex after angle scaling; principal complex cpow is the signed polar object's value on the full carrier. Holomorphy asserted only on the proved positive-real-action domain. | PASS |

No new abbrev, structure, instance, fallback branch or invented characterization. Bodies
are explicit formulas, so uniqueness/choice independence is not a missing obligation.
The upstream pgAvg is a chosen witness of proved pg_avg; `kh_avg_spec` certifies that
same witness, not an assumed averaging conclusion. No new choice is introduced here.

For the three signed theorems: dimensions are TYPING; PGData carries the literal frozen
SOURCE inputs; r and mu are TYPING; admissible is the explicit STANDING small-parameter
range derived from the chosen data-only threshold. There are no EXCESS premises.
Other helpers expose local membership, differentiability or local-equality premises
suited to their helper claims and discharge them before the signed exports. In particular
the generic derivative-restriction helper's eventual equality is not a hypothesis of a
source theorem. No KAM conclusion, inverse bound, uniform remainder, frequency
injectivity or chart result is accepted as an extra provider/source premise.

## Independent hygiene and validation

All audit Lean/Lake commands run sequentially with `LEAN_NUM_THREADS=1` and niceness 5.
Only the named target is built, through the supplied compile gate; no clean/update/cache
operation or dependency edit is performed. Lake's reported job count is not a clean build.
Provider/frozen-type and seal-body probes are N/A: this scoped package has neither a
provider export nor a proposed frozen seal. No frozen theorem is imported into the probe.

1. Targeted build:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p5kh KAM.Planetary.PGAssembly.KAMInputs
   ```

   Exit 0. Exact gate/completion lines:

   ```text
   [inp-gate] slot 2 acquired 19:08:14 for KAM.Planetary.PGAssembly.KAMInputs
   Build completed successfully (9305 jobs).
   ```

   The intervening output replays dependency warnings and nonfatal linter suggestions.
   Within scope: KAMInputsKamH:38,173 suggest tactic simplifications; :164 has an unused
   simp argument. KAMInputsF:44 has an unnecessary simp sequence; :53–54,66–67 have
   unused simp arguments; :131 reports that h is not explicitly referenced. No error or
   heartbeat failure. Complete transient build output was captured in `/tmp/p5kh-build.log`.

2. Fresh exact-signature, definition-body and bridge probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P5KHAudit1.lean
   ```

   Exit 0. Three copied signed definitions were checked both by `type_of% @name`
   and `rfl` equality with their copied formula. Three signed theorem conclusions were
   repeated literally under anonymous names, using `@name a b d r mu h` as proof.
   The copied explicit design frequency-bridge telescope used
   `@complexFrequency_realSlice a b d mu hmu J hJ`. No draft signature file was imported,
   and the probe contained no sorry. All passed at default heartbeat settings.
   Exact complete axiom output for all 63 exports:

   ```text
   'KAM.Planetary.kh_mem_dom' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kh_realNbhd_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kamF_inClass' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kam_hyp' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.pg_kam_hyp' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.pg_kam_dictionary' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kamH' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.pgKamScale' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.mu_lt_one_of_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.pgKamScale_L' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.pgKamScale_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.pgKamScale_rhoHat' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.pgKamScale_eHat' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kamF' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kamPolarPt' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kh_avg_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kh_cpow_half_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kh_norm_cos_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kh_norm_sin_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kh_exp_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.pgWidth_lt_half' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kamPolarPt_fst_fast' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kamPolarPt_fst_slow' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kamPolarPt_snd_fast' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kamPolarPt_snd_slow' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kh_slow_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kh_fast_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kamPolar_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kh_ext_fast_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kamF_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kamF_sup' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kamPolarPt_differentiableAt' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kamF_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.fderiv_complex_realSlice' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.realInclusion_mem_actionNbhd' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.complexFast_realSlice' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.jpGrad_realSlice' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.complexFrequency_realSlice' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kamH_eq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.two_pi_ne_zero_complex' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.fderiv_kamH' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.freq_kamH' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.realFreq_kamH' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kh_dyn' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.mu_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.norm_blockFast_sub_le_real' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.actionNbhd_sub_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.analytic_mem_half' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kamH_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kamH_injOn' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.pgCU_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kamH_hessian' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kh_single_castAdd_natAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kh_single_natAdd_castAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kh_single_natAdd_natAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kh_single_castAdd_castAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kamPolarPt_add_slow' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kamPolarPt_add_fast' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kamF_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.jetPolynomial_realSlice' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kh_real_fast' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kamH_real' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.kamF_real' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   Thus all 59 new public theorems, and the four definitions, use only the allowlist;
   no sorryAx, project axiom or unclosed frozen theorem is inherited.

## Static checks and file integrity

Recursive production import inspection found 259 project modules, including 52 frozen
modules: all 52 are manifest-SEALED **definitions**. There are zero provider imports and
zero frozen theorem imports. The DRAFT_SORRY P-G anchor is outside this dependency
closure. The axiom output independently confirms there is no inherited sorry proof.

A project-wide declaration scan found no reused short name for any of the 63 new
public declarations. All declarations remain in KAM.Planetary; no new root declaration,
namespace alias, global instance or harmful shadow was introduced. In particular
`KAM.NormalForm.freq` is explicit where the derivative-based frequency is meant, and
`KAM.Planetary.freq` is the original real formula where the dictionary requires it.
All six files contain the copyright, module command, public imports, module docstring
and exposed public noncomputable section. No banned token or option was found, including
EuclideanSpace and heartbeat/recursion/synthesis overrides. File metrics count Unicode
characters consistently with lint:

| File | Lines | Maximum line width | SHA256 |
|---|---:|---:|---|
| `KAMInputs.lean` | 208 | 98 | `363b138001cf4c933afae9cbe6a4a714f7adb527c86324298da531a1dece33e3` |
| `KAMInputsBase.lean` | 113 | 99 | `dbe5f777f8be7ff463a779fde07b017ea68dbfaf72e65610a9b9e50dd9ccfdd3` |
| `KAMInputsF.lean` | 362 | 100 | `a8a61a7b50dfb31923f90571697f971c10f2b1658997e1afa552f098eecb4f86` |
| `KAMInputsFreq.lean` | 145 | 98 | `54bc6f0943f4c28aa2f7bdbb53b83e3f7a84dec0c9efb00de891f1683fc03553` |
| `KAMInputsKamH.lean` | 221 | 100 | `aea33dbe6c64269414f8fdd24a14c64f2f15939e297a69abb9b7a4e14679dd66` |
| `KAMInputsPer.lean` | 268 | 98 | `45567930199038d48ea0b20ddd7edaf5c82daf4d8d37ec5459089034302eae94` |

Both `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` and
`git diff --check` produced no output and exited 0. The generated files and protected
paths remain untouched. Every file is below 1500 lines and every line is at most 100
Unicode characters. The public import facade preserves the signed package import path.

## Kernel replay and repository lint

Kernel replay, one invocation for all six scoped modules:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.KAMInputs KAM.Planetary.PGAssembly.KAMInputsBase KAM.Planetary.PGAssembly.KAMInputsFreq KAM.Planetary.PGAssembly.KAMInputsKamH KAM.Planetary.PGAssembly.KAMInputsF KAM.Planetary.PGAssembly.KAMInputsPer
```

Exit 0. Exact output:

```text
replaying KAM.Planetary.PGAssembly.KAMInputsPer
replaying KAM.Planetary.PGAssembly.KAMInputsF
replaying KAM.Planetary.PGAssembly.KAMInputsKamH
replaying KAM.Planetary.PGAssembly.KAMInputsFreq
replaying KAM.Planetary.PGAssembly.KAMInputsBase
replaying KAM.Planetary.PGAssembly.KAMInputs
```

Repository lint, after kernel replay completed:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the explicitly permitted stale generated-root discrepancy. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (838 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The lint's ABI subprocess inherited LEAN_NUM_THREADS=1 and niceness 5. It ran after
all other audit Lean commands, not alongside them. No generated root was regenerated.

## Findings, uncertainties, errata and closeout

No blocking finding or new suspected pinned-source, blueprint or frozen-statement defect
was found in this slice. The inherited Revision-4 correction to extension agreement is
recorded in the design and respected by these proofs; its known blueprint gloss is not
silently used to assert original-source agreement outside the closed cylinder. This audit
compares the local authoritative blueprint and signed package contracts; it does not
re-adjudicate the underlying pinned papers or validate unrelated package proofs.

The full-strip question is resolved by the open-strip argument and the actual weighted
conversion API. The real-frequency bridge is fully established on its intended on-V
carrier. The six signed package exports are verified; there is no unsigned weakened
substitute for an assigned graph node. The submodule split retains the facade import
path; the bridge's fresh export name and implicit mu/J binders are the documented
presentation deviation. No mathematical deviation or extra premise was introduced.
The build's nonfatal linter suggestions and permitted generated-root discrepancy are
recorded above. These notes explain PASS WITH NOTES rather than an unqualified PASS.

Provider seal readiness is not applicable to P5-KH. The remaining campaign obligation is
still the complete frozen P-G theorem, not a type probe or a compiled KamHyp record.
No frozen anchor is sealed by this report, and no inference of P-PLANAR/P-FIXED closure
is made.

The audit probe `.lake/abi-scratch/P5KHAudit1.lean` was deleted after checks. The only
persistent repository file written by this audit is this report at the exact requested
absolute path. Final source/signature hashes, 63 declaration rows, balanced code fences,
report whitespace, protected-path diff and `git diff --check` were verified. Final status
contains only this report and the pre-existing untracked handoff; there is no tracked
worktree modification. No state-changing git command was run.
