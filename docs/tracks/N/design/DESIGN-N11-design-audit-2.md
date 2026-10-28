# DESIGN-N11 delta design audit 2

Overall verdict: **PASS**.

Revision 2 resolves audit-1 F1–F4. The changed signatures retain the blueprint premises and conclusions, and the new real-Hessian extraction bridge has an appropriate unconditional signature. No new design failure was found in the delta. This verdict approves the audited design interfaces, not their placeholder proofs. N11-G remains explicitly blocked pending the stated Part-8 interface reconciliation.

## Scope and immutable inputs

Date: 2026-10-28. Independent, refute-first delta audit under the external `inp-audit-design.md` brief and the already-read repository rules and manuscript-audit protocol. Re-read the audit brief, revised handoff, earlier findings and the relevant blueprint/packet contracts. AGENTS.md, PLAN.md and DECISIONS.md have no changes from the first-audit snapshot. No subagents or network sources were used.

| Input | Commit / SHA-256 |
|---|---|
| Revision 2 HEAD | `311c128a4268c3dbb09537c53fcf28bc9f8a7a77` |
| Compared first-audit design commit | `bd2159ab74084f46f51c200dec05af420901d4ce` |
| Revised design | `f0fd0d111b6abd5c335a5ea144135a07b28be326f3d699f3c2761c46ad097609` |
| Revised signatures, 845 lines | `23bd2cc2645243b3357acccda6e04ff69fad4d055963010025c582f3c886a0e4` |
| Audit-1 report | `7fa316de9f393f151c995fe5b6ee2fe56953f6a551821dd52acad1e91c56517d` |
| p11a | `dede87e5ec7b638136dff072abbf021b24ed4a4cedf6befae88eddf6e87d57b3` |
| p11b | `4005a51b99ed21cba7c6cbca27b8e70392f9d8d6c67d6b59fec9e25cac51232d` |
| p11c | `5d6fe7fc6b09459b6bf307596832695fcda1b62bf5292bd926d84bf216f7b7ea` |
| N DEPGRAPH | `941c8d1d4bb6c17e3369d57b86441798544e1dabc8a9af1735882f75aa8972d2` |
| Frozen partial-convex theorem | `e6bb9443a34096433a84e3450162ed032b07d934352c7ecaaa10eb7caf16b4a3` |

Appendix A equals the revised delivered signatures byte for byte. Mechanical comparison with the first-audit Appendix finds exactly five changed existing theorem declarations, one added theorem, one added structure and four added imports. The other 39 theorem declarations and all 76 existing definitions/structures/abbreviations are unchanged. There are now 45 theorem obligations and 77 literal object declarations. Source files, graph packets, repository rules and frozen/manifest files are unchanged by the revision. All first-audit source-level checks outside this delta are carried forward with these equality checks, rather than claimed as a new full proof audit.

A/B/C below denote p11a/p11b/p11c; S2 denotes the revised signatures at the hash above. All line references refer to this fixed revision.

## Disposition of every earlier finding and note

| Earlier item | Delta evidence and adversarial recheck | Disposition |
|---|---|---|
| F1 — Major, extra complex Hessian bound in energy | S2 L551–561 defines `RealFastConvex` with `hessian_real` over real I and real v only; `energy_free` L583–598 consumes it. This matches C L78–84 and packet `bpN:p11:energy-free`, which bounds the real Hessian on U. `FastConvex` retains the stronger complex hypothesis only where the source requires it. | CLOSED |
| F2 — Major, canonical inverse image | S2 L301–320 now includes `MapsTo Ψ U (Dom ... (R-ρ) (s-σ))` as well as the Φ inclusion. Both use the actual negative/positive-time `extFlow`. B L108–110 and packet `bpN:p11:canonical-map` require exactly these image clauses. No source premise changed. | CLOSED |
| F2 — Major, iterative map contract | S2 L366–409 exports holomorphy and the image inclusion on Dom(R−3ρ/2,s−3σ/2), integer-angle equivariance there and `extFlow ... (-1) (Φ z)=z` on Dom(R−2ρ,s−2σ). All previous estimates and residual witnesses remain. B L126–133 and the iterative packet match. | CLOSED |
| F2 — Major, periodic real field | S2 L436–447 now states periodicity of `realWfield ... (realHamiltonianExt ...)`, in addition to scalar-Hamiltonian periodicity. This supplies the hypothesis consumed by independent-transverse continuation. C L7–13 and the real-system packet match. | CLOSED |
| F3 — Medium, unnecessary reality premise and real-only gradient | S2 L520–527 uses `InClass` and exports both real and imaginary derivative vectors in `resSpan Λ`. This is the complexified projection assertion of C L12; no `extReal` premise remains. The real energy consumer takes the first conjunct. | CLOSED |
| F4 — Medium, wrong Mathlib namespace | Design Revision 2 and reuse/inventory entries use root `tendsto_exp_div_rpow_atTop` and root `tendsto_exp_mul_div_rpow_atTop`. No stale qualified `Real.tendsto_exp_div_rpow_atTop` remains in the design. Fresh gated API probes succeeded with the exact intended types. | CLOSED |
| N1 — Part-8 interface reconciliation | Design L155 and N11-G explicitly forbid dispatch until singleton radius bounds, K/sqrt(n) analytic divisors, strict resonance closeness and full-rank exclusion are supplied by actual owner signatures. No fabricated theorem replaces these inputs. | RETAINED AS DISPATCH GATE |
| N2 — imports and unequal-carrier derivative transport | SupWeighted, Algebra, Continuation and ExponentialBounds imports were added. The equal-size `hamiltonian_real_fderiv` is explicitly a proof pattern; N11-D owns the local unequal-carrier proof, without an equality hypothesis replacing a frozen field. Fresh gated API probes succeeded with the exact intended types. | RESOLVED AT DESIGN LEVEL |
| N3 — open ball and stale locator | C L31's radius-half ball is still interpreted as open at the endpoint width; the graph adjoint proof locator still overreaches B L73 into Taylor. Both are disclosed in the revised design and handoff, with no unauthorized source/graph change. | RETAINED NONBLOCKING NOTES |

The F1 recheck specifically tried to invalidate the repair by recovering a hidden complex bound through the new bundle or a consumer hypothesis: none is present in `RealFastConvex` or `energy_free`. The F2 recheck compared the exact domains, integer shifts and selected flow, rather than accepting weaker existence or injectivity statements. The F3 recheck considered imaginary-valued resonant Fourier functions; the revised premise and both conclusions apply. No earlier finding remains open as a design correction.

## Added bridge and affected consumers

The new theorem is:

```lean
theorem FastConvex.toRealFastConvex {Ic : Fin n → ℝ} {R m M : ℝ}
    {h : (Fin n → ℂ) → ℂ} (hh : FastConvex Ic R m M h) :
    RealFastConvex Ic R m M h := sorry
```

**PASS.** The only premise is the existing complex-bound convexity object. The common positivity, holomorphy, reality and lower-convexity fields are unchanged. At a real action with `‖I-Ic‖<R`, holomorphy and reality on the open tube identify the real Hessian of the actual frozen `realPart h` with the restriction of the complex Hessian. Applying the complex bound to the coordinatewise complex inclusion of a real v gives `hessian_real` with the same M and the same Euclidean norm. There is no dimension factor, enlarged constant or new frequency assumption. For R≤0 the new upper-bound obligation is vacuous, so omitting a positive-radius premise does not introduce a degenerate-radius defect.

The bridge belongs to N11-E3/Hessian, and N11-M2 now explicitly depends on E3. The resonant consumer restricts its fast convexity data to the normal-form radius and applies the bridge before `energy_free`. Energy itself depends only on the real bundle declared in Setting; its time `s*m*r/(20*M*zeta)`, drift r/4, strict initial margin, slow half-radius margin and frequency-free quantifiers are unchanged.

The normal-form consumers N11-K1/K2 can now consume the iterative map properties on every next domain: positive losses put Dom(R−2ρ,s−2σ) inside Dom(R−3ρ/2,s−3σ/2), and the exported image lies in the preceding domain. The canonical inverse inclusion uses the same U as its holomorphy clause. Transfer can now obtain field periodicity from `real_system` before invoking the independent-transverse continuation theorem; regrouping the real transverse coordinates remains part of the assigned implementation.

No direct Part-11 consumers were found in the I/P blueprints or N Part 12. Their shared Part-3 ODE uses are unchanged. The revision does not substitute extended predicates for Newton/restricted solution predicates. N Part 7 remains an upstream proof pattern, with its equal-size energy/no-exit theorem still excluded from direct application to the extended slow-dependent system.

## Theorem-signature ledger

PASS denotes design/source correspondence, not proved Lean code. Unqualified names are in `KAM.Nekhoroshev`; provider qualification is explicit. Unchanged rows carry forward audit 1 after exact declaration comparison.

| Lean name (S2 line) | Blueprint label (`bpN:p11:` unless stated) | Verdict | Reason |
|---|---|---|---|
| `orbit` (110) | `orbit` | PASS | Unchanged; Exact frozen field; period conversion preserves actions, slow coordinates and time. |
| `exponents` (115) | `exponents` | PASS | Unchanged; Omitted positive comparison consequences follow arithmetically from displayed inequalities. |
| `ext_part4` (174) | `ext-part4` | PASS | Unchanged; Sup bound wrapper; other Part-4 statements are explicitly reused at independent base dimension. |
| `bracket` (178) | `bracket` | PASS | Unchanged; Fast and slow constants and domain losses match. |
| `bracket_dominated` (188) | `bracket` | PASS | Unchanged; Nonnegative c and SL give the stated half-sum bound. |
| `bracket_g` (194) | `bracket-g` | PASS | Unchanged; Literal finite decomposition and source weights. |
| `vf` (205) | `vf` | PASS | Unchanged; Scaled field and slow component bounds; SL and k positivity retained. |
| `flow` (213) | `flow` | PASS | Unchanged; Partial wrapper; generic flow_a–d are explicitly direct imports, reality has its own wrapper. |
| `symplectic` (225) | `symplectic` | PASS | Unchanged; Functional canonical identity; form, determinant and bracket exports below supply companion clauses. |
| `adjoint` (231) | `adjoint` | PASS | Unchanged; Factorial-normalized bound has e squared times eta over eight. |
| `ext_taylor` (240) | `ext-taylor` | PASS | Unchanged; Correct recursive bracket orientation and integral kernel. |
| `composition` (264) | `composition` | PASS | Unchanged; Maps, all-time norm bound, pointwise HasSum and uniform weighted convergence. |
| `transform` (277) | `transform` | PASS | Unchanged; Integral remainder, sign and bound match. |
| `transform_integral` (291) | `transform` | PASS | Unchanged; Joint function and derivative continuity retained. |
| `canonical_map` (301) | `canonical-map` | PASS | F2 closed: both forward and inverse map U into the required loss domain. |
| `hom` (324) | `hom` | PASS | Unchanged; Independent base dimension, divisor alpha/q, sign and real-frequency guard match. |
| `iterative` (366) | `iterative` | PASS | F2 closed: holomorphy, map domain, integer equivariance and actual flow left inverse exported. |
| `nf` (411) | `nf` | PASS | Unchanged complete target; repaired iterative exports now supply its map properties. |
| `real_system` (436) | `real-system` | PASS | F2 closed: periodicity of the real vector field is explicit. |
| `real_system_bounds` (449) | `real-system` | PASS | Unchanged; Correct fixed-base angular derivative sum and factor 1/(e s). |
| `conj` (472) | `conj` | PASS | Unchanged; Real restriction of the actual complex map and exact orbit predicate. |
| `preimage` (476) | `preimage` | PASS | Unchanged; Source non-strict upper margins retained; positive block scales are typing data. |
| `continuation` (487) | `continuation` | PASS | Unchanged; Independent transverse dimension, compact tail and maximal solution match. |
| `real_system_resonant` (520) | `real-system` | PASS | F3 closed: no reality premise; both real and imaginary resonance-span conclusions. |
| `transfer_conditional` (530) | `transfer` | PASS | Unchanged; T3 is visibly conditional; arbitrary original extension, closed prefixes and infinite T retained. |
| `FastConvex.toRealFastConvex` (576) | `hessian / energy-free (new restriction bridge)` | PASS | New bridge: restrict the existing complex Hessian bound to the real slice, without extra premises. |
| `energy_free` (583) | `energy-free` | PASS | F1 closed: only the real Hessian bound is required; constants, slow margin and time unchanged. |
| `nonresonant` (598) | `nonresonant` | PASS | Unchanged; Exact stopped hypotheses, max norm, time constant 5 and radius half. |
| `resonant` (611) | `resonant` | PASS | Unchanged; Complex bound is a source premise here; p=9/8, time 240 and Euclidean drift match. |
| `hessian` (669) | `hessian` | PASS | Unchanged; Local signed consequences; frozen global hypotheses remain in PartialData. |
| `domain` (682) | `domain` | PASS | Unchanged; Complex domain inclusion and normalized weighted bound; other clauses are separate exports. |
| `block_data` (693) | `block-data` | PASS | Unchanged; Consumer-facing geometric consequences; lattice enumeration is intentionally upstream. |
| `domain_field` (710) | `domain` | PASS | Unchanged; Frozen Hamiltonian equals signed physical weighted field on the actual open set. |
| `block` (720) | `block` | PASS | Unchanged; Physical/scaled carriers separated; exact stopped prefix and drift. |
| `threshold` (737) | `constants / p0:partial` | PASS | Unchanged; Threshold precedes perturbation and orbit; six comparisons uniform in initial point. |
| `hessian_at_sign` (746) | `hessian` | PASS | Unchanged; Uses the selected frozen sign rather than choosing an incompatible second witness. |
| `flow_real` (752) | `flow` | PASS | Unchanged; Actual generic flow; real-locus tangent condition, no hidden domain symmetry assumption. |
| `ext_taylor_bound` (759) | `ext-taylor` | PASS | Unchanged; Uniform integrand bound avoids an unjustified maximum choice. |
| `symplectic_bracket` (767) | `symplectic` | PASS | Unchanged; Holomorphic observable invariance on explicit image domain. |
| `symplectic_det` (773) | `symplectic` | PASS | Unchanged; Nondegenerate weight and determinant plus/minus one. |
| `composition_domain` (779) | `composition` | PASS | Unchanged; Retains smaller image tube from clause (i). |
| `composition_real` (786) | `composition` | PASS | Unchanged; Stronger reality-only observable assumption suffices for the reality conclusion. |
| `ext_taylor_regular` (792) | `ext-taylor` | PASS | Unchanged; Within derivatives on [0,1] preserve endpoint interpretation. |
| `symplectic_form` (803) | `symplectic` | PASS | Unchanged; Inverse slow weight c inverse in the preserved form. |
| `KAM.Provider.Nekhoroshev.partialConvex_nekhoroshev` (812) | `p0:partial` | PASS | Unchanged; Provider command type byte-identical to the frozen theorem; all premises and quantifiers retained. |

## Object, frozen-object and package checks

| Changed or added object/interface | Verdict | Reason |
|---|---|---|
| `RealFastConvex` (S2 L551) | PASS | Literal real-slice Hessian assumptions of C L79; no energy or confinement conclusion in a field. |
| `FastConvex` | PASS | Body unchanged; complex upper bound retained for the resonant/domain source contracts. |
| Four added imports | PASS | Intended existing library interfaces; no provider or DRAFT_SORRY anchor imported. |
| Existing 76 object declarations | PASS, carried forward | No body/type changes; the first audit's object checks remain applicable. |

**Frozen objects: PASS.** The provider command type is still byte-identical to the actual frozen `partialConvex_nekhoroshev` declaration. The frozen theorem and source fingerprints are unchanged. Rechecked `realPart`, the differentiability guard and two-sided derivative in `IsSolutionOn`, and the global sign in `HasDefiniteFastPart`. The new real Hessian uses that actual `realPart`; no parallel frozen definition is presumed equal. Existing `orbit`, `domain_field`, `ExtOrbit` and the provider still connect to the actual frozen field, Hamiltonian and supplied stopped solution interval. No conclusion-shaped premise, upper frequency bound, whole-window slow confinement or changed constant-dependence order is introduced.

**Packages: PASS.** All revised package edges were checked. Moving both convexity bundles into Setting gives Energy access without a reverse Hessian/NormalForm dependency. Hessian owns the extraction theorem; Resonant imports it. CanonicalMap and Iterative export the additional map clauses at their existing positions in the DAG. The 23-package, ten-wave schedule stays acyclic; single-file estimates stay below 1500 lines (largest listed estimate 650). The signature file has 845 lines. N11-G's explicit Part-8 gate remains mandatory, and the twelve staging owner definitions must still be retired at integration. No global norm/typeclass instances or resource overrides were added.

## Verification

1. **Original revised signatures, copied and elaborated once.** Fresh copy `.drafts/scratch/N11Audit2Signatures.lean`, identical SHA-256 to the delivery, using the required command:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh \
     /root/code/KAM-inp-design-n11 .drafts/scratch/N11Audit2Signatures.lean
   ```

   **Exit 0; exactly 45 `declaration uses sorry` warnings, no other compiler diagnostics.** The gate reported slot 1 acquired at 05:49:00 UTC.

2. **API/bridge probe.** Temporary `.lake/abi-scratch/N11Audit2Probe.lean` imports the revised interface modules, reproduces only the two fast-convexity structures and new bridge target, and checks both root asymptotic lemmas, `Real.exp_one_lt_d9`, the three Weighted conversion/algebra exports, `gen_continuation` and the bridge type. **Exit 0; all eight `#check` commands succeeded.** The only warning is the deliberate bridge `sorry`.

3. **Source lint.** **Exit 0:** `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`; `ABI HASHES OK (144 frozen declarations)`. Lint used the pre-existing `.drafts/scratch/lint-bin/lake` wrapper so its ABI elaboration also passed through the prescribed gate. No targeted production module build is applicable: only Markdown is edited; the brief's signature elaboration check is the relevant Lean validation.

4. **Axioms.** The fresh bridge probe independently printed `[propext, sorryAx, Classical.choice, Quot.sound]` for `FastConvex.toRealFastConvex`. The revised designer inspection additionally lists nf, energy_free, transfer_conditional and the frozen-type provider draft as `[propext, sorryAx, Classical.choice, Quot.sound]`; that is a designer receipt, not an independently rerun proof check. Every theorem remains deliberately unproved.

5. **Artifact and hygiene checks.** `git diff --check` and `git diff --no-index --check /dev/null <audit-2-report>` passed. Working-tree status contains only the two untracked audit reports; audit 1 retains its recorded hash. All 122 packet nodes plus the root remain covered by the design inventory. The first audit report and original delivered signatures are preserved. Temporary auditor scratch copies/probes are removed after checking. No state-changing git, build-cache mutation, frozen/manifest edit or production Lean edit was performed.

Audit Lean commands are serialized: acquire both campaign compile slots and signature slots 2–3, then invoke the prescribed signature gate (which acquires slot 1). Its implementation sets `LEAN_NUM_THREADS=1` and runs `nice -n 5 lake env lean` against the shared `/root/code/KAM-inp` build. No heartbeat, recursion or synthesis limit is changed. Waits are gate waits. Other sessions' ungated actions are outside this audit's control.

## Remaining notes and closeout

- **N1 — Nonblocking for design approval; blocking for N11-G dispatch.** Reconcile the actual Part-8 signatures before dispatch, exactly as the revised design requires. No upstream proof or interface reconciliation is certified here.
- **N2 — Implementation obligation.** Prove the declared bridge and unequal-carrier real derivative transport; remove staging declarations when their owner modules land. Successful elaboration supplies no proof of these statements.
- **N3 — Reported source/graph issues retained.** Preserve the open-ball endpoint reading and report the adjoint locator correction to its owner. No new pinned-source erratum or source deviation was found.

All earlier findings are resolved at the design level; all delta declarations and touched consumer/package contracts are classified. No corrective signature block is needed because no signature fails this delta audit. Energy/transfer mathematics, finite-coordinate transports and eventual theorem bodies still require their planned independent proof audits. No frozen root is closed by this PASS.
