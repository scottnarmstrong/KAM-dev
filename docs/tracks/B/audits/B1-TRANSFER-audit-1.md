# B1-TRANSFER independent package audit 1

**Overall: PASS WITH NOTES.** Both ordinary implementation modules pass statement fidelity, proof inspection, exact-signature elaboration, consumer-interface probes, axiom checks and kernel replay. No blocking proof defect found. Note N1 concerns an existing false documentation claim in OD-B2; N2 records the generated-root lint exception. This is readiness of the assigned helper package for integration, not a seal or a proof of either confinement headline.

## Scope and identity

- Worktree and report destination: `/root/code/KAM-inp-b1xfer`; branch `inp-b1xfer`.
- Audited HEAD: `73d930baa3b2cbfacb29cf8d9db6e88deee52897`.
- Compared branch `inp`: `98ebd477197dcb292eb2938ec3c3aa669f444ae4`; comparison: `git diff inp...HEAD`.
- New Lean files: `KAM/EffectiveStability/Transfer.lean` (147 lines) and `KAM/EffectiveStability/ActionDerivative.lean` (139 lines). Their working bytes agree with HEAD throughout this audit.
- SHA-256: Transfer `df43f2d8ed7ca94291666cccfe55e6ed965f5e312699e221215b9cfcf2740845`; ActionDerivative `73dc90c98528eac37c748d9c47af3965b6e7db06fbe0758839f2f622fd89703c`.
- Initial working-tree difference: `.drafts/handoff-B1-TRANSFER.md` was already modified (old chart-identity name corrected to the current name). Preserved unchanged by auditor. The controlling handoff is `docs/tracks/B/audits/B1-TRANSFER-handoff.md`.

Read AGENTS, PLAN, DECISIONS, the independent package brief, the handoff including AUDIT FOCUS, `/root/code/KAM-inp-b1/.drafts/B/brief-B1-common.md`, its B1-TRANSFER brief, SPEC, FREEZE-PROPOSAL, OWNER-DECISIONS, the local program-B plan §§2.2–2.4 and Brief 2, all three relevant frozen definition bodies, and the reused ODE regularity proof. The statement review named by the handoff is absent in this worktree; read `/root/code/KAM-inp-b1/docs/tracks/B/freeze/STATEMENT-REVIEW-1.md` as supplementary evidence. Proposal SHA-256 `a1d162988a5b03a0edbd87fc980b5ff3a9864a66e75e608f25fce9991e292d05` agrees with that review's proposal identity.

The generic I/N/P provider/seal and blueprint-node tests are specialized by AUDIT FOCUS: this is Track B, with **no frozen theorem, registered provider, or seal body** in this package. Provider-to-frozen type equality and seal-body elaboration are therefore **N/A**, not passed by analogy. Its specifications are the requested helper signatures and SPEC steps 2–3. No unrelated I/N/P theorem or blueprint node is claimed proved.

| Proposed consumer | Verdict for this package's contribution | Scope |
|---|---|---|
| B1-T `torus_confinement` | PASS WITH NOTES | Transport, regularity and angle-action cancellation supplied; whole headline not implemented here. |
| B1-E `oscillator_confinement` | PASS WITH NOTES | Transport, regularity, rotation cancellation and oscillator velocity supplied, including zero actions; whole headline not implemented here. |
| Internal B1-transfer corollary | PASS | Exact algebraic estimate supplied; trajectory/static-observable premises remain the caller's obligations. |

## Declaration-by-declaration fidelity

Names below are in `KAM.EffectiveStability`. All 12 public theorem types were inspected. The five Lean fences in the requested-signature brief were copied literally into a scratch probe, renamed, and proved by applying the corresponding export with all explicit binders in order. All five elaborated. Section-generalized `{n : ℕ}` (and `{m : ℕ}` for observable transfer) preserves the brief's parameter order and dependence. The remaining requested statements are specified in prose and match that prose; there is no literal Lean command for them to compare byte for byte.

| Node / brief item | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| Transfer 1, field identity | `symplecticForm_hamiltonianVectorField` (Transfer:53) | PASS | All H,z,v; precisely `ω(X_H z,v) = -dH(z)v`. No differentiability assumption needed for this algebraic identity of the frozen totalized derivative formula. |
| Transfer 1, nondegeneracy | `symplecticForm_nondegenerate` (Transfer:63) | PASS | Tests all phase vectors; concludes u=0, without a dimension restriction. Coordinate tests recover both components. |
| Transfer 2 | `bijective_of_symplectic` (Transfer:72) | PASS | Continuous real linear endomorphism of the same finite phase space; exact symplecticity implies injectivity, then finite-dimensional surjectivity. No surjectivity premise. |
| Transfer 3 / SPEC 2 | `fderiv_chart_apply_hamiltonianVectorField` (Transfer:84) | PASS | Exact fenced type; explicit order hH,hΨ,hsymp. Chain rule, symplecticity, surjectivity and nondegeneracy prove the entire vector equality. |
| Transfer 4 / SPEC 2 | `hasDerivAt_comp_chart` (Transfer:107) | PASS | Explicit order hc,hΨ,hH,hsymp; outputs the physical Hamiltonian derivative of Ψ∘c at t. |
| Transfer 5 | `contDiffOn_hamiltonianVectorField` (Transfer:119) | PASS | C² on open V gives C¹ field on V; hH then hV, as requested. Direct application of existing `KAM.ODE.ham_smooth_c1`. |
| Transfer 6 / plan B1-transfer | `observable_transfer_bound` (Transfer:125) | PASS | Exact fenced type, including A,L,d,η,t,x₀,x,J₀,J and explicit premise order. Constant 2 and sum `abs(L i j)*η j` preserved. No extra nonnegativity assumptions or wider constant dependence. |
| New supporting helper | `fderiv_eq_zero_of_const_curve` (ActionDerivative:35) | PASS | Differentiable G, curve derivative, base point, and local constancy give dG(v)=0 by uniqueness of derivatives. Distinct helper; its constancy premise is proved at both package consumers. |
| ActionDerivative 1 / SPEC 3 | `fderiv_angle_eq_of_eventuallyEq` (ActionDerivative:47) | PASS | Exact fenced type hK,hR,heq,j. Arbitrary N, local equality in nhds, full angle direction. |
| ActionDerivative 2 / SPEC 3 | `hamiltonianVectorField_snd_apply` (ActionDerivative:71) | PASS | Definitional negative angle derivative; no hidden regularity assumption. |
| ActionDerivative 3 / SPEC 3 | `bracket_action_eq_of_eventuallyEq` (ActionDerivative:76) | PASS | Exact fenced type and bracket `q_j d_p K - p_j d_q K`; arbitrary N, no positive-action premise. |
| ActionDerivative 4 / SPEC 3 | `hasDerivAt_oscillatorAction` (ActionDerivative:121) | PASS | Exact fenced type and p-before-q action API; only the displayed chart-curve ODE is assumed. |
| Private linear algebra support | `clm_fst_eq` (Transfer:34) | PASS | Expands a real continuous linear functional on (a,0) in the finite coordinate basis. |
| Private linear algebra support | `clm_snd_eq` (Transfer:43) | PASS | Corresponding expansion on (0,b). |

No extra premise, changed carrier, weakened conclusion, or hidden constant dependence was found. Public names do not duplicate one another. Repository/Mathlib namespace search found no other `KAM.EffectiveStability` namespace; successful module imports and probes found no qualified declaration collision. Private coordinate helpers do not clash with the similarly named private ODE helpers.

## Mathematical refutation and consumer applicability

**Transport and signs.** Frozen `hamiltonianVectorField` is `(d_p H,-d_q H)`; `symplecticForm v u` is `Σ(v_p u_q-v_q u_p)`. Expansion therefore gives **minus** dH, as used in Transfer:95–103. The proof uses the actual chain rule at a point where H and Ψ are differentiable. It never assumes the desired transport equality. Injectivity uses nondegeneracy, and finite dimension upgrades it to surjectivity before testing every physical vector. The curve theorem applies the ordinary derivative chain rule.

**No differentiation of N.** ActionDerivative:58–67 differentiates K−R and proves constancy on the angle line by the local decomposition. ActionDerivative:84–118 uses the exact Cartesian rotation
`q_j(θ)=q_j cos θ+p_j sin θ`, `p_j(θ)=−q_j sin θ+p_j cos θ`, with all other coordinates fixed. It proves equality of the **whole action vector**, pulls the local decomposition back along this continuous curve, and differentiates K−R. The tangent `(p_j e_j,−q_j e_j)` gives the negative of the printed bracket, and zero is unchanged by this sign reversal. The final velocity theorem independently computes `dI/dt=p_j p'_j+q_j q'_j=q_j d_p K−p_j d_q K`. No `fderiv N`, chain rule through N, square root, polar angle, division by action, or positivity premise occurs. At q_j=p_j=0 both tangent and bracket vanish; n=0 has no indexed obligation.

**Premise provenance.** Differentiability premises are local source regularity data. `heq` is the static normal-form identity, and hsymp the specified chart property. The helper's hconst is supplied by the above invariances. Observable transfer is explicitly an algebraic helper: hJ is input drift data for that helper, not a substitute assumption for either headline proof. The caller must establish drift by the action lemmas plus the separate stopped-drift/first-exit packages.

**Consumer probes.** A second scratch file proved two pointwise interfaces from open sets D,V, C² H on V, C² Ψ on D, `MapsTo Ψ D V`, differentiable R on D, the normal-form identity throughout D, and the chart ODE at c(t)∈D. It derives actual derivatives using openness, obtains the neighborhood identity from `D ∈ nhds (c t)`, then proves:

1. Physical curve transport and `HasDerivAt (fun s => (c s).2 j) (−dR(e_j,0)) t` for the torus decomposition (also using chart symplecticity).
2. `HasDerivAt (fun s => oscillatorAction (c s).2 (c s).1 j) (q_j d_p R−p_j d_q R) t` for the oscillator decomposition.

These match SPEC 2–3. Headline domains are open finite intersections of strict sublevels of continuous coordinate/action functions, so this open-domain interface applies there. Neither probe assumes differentiability of N. Their supplied chart ODE is precisely the output expected of the separate chart-flow package. This verifies local composition of the audited interfaces, not first exit, continuation, endpoint lifetime, uniqueness assembly or a complete B1-HEAD proof.

## Definitions and import classification

There is **no new `def`, `abbrev`, `structure`, instance, carrier or bundled assumption** in either module. Local `set` terms e,e₁,e₂,a,b,γ are explicit basis directions, scalar trigonometric functions and Cartesian curves, used only within proofs; none has fallback values or hidden premises.

| Reused frozen definition | Classification on its carrier |
|---|---|
| `KAM.hamiltonianVectorField` | SEALED; exact coordinate evaluations of the total real Fréchet derivative on phase space. At nondifferentiable points the frozen totalization is used only in algebraic/curve identities; analytic transport explicitly requires actual differentiability. |
| `KAM.symplecticForm` | SEALED; finite bilinear coordinate sum on all real phase vectors, with the prescribed sign. |
| `KAM.Planetary.oscillatorAction` | SEALED; polynomial `(p_j²+q_j²)/2` on the entire real Cartesian carrier, including zero. |

A recursive source import scan from both modules reached 24 project modules, all implementation/definition modules: **no provider or frozen theorem anchor** (SEALED or DRAFT_SORRY). Hence no assumed frozen theorem enters the package. The manifest states of the three meaning-carrying definitions above were checked directly. Standard-only axiom outputs additionally confirm that no `sorryAx` is inherited by any public result.

## Mechanical checks and exact receipts

All calls were serial. Every Lean/Lake invocation, including the ABI invocation inside lint, inherited this complete cap:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1
```

In the commands below `CAP` denotes exactly that prefix, not a shell command actually installed. Builds used the mandated compile gate (which additionally invokes `nice -n 5 lake build`); no whole-library or opt-in application build was requested. No limits were raised, and no cache clean/update/download or package edit occurred.

```text
CAP /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b1xfer KAM.EffectiveStability.Transfer
[inp-gate] slot 1 acquired 23:47:48 for KAM.EffectiveStability.Transfer
Build completed successfully (2756 jobs).
exit 0

CAP /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b1xfer KAM.EffectiveStability.ActionDerivative
[inp-gate] slot 1 acquired 23:48:12 for KAM.EffectiveStability.ActionDerivative
Build completed successfully (2757 jobs).
exit 0

CAP lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .lake/abi-scratch/B1TransferAudit.lean
exit 0; no errors or warnings; axiom output below

CAP lake env leanchecker --verbose KAM.EffectiveStability.Transfer KAM.EffectiveStability.ActionDerivative
replaying KAM.EffectiveStability.ActionDerivative
replaying KAM.EffectiveStability.Transfer
exit 0

CAP lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .lake/abi-scratch/B1TransferConsumer.lean
exit 0; empty output
```

The first version of the auditor's extra consumer probe exited 1 because `(hD.mem_nhds hw).mono` did not elaborate as field notation. Replacing that scratch-only expression with `Filter.mem_of_superset (hD.mem_nhds hw) ...` produced the successful run above; no package change was involved. No proof/design failure or heartbeat exception occurred.

Every public theorem was queried by `#print axioms KAM.EffectiveStability.<name>`; output, with line wraps normalized only:

```text
'KAM.EffectiveStability.symplecticForm_hamiltonianVectorField' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.symplecticForm_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.bijective_of_symplectic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.fderiv_chart_apply_hamiltonianVectorField' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.hasDerivAt_comp_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.contDiffOn_hamiltonianVectorField' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.observable_transfer_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.fderiv_eq_zero_of_const_curve' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.fderiv_angle_eq_of_eventuallyEq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.hamiltonianVectorField_snd_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.bracket_action_eq_of_eventuallyEq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.hasDerivAt_oscillatorAction' depends on axioms: [propext, Classical.choice, Quot.sound]
```

LINT_RECEIPT_PENDING

Other checks:

- `git diff --check inp...HEAD`: exit 0, empty output.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0, empty output. Extending the protected list to `KAM/Root` and `lakefile.lean` also gives empty output.
- Both files have the copyright comment, `module`, public imports, module docstring and `@[expose] public noncomputable section`; 147/139 lines, below the 1500 cap.
- Source inspection found no forbidden proof escape, resource override, `EuclideanSpace`, new global notation/abbreviation, provider import or root import.
- No repository edit was made by the auditor except this report. Scratch Lean probes were confined to this worktree's `.lake/abi-scratch/` and deleted after checking; build/lint/kernel outputs are artifacts under `.lake/`.

## Notes, suspected defects and deviations

**N1 — existing documentation defect, nonblocking.** `docs/tracks/B/OWNER-DECISIONS.md:10` says: “K = H ∘ Ψ is C² from H and Ψ, so N's and R's regularity follow on the chart domain.” Recovery of the dropped C² regularity is false: take n=1, Ψ=id, H=0, `N(J)=|J₀|^(3/2)` and `R(φ,J)=−|J₀|^(3/2)`. R is differentiable and angle-periodic, K is smooth, but N and R are not C² at J₀=0. This agrees with C1 in the independent statement review; the sentence remains in this worktree's audited documentation. The sound replacement explanation is that **K−R is differentiable and invariant along the relevant curves**, sufficient for cancellation. The two Lean modules implement exactly that argument. No premise or theorem change is needed; report this for the orchestrator's documentation/errata handling.

**N2 — generated-root integration.** The generic audit brief permits the stale `KAM.lean` diagnostic, and AGENTS prohibits editing generated roots. Record the lint receipt above and regenerate roots through the orchestrator's integration workflow; the auditor does not repair generated files.

No new suspected defect in a pinned mathematical source was exposed by these elementary identities. This audit reconstructs the local helper contract and the frozen formulas; it does not re-audit every CL20/GLS17 passage or certify a numerical remainder. The program plan's entire-remainder requirement remains intact. The rotation's orientation differs from one formulation in the statement review but produces the same zero bracket and is not a theorem deviation.

The ordinary-theorem status and weaker normal-part regularity are explicitly part of the controlling B briefs/overnight proposal; no frozen approval is inferred. No implementation deviation from the requested helper statements was introduced or detected. Outstanding work belongs to B1-CORE/B1-HEAD and any future authorized freeze/seal audit, outside this package's passing scope.
