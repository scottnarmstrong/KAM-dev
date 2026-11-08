# B4-TORIG independent package audit 1

**Verdict: PASS WITH NOTES for B4-TORIG.** All six public theorems meet the package brief. No mathematical, statement-fidelity, or proof-hygiene defect was found in the two assigned modules. Notes concern a redundant finite premise and the deliberately narrow smoke export.

There is **no assigned frozen anchor or provider**: Track B is ordinary infrastructure under D71 / OD-B11. Provider/frozen-type equality and a proposed frozen seal-body probe are not applicable. This report does not authorize a freeze or seal, and does not replace the separate B4-TSTEP audit.

## Snapshot, authority, and scope

- Worktree and report destination: `/root/code/KAM-inp-b4torig`; the user's exact destination overrides the generic brief's MAIN-worktree output instruction.
- Audited HEAD: `b539da6752364cf51819b09fad7186dae5176ce6`.
- `inp` at comparison: `8f9a0aea60b4c4d72761dae0528d80077897a6e0`; merge base: `1cacb4a4ea1abced3b3c7ac7ea4a2f58b71226ba`.
- Read and compared `git diff inp...HEAD` (8 files, 858 insertions). It contains the two TORIG files, four inherited TSTEP files, and both handoffs. The AUDIT FOCUS assigns commit `11f02053c543d85ee3a184b48ea7729103130387`, namely `TorusPhysical.lean` and `TorusPhysicalSmoke.lean`; these files are unchanged between that commit and HEAD. The TSTEP files were inspected as direct dependencies, not given a separate package verdict here.
- Authority read: AGENTS.md; docs/PLAN.md and docs/DECISIONS.md; `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`; B4-TORIG handoff and AUDIT FOCUS; B4-TORIG and B1-common briefs; B SPEC, FREEZE-PROPOSAL and OWNER-DECISIONS; `/root/code/KAM/docs/explorations/program-b-plan.md` §2.2 (lines 140–160), and D71 in that checkout's DECISIONS. D71 is absent from this worktree's older DECISIONS snapshot. No new ruling was inferred.
- The package brief and B plan/SPEC are the direct statement authority. `blueprint-N/parts/p5-canonical-maps.tex`, `bpN:p5:setting` and `bpN:p5:flow` (a), (c), (e), supply the reused norm, displacement, inverse and reality contracts. No I/N/P headline theorem is implemented by this package.

| File | Lines | SHA-256 |
|---|---:|---|
| `KAM/EffectiveStability/TorusPhysical.lean` | 195 | `c943a5d2e333bfaea863b6d2cdab4ca46b83660d2cf7479bee03036f650c4aa7` |
| `KAM/EffectiveStability/TorusPhysicalSmoke.lean` | 58 | `8297d2e8a4131d52523a0cb33256a1b2ed23aff9a94e7d925ae6b7f10d7b86f8` |

## Declaration-by-declaration review

All declarations are in `KAM.EffectiveStability`. Line references are to TorusPhysical unless explicitly marked Smoke.

| Node / brief item | Declaration | Verdict | Reason |
|---|---|---|---|
| Finite majorants / private helper | `torus_smallField` (30) | PASS | Derives positive λ from the strip inequality, then proves SmallField using `strip_le_log_lam` and `smallField_of_ftBounds`. No flow or confinement premise. |
| 1 / time-dependent displacement | `torusFlow_coord_sub_le` (48) | PASS | On half real interior, for every `t ∈ [-1,1]`, obtains both coordinate bounds with `abs t`; positive denominators are cleared in the correct order. |
| 1 / forward chart displacement | `torusChart_sub_le` (74) | PASS | Specializes time to +1, giving angle bound `ε*σ'` and action bound `ε*ρ'`. |
| 1 / inverse chart displacement | `torusChartInv_sub_le` (86) | PASS | Specializes time to −1 with the same bounds. |
| 1 / inverse identity | `torusChart_torusChartInv` (98) | PASS | Proves exactly `Ψ (Ψinv z) = z` on radius-one real interior; uses holomorphy, reality and the existing inverse-flow theorem. |
| 2 / physical initial box and physical drift | `torusStep_physical` (112) | PASS | Preserves all base finite premises, replaces chart initial datum by physical `z₀`, proves chart-box inclusion through Ψinv, retains B1-T lifetime/ODE/uniqueness, and gives both requested physical bounds. |
| 3 / integrable smoke | `torusPhysicalSmoke_zeroDrift` (Smoke:25) | PASS WITH NOTES | Actually instantiates the main theorem at `n=1`, `H=J₀²/2`, `χ=[]`, `P=[]`, `ε=η=0`, `L=T=1`. Kernel arithmetic discharges all finite checks. Export retains the physical initial condition and zero drift; see N2. |

## Proof and statement fidelity

**Premises.** A source comparison of the declaration prefixes, from the polynomial binders through `hmargin`, returned `base premise prefix identical: True`. Thus the physical theorem has exactly the premises of `torusStep_confinement` before its initial datum, followed by `a'`, `hpa`, `hpρ`, `z₀`, and `hz₀`. There is no assumed inverse inclusion, solution, drift, chart identity or continuation statement. SmallField in the displacement helpers is a legitimate standing analytic premise; the main theorem constructs it from finite derivative majorants. Its fields are openness, holomorphy, `0 ≤ ε ≤ 1/2`, and the field bound, with no hidden downstream result.

**Gauge and carriers.** The reused `scaleCLE ρ' σ'` has norm `max(‖angle‖/σ', ‖action‖/ρ')`, matching the blueprint. `norm_realFlow_sub_le` bounds this norm by `abs t * ε`. Clearing the positive widths and bounding each Pi coordinate gives precisely angle displacement `abs t * ε * σ'` and action displacement `abs t * ε * ρ'`. The frozen field is `(∂_J H, −∂_φ H)`; no sign or width exchange occurs. All real/complex phase carriers and Fourier indices retain the prescribed Fin-function conventions. No coefficient-radius reinterpretation or missing 2π conversion is introduced by the displacement step.

**Physical initial data (148–169).** `hz₀`, `hpρ`, and `σ'<σ` place `z₀` in radius-one real interior, hence in half interior. Set `w₀=Ψinv z₀`. The inverse theorem proves `Ψ w₀=z₀`; the inverse displacement bound and triangle inequality give

```
|w₀.2 j| ≤ |z₀.2 j| + |w₀.2 j − z₀.2 j|
           ≤ a' j + ε*ρ' ≤ a j.
```

The base confinement theorem therefore applies to `w₀`. Rewriting `Ψ w₀=z₀` gives the exact physical initial condition and the same physical initial condition in the uniqueness clause. This proves containment of the requested physical box, rather than merely defining a chart image.

**Physical bounds (170–191).** For every `abs t ≤ T`, the base theorem supplies `u=Ψinv(z t)`, `Ψ u=z t`, `|u.2 j−w₀.2 j|≤η j*abs t`, and `|u.2 j|≤a j+η j*T<b j`. The strict outer margin follows from `hdom1` and `εb>0`, so u is in the real interior required for forward displacement. Consequently

```
|(z t).2 j − z₀.2 j|
  ≤ |(z t).2 j − u.2 j| + |u.2 j − w₀.2 j| + |w₀.2 j − z₀.2 j|
  ≤ 2*(ε*ρ') + η j*abs t,
|(z t).2 j| ≤ a j + η j*T + ε*ρ'.
```

The two chart errors are each booked once. Endpoint times `±T` are included, with an ODE lifetime strictly larger than T. Uniqueness remains for every order-connected I containing zero and every physical solution of `ftEvalR H` in `univ`, on the interval intersection. It is not restricted to comparison curves already in the chart image. The case T=0 and the allowed zero generator/zero drift introduce no new premise or division by ε.

## Definitions, imports, and totality

The assigned two files introduce **no def, abbrev, structure, class, instance, or new carrier**. The local proof aliases w₀ and u are actual inverse-chart evaluations, not altered objects or hidden hypotheses.

The imported `torusChart` and `torusChartInv` are the real time +1 and −1 maps, respectively. The older chosen `flow` has a fallback to its starting point when no solution exists. No assigned proof uses that fallback: SmallField and half-interior membership invoke the existing existence, displacement and reality theorems; radius-one membership invokes the inverse theorem. Bounds are not asserted outside those certified domains. The imported smoke polynomial is exactly `[⟨[], [2], 0, 1/2, 0⟩]`, representing `J₀²/2` in dimension one.

A recursive source import scan found 84 KAM modules, **no provider imports and no frozen theorem imports**. Frozen imports are definitions only; the main real/complex Hamiltonian field and symplectic definitions were read. No DRAFT_SORRY theorem can supply a proof step here. Full axiom checks below independently exclude `sorryAx` in every new public result.

## Notes, source defects, and deviations

- **N1 — handoff documentation error, not a theorem defect.** `docs/tracks/B/audits/B4-TORIG-handoff.md:33` says hpρ is a separate check and includes “not in general; kept explicit”. Under the complete actual premises it is redundant: `0≤ε`, `ρ'>0` and hpa imply `a'≤a`; `T≥0`, `η≥0` and hmargin imply `a<b`; hdom1 and `εb>0` imply `b+ρ'<ρ`. Hence `a'+ρ'<ρ`. An independent Lean example proved this implication at default settings, without hpρ or the upper bound ε≤1/2. Keeping the explicit finite check is permitted by the brief and does not invalidate the theorem. Correct the handoff explanation when next maintaining it; no source was edited here.
- **N2 — smoke export scope.** `TorusPhysicalSmoke.lean:25–29` exports only existence of a curve with `z 0=z₀` and zero physical drift for zero initial action. It discards the ODE, lifetime and uniqueness clauses, so its statement alone is not an independent dynamics certificate (a constant curve satisfies it). Its proof genuinely calls `torusStep_physical` and discharges all premises; this passes the requested χ=0 smoke. Use the main theorem when consuming the dynamics.
- No suspected defect was found in the reviewed blueprint gauge/flow statements or the local plan's inverse-box/observable-transfer claim. This is not a new audit of GLS17's printed source or of the entire inherited TSTEP normalization proof.
- No implementation deviation, signature change, heartbeat failure, or resource override was introduced by the auditor. Only this report was added; temporary audit files are removed after verification.

## Independent checks

All commands ran from `/root/code/KAM-inp-b4torig`. Every Lean/Lake invocation, including lint's internal ABI check, was wrapped in this prefix:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1
```

Checks consuming Lean ran serially. Targeted builds used the requested compile gate (which additionally invokes `nice -n 5 lake build`). Existing build artifacts were reused; no clean, cache fetch, package update, or full-library rebuild was run.

### Targeted builds

Prefix above followed by, one call at a time:

```sh
/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b4torig KAM.EffectiveStability.TorusPhysical
/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b4torig KAM.EffectiveStability.TorusPhysicalSmoke
```

Both exited 0, no warnings:

```text
[inp-gate] slot 1 acquired 02:50:24 for KAM.EffectiveStability.TorusPhysical
Build completed successfully (2994 jobs).
[inp-gate] slot 1 acquired 02:50:55 for KAM.EffectiveStability.TorusPhysicalSmoke
Build completed successfully (2996 jobs).
```

### Axioms and finite-premise probe

Prefix above followed by:

```sh
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .lake/abi-scratch/B4TORIGAudit.lean
```

Exit 0. The scratch imported TorusPhysicalSmoke, printed axioms of every new public theorem, and proved N1's scalar implication. Exact axiom output:

```text
'KAM.EffectiveStability.torusFlow_coord_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChart_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChartInv_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChart_torusChartInv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusStep_physical' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusPhysicalSmoke_zeroDrift' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

Prefix above followed by one invocation with both assigned module names:

```sh
lake env leanchecker --verbose KAM.EffectiveStability.TorusPhysical KAM.EffectiveStability.TorusPhysicalSmoke
```

Exit 0; exact output:

```text
replaying KAM.EffectiveStability.TorusPhysicalSmoke
replaying KAM.EffectiveStability.TorusPhysical
```

### Source hygiene and names

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-b4torig KAM.EffectiveStability.TorusPhysical KAM.EffectiveStability.TorusPhysicalSmoke
```

Exit 0:

```text
short-name check OK (no reused public short name)
```

Static inspection/script: each assigned file has copyright, `module`, public interface imports, module docstring and `@[expose] public noncomputable section`. Lengths are 195/58, below both the package's 600-line bound and the hard 1500-line cap. Over-100-character lines: `[]` for each file. Forbidden proof escape, forbidden ambient type, and resource-override matches: `[]` for each file. `decide +kernel` in the smoke stays kernel checked.

```sh
git diff --check inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

Both exit 0 with empty output. The full path list also shows no generated root parts, application roots or lakefile changes. No production code or git state was changed by the audit.

### Lint

Prefix above followed by:

```sh
sh scripts/lint_sources.sh
```

Exit **1**, solely for the generic brief's explicitly permitted stale generated-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean)
check_lean_modules: PASS (4535 Lean files, 0 comparator configurations)
.........................
----------------------------------------------------------------------
Ran 25 tests in 4.060s

OK
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (314 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

All other lint stages pass. The stale item is `KAM/Root/EffectiveStability.lean`, reported by the generator as “KAM.lean is out of date”. Generated files were left untouched as required. ABI checking covers 314 core frozen declarations; the two band application anchors are file-hash-only as the lint output states, not rebuilt by this audit.

Final disposition: no blocking finding for B4-TORIG; retain N1/N2 and the separate upstream B4-TSTEP audit boundary. No frozen statement or pinned source was silently repaired.

