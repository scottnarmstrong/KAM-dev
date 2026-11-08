# B4-TORIGCHAIN independent package audit 1

**Verdict: PASS WITH NOTES** for `KAM.EffectiveStability.torusChain_physical` and the
B4-TORIGCHAIN package. No blocking mathematical or proof defect found. No frozen anchor
is assigned: this is ordinary Track B infrastructure, not a seal authorization.

## Scope and authority

Audit date: 2026-11-03. Worktree: `/root/code/KAM-inp-b4togchain`.
Audited HEAD: `34e6710d21631ec9e34612e71bba0b56044277c2`.
Comparison ref `inp`: `8c4ccc73102acb696ed39882984eb34cf037eebd`.
Merge base: `dfcfe1a17425f7c0a66cb73cb40715caa0d04e18`.
`git diff inp...HEAD` contains exactly:

- `KAM/EffectiveStability/TorusChainPhysical.lean` (181 lines);
- `KAM/EffectiveStability/TorusChainPhysicalSmoke.lean` (59 lines);
- `docs/tracks/B/audits/B4-TORIGCHAIN-handoff.md` (50 lines).

Both Lean files are byte-unchanged from producer commit `4b4cb5c91` through the inp-b1
merge `4063954bb` and audited HEAD. Read AGENTS, PLAN, DECISIONS, the named generic audit
brief, the handoff/AUDIT FOCUS, B4-TORIGCHAIN/B1-common/common-prover briefs, B SPEC,
OWNER-DECISIONS and FREEZE-PROPOSAL; compared TorusChain and TorusPhysical APIs and the
OscillatorChainPhysical template. The governing contract is the Track B package brief
and OD-B11, not an unrelated I/N/P anchor. Local DECISIONS ends at D70; D71 is the
packet's recorded overnight status, not an inferred exact-text freeze approval.

Also checked the local blueprint-N Part 5 setting/flow/inverse/transport statements
(`blueprint-N/parts/p5-canonical-maps.tex`) and program-b-plan §2.1–2.2, especially the
physical-box inclusion and `2d + Lη|t|` transfer at lines 143–155. The plan is absent
from this checkout and was read at `/root/code/KAM/docs/explorations/program-b-plan.md`;
the package brief itself supplies the exact deliverable. This is not a new paper/PDF audit.
There is no Track B `statement.md` or `blueprint-B` here; SPEC/FREEZE-PROPOSAL and the
package brief supply the relevant statement authority.

Provider/frozen type-equality and seal-body probes are **not applicable**: no provider
or frozen declaration is introduced. An independent application probe instead extracts
B1-T's solution/uniqueness conclusion from `Torus.lean`, specializes H to `ftEvalR H`
and V to `univ`, sets the initial value to physical `z₀`, and appends the two requested
physical bounds. Applying all 25 explicit main binders in order elaborates successfully.
The user's exact worktree report destination overrides the generic brief's destination.

## Notes

**N1 — documentation-only missing name.** `TorusChainPhysical.lean:19` advertises
“`tchChainMap_tchChainInv`: `Ψ (Ψinv z) = z`”. No declaration of that name exists.
The equality is actually the second conjunct of `tchChainInv_sub_le` (lines 83 and
108–111), and is used correctly by the main theorem. Update the introductory comment
or refer to that conjunct; no missing proof or requested theorem conclusion results.
This documentation defect is inherited in shape from the oscillator-chain template.

**N2 — smoke coverage.** `TorusChainPhysicalSmoke.lean:33–55` genuinely calls the main
theorem with two steps and discharges every hypothesis using kernel evaluation,
`norm_num`, or existing checked step data. Both generators and both ε are zero, and
`a' = 0`. Its exported statement retains `z 0 = z₀` and zero physical drift, but drops
ODE, lifetime and uniqueness. A constant curve would satisfy that exported statement.
It is the requested instantiation smoke, not an independent dynamics certificate or
a test of nonzero displacement/noncommuting charts. Consume the main theorem for dynamics.

**N3 — domain/certificate scope.** `TChPhysDom` is a finite real-inequality predicate,
independent in definition from `TChDomOK`; both are supplied to the main theorem.
It is not an executable certificate producer. No nonempty physical box is claimed
without an actual `z₀` satisfying `hz₀`. Real radii/boxes are allowed, as in the
underlying confinement theorem. No unquantified constant is added.

## Mathematical review

The main theorem's hypotheses through `hmargin` are exactly those of
`torusChain_confinement`. Chart initial data `w₀, hw₀` are replaced by physical data
`z₀, hz₀` and `a', hpa, hpd`. `hpa` is `a' + D ≤ a`, and `hpd` unfolds to finitely
many strict radius inequalities. Neither mentions a flow, trajectory, inverse identity,
remainder estimate or confinement conclusion. `TChStepOK` and `TChChainOK` are the
existing finite typing/majorant/Bool checks, not bundled analytic obligations.

For `s :: l`, Ψ = Φ_s ∘ Ψ_l and Ψinv = Ψinv_l ∘ Φ_s⁻¹. A symbolic two-step probe
checks both orders by `rfl`, with arbitrary distinct steps. The new budget processes
the outer step first for the inverse: before step k the action bound is q_i + c,
and the next accumulator is c + ε_k ρ'_k. The full gauge ball is in the open strip
because q_i + c + ρ'_k < ρ_k and σ'_k < σ_k. The proof explicitly obtains the full
real interior via `cylClosed_subset_realInterior_cstrip`, restricts to the half interior
for inverse displacement, and uses the full interior for Φ_s(Φ_s⁻¹ z) = z.
Induction supplies the next input bound by a triangle inequality. The inverse identity
is then proved by cancelling the inner chain first, followed by the outer step.
No totalized-flow fallback supplies a theorem step.

Forward displacement uses the inner chain's proved `chart_maps` into
`cyl (b + εb + tchTailJ l)`, then the matching outer real-domain inequality in
`TChDomOK`. It passes from full to half real interior before invoking the one-step
bound. Coordinate triangle inequalities sum the displacements in the same lifted
coordinates; no derivative/Lipschitz multiplier is required for this telescoping.
The gauge is `scaleCLE ρ' σ'`, with norm max(‖angle‖/σ', ‖action‖/ρ')
(`Canonical/Setting.lean:44–59`), so the tails are correctly Σ εσ' for angles and
Σ ερ' for actions, with no swapped scale or extra 2π.

In the main proof, w₀ := Ψinv z₀ satisfies |w₀.2_i| ≤ |z₀.2_i| + D ≤ a_i.
The preceding inverse result proves Ψ w₀ = z₀. Since η_i ≥ 0 and T ≥ 0,
`hmargin` and εb > 0 place w₀ inside the chart cylinder; membership is not assumed
as a premise. Applying the original chain confinement theorem and rewriting this
equality preserves the initial condition, Hamiltonian equation for the original
`ftEvalR H`, existence on Ioo(-T₁,T₁) with T₁ > T, and B1-T uniqueness on every
order-connected I containing zero. It does not claim uniqueness of total-function
values outside the solution interval.

For every |t| ≤ T, the original conclusion gives u := Ψinv(z t), Ψ u = z t,
|u.2_j − w₀.2_j| ≤ η_j|t| and |u.2_j| ≤ a_j + η_jT < b_j.
Thus u lies in `cyl (b + εb)` and forward displacement applies. The three action
differences z(t)−u(t), u(t)−w₀, and w₀−z₀ contribute respectively D, η_j|t|, and D.
This proves the requested physical drift 2D + η_j|t|. The level bound uses
|z(t).2_j| ≤ |u.2_j| + D ≤ a_j + η_jT + D. Both bounds include endpoints.

## Declaration inventory and definition classification

All names are in `KAM.EffectiveStability`. Every new public source declaration is listed.

| Node | Declaration | Verdict | Reason |
|---|---|---|---|
| Inverse radius budget | `TChPhysDom` | PASS | Recursive conjunction of finite strict inequalities; arbitrary starting c; empty chain True. |
| Forward chain displacement | `tchChainMap_sub_le` | PASS | Exact angle/action tails on the original cylinder; valid intermediate domains. |
| Inverse displacement and right inverse | `tchChainInv_sub_le` | PASS | Prefix radius budget, both coordinate bounds, and Ψ(Ψinv z)=z proved. |
| Physical initial box and dynamics | `torusChain_physical` | PASS WITH NOTES | Full requested initial value, ODE, lifetime, uniqueness and physical bounds; N1/N3. |
| Two-step instantiation | `tchChainPhysicalSmoke_zeroDrift` | PASS WITH NOTES | Actual checked main-theorem application; limited exported coverage N2. |

The sole new `def` is `TChPhysDom`; there is no new abbrev, structure, instance,
choose/default object or flow definition. Its body is the intended syntactic budget
on its whole carrier, including negative/unchecked data (which are still just finite
inequalities) and empty lists. It contains no hidden analytic field or junk branch.
Three private lemmas (`tchPhys_abs_sub_add_le`, `tchPhys_tailA`, `tchPhys_tailJ`) are
triangle arithmetic and cast/sum identities only, with no additional source premise.

## Independent checks

All Lean/Lake calls, including lint's ABI phase, ran serially from this worktree under:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 \
  nice -n 10 env LEAN_NUM_THREADS=1 <command>
```

Builds additionally use the compile gate's `nice -n 5 lake build`. No full library or
application build, clean, cache fetch, package update or resource override was used.

### Targeted builds

Each command below was run separately inside the wrapper above, in import order:

```sh
/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b4togchain KAM.EffectiveStability.TorusChainPhysical
/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b4togchain KAM.EffectiveStability.TorusChainPhysicalSmoke
```

Both exit 0, without warnings. Exact output:

```text
[inp-gate] slot 1 acquired 03:25:24 for KAM.EffectiveStability.TorusChainPhysical
Build completed successfully (3002 jobs).
[inp-gate] slot 1 acquired 03:25:37 for KAM.EffectiveStability.TorusChainPhysicalSmoke
Build completed successfully (3005 jobs).
```

### Axioms and conclusion/order/budget probe

Inside the same wrapper:

```sh
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .lake/abi-scratch/B4TOrigChainAudit1.lean
```

Exit 0. This prints axioms of all four new public theorems, checks symbolic two-step
map/inverse order, unfolds the two-step inverse budget, checks its empty case, and
elaborates the independently assembled physical dynamics conclusion described above.
Exact output:

```text
'KAM.EffectiveStability.tchChainMap_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchChainInv_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChain_physical' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchChainPhysicalSmoke_zeroDrift' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

One invocation inside the wrapper:

```sh
lake env leanchecker --verbose KAM.EffectiveStability.TorusChainPhysical KAM.EffectiveStability.TorusChainPhysicalSmoke
```

Exit 0. Exact output:

```text
replaying KAM.EffectiveStability.TorusChainPhysicalSmoke
replaying KAM.EffectiveStability.TorusChainPhysical
```

### Source hygiene, imports, protected paths and names

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-b4togchain KAM.EffectiveStability.TorusChainPhysical KAM.EffectiveStability.TorusChainPhysicalSmoke
```

Exit 0: `short-name check OK (no reused public short name)`. This is a static Python/git
check and does not launch Lean. Both new files have copyright, `module`, public imports,
module docstring and `@[expose] public noncomputable section`. Sizes are 181 and 59,
within the package's 600-line limit and hard 1500-line cap. A Python per-line Unicode
width check returned `overlong []` for each file (no exemptions). Forbidden-token and
`set_option` search returned `forbidden []` for each. Ambient coordinates remain
Fin n → ℝ / ℂ with Pi/product norms. Smoke uses `decide +kernel`, with no native escape.

A recursive static import scan of both modules found 93 KAM modules, including 20 frozen
definition modules, all matching SEALED manifest entries. No provider, frozen theorem
or DRAFT_SORRY import occurs. No application module is introduced by the package.

```sh
git diff --check inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md KAM/Root lakefile.lean
git diff 4b4cb5c91 HEAD -- KAM/EffectiveStability/TorusChainPhysical.lean KAM/EffectiveStability/TorusChainPhysicalSmoke.lean
```

All exit 0 with empty output. Full diff inventory also excludes generated application
roots and their parts. The producer's two files are unchanged by integration.

### Lint

Inside the same memory-capped wrapper:

```sh
sh scripts/lint_sources.sh
```

Exit **1**, solely for the generated-root staleness explicitly permitted by the audit
brief. Complete output, collected across the original invocation's output chunks:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean)
check_lean_modules: PASS (4544 Lean files, 0 comparator configurations)
.........................
----------------------------------------------------------------------
Ran 25 tests in 3.891s

OK
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (314 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

The original lint invocation completed; no rerun was needed. All other lint stages
passed. The stale generated part is `KAM/Root/EffectiveStability.lean`; it was left
untouched as required. The ABI receipt covers 314 core frozen declarations. The two
KAMLunarBand application anchors were checked by file hash only, as the output states;
this audit did not rebuild or certify that application's elaborated ABI.

## Errata, deviations and audit limits

No new suspected mathematical defect in a pinned source or blueprint was found in
this scope. N1 quotes the exact local documentation defect and its actual proof
location; no source statement or frozen definition was silently repaired. N2/N3 are
coverage/formulation notes, not unpaid analytic assumptions. This audit does not
re-audit every inherited normalization lemma or unrelated I/N/P headline.
No signature change, heartbeat failure, or auditor source-code deviation occurred.

| Audited Lean file | SHA-256 |
|---|---|
| `KAM/EffectiveStability/TorusChainPhysical.lean` | `c8e0c33de99f695f38b1bffa6f6c65ca367a4e7ba0d30f7771935de5f22f86bb` |
| `KAM/EffectiveStability/TorusChainPhysicalSmoke.lean` | `49034d5d60e762798e3c1eb64e8f1d9928b4d92eee73899748e9cf49264ba03a` |

The temporary `.lake/abi-scratch/B4TOrigChainAudit1.lean` probe was deleted after its
successful checks. Final `git status --short` shows only
`?? docs/tracks/B/audits/B4-TORIGCHAIN-audit-1.md`. This report is the sole retained
audit edit; no state-changing git command, source repair, freeze or seal was performed.

Final disposition: **PASS WITH NOTES**, retaining N1–N3 and the permitted generated-root
lint exception. No blocking finding remains in the assigned B4-TORIGCHAIN scope.
