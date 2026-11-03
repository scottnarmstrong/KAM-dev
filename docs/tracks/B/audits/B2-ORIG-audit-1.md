# B2-ORIG independent package audit 1

Verdict: **PASS WITH NOTES** for B2-ORIG / `oscillatorStep_physical`.
No blocking mathematical, premise-fidelity, carrier, or proof-hygiene defect found.
This is an ordinary Track B theorem package under OD-B7, **not a frozen-anchor seal**.
There is no B2-ORIG provider or frozen theorem, so provider/frozen type equality and
seal-body probes are not applicable; this audit does not authorize a new freeze.

## Scope and controlling text

Audited worktree `/root/code/KAM-inp-b2orig`, HEAD
`5343103aaa00b28998e76f3751335e9ece27b52f`, compared with `inp`
`597ea6fd20832ed0816072ffa5d4af9681d78546` using `git diff inp...HEAD`.
The implementation commit is `a8599414c0c0440206bfdfacdff0cbc9def46b13`;
HEAD includes merge `6b129fa83` of inp-b1. The diff contains precisely the two
new Lean files, the handoff, and inherited B2-MULTI bookkeeping in PROGRESS.md
and packages.json. No B2-MULTI Lean implementation is newly changed in this diff.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the requested package-audit
brief, B2-ORIG-handoff.md including AUDIT FOCUS, brief-B2-ORIG.md and
brief-B1-common.md in `/root/code/KAM-inp-b1/.drafts/B/`, Track B SPEC,
FREEZE-PROPOSAL and OWNER-DECISIONS. The applicable source contract is the
original-box requirement and B1-transfer in
`/root/code/KAM/docs/explorations/program-b-plan.md:140–160`, together with
the exact B2-ORIG brief and B2-STEP interface. I/N/P frozen theorem lists are
generic instructions, not the anchors of this Track B package. No blueprint-B
exists; no unrelated I/N/P theorem is being certified here.

Inspected the inherited real-flow displacement and inverse interfaces, scalar
gauge and polydisc domain bridges, and the frozen definitions
`KAM.Planetary.oscillatorAction` and `KAM.hamiltonianVectorField`.
An import traversal reaches 75 KAM modules, no provider and no frozen theorem
anchor (hence no DRAFT_SORRY theorem). Imports of frozen definitions are allowed.

## Declaration-by-declaration review

All names below are in `KAM.EffectiveStability`. Locations are in
`KAM/EffectiveStability/`, relative to the audited HEAD.

| Node / location | Declaration | Verdict | Reason |
|---|---|---|---|
| B2-ORIG displacement, OscillatorPhysical:30 | `realFlow_coord_sub_le` | PASS | Actual real flow, every coordinate, both q and p, all t in [-1,1]; bound is exactly abs(t) ε δ. |
| Chart displacement, :58 | `stepChart_sub_le` | PASS | Time 1 specialization, certified realInterior 1. |
| Inverse displacement, :72 | `stepChartInv_sub_le` | PASS | Time -1 specialization on the same domain, no assumed image membership. |
| Right inverse, :87 | `stepChart_stepChartInv` | PASS | Derives Ψ(Ψinv z)=z from the inherited real inverse theorem under finite small-field checks. |
| Action perturbation, :100 | `oscillatorAction_sub_le` | PASS | Sharp asymmetric bound e(s+s′); equal radii give the requested 2es form. No unproved sign assumption. |
| Coordinate bridge, :120 | `coord_abs_le_of_action_le` (private) | PASS | From A(w)≤c, 2c≤r² and r≥0, proves both coordinate bounds using nonnegative squares. |
| Physical confinement, :131 | `oscillatorStep_physical` | PASS | Exact B2-STEP shared premise prefix, explicit hs0–hs3 and hd only, physical initial point and physical drift/level conclusions, full B1-E uniqueness. |
| Smoke majorant, OscillatorPhysicalSmoke:23 | `physSmoke_supBound_zero` (private) | PASS | Literal zero bound of an empty polynomial. |
| Harmonic smoke, :28 | `physicalSmoke_zeroDrift` | PASS WITH NOTES | Calls the actual main theorem with χ=ε=d=0 and kernel-checked identities; initial action box is zero, so only the origin is exercised. |

The main theorem's binder prefix from `{H χ Nact P : CartPoly}` through
`hmargin` is **byte-identical** to that of `oscillatorStep_confinement`.
Additional data are exactly `a′ s d`, hs0–hs3, hd and physical `z₀,hz₀`.
There is no image-membership, flow, confinement, inverse, or analytic-bound
hypothesis smuggled into the physical theorem. All extra checks are the explicit
finite scalar inequalities requested by the brief.

## Refutation attempts and proof accounting

1. **Gauge / max norm.** `norm_realFlow_sub_le` bounds the gauge norm by
   abs(t) ε. With W=gaugeScalar δ, its norm is the ordinary product norm divided
   by δ. Multiplication by positive δ yields abs(t) ε δ. The product max norm
   and each Pi sup norm dominate the individual coordinate norm. Real inclusion
   converts complex norms to real absolute values. Thus no dimension factor or
   missing δ is hidden here. Interior monotonicity safely passes from 1 to 1/2.

2. **Physical initial box is genuinely pulled back.** At :170–193,
   A(z₀)≤a′ and hs0/hs1 yield abs(q₀),abs(p₀)≤s. Since εδ≥0, hs2 implies
   s+δ<ρ, so z₀ belongs to realInterior 1. Set w₀=Ψinv z₀; inverse displacement
   gives coordinate bounds s+εδ, and the right-inverse theorem proves
   Ψ w₀=z₀ (:176). Therefore A(w₀)≤(s+εδ)²≤a by hs3. This proves the
   requested inclusion for **every** physical point of the box, without assuming
   that it lies in a chart image. The initial datum in the returned ODE is z₀.

3. **Transfer uses the correct domains.** Applying B2-STEP at w₀ yields the
   physical solution and chart actions. For abs(t)≤T, let u=Ψinv(z(t)). The
   inherited level estimate and strict margin give A(u)≤a+ηT<b, while
   hdom1 and εb>0 imply 2b≤r². Consequently u is in realInterior 1 and has
   coordinates bounded by r (:205–214). Apply *forward* chart displacement at
   u and use the inherited identity Ψu=z(t). Coordinates of z(t) are bounded
   by r+εδ. No inverse displacement is invoked at an unverified physical z(t).

4. **Exactly one transfer invoice.** The same r bound holds for w₀ because
   A(w₀)≤a≤b. Initial inverse displacement bounds the difference z₀−w₀ and
   gives coordinates of z₀ bounded by r+εδ. The action perturbation lemma at
   both endpoints gives εδ((r+εδ)+r)=εδ(2r+εδ)≤d. Thus
   abs(A(z(t))−A(z₀))≤d+η abs(t)+d and
   A(z(t))≤a+ηT+d (:233–245). The requested hd is preserved exactly;
   no second s-dependent d premise is needed. hs3 and s bounds are initial-only.

5. **Existence and uniqueness.** The full open lifetime T₁>T and Hamiltonian
   equation for physical cartEval H are retained. Rewriting Ψw₀=z₀ also rewrites
   the initial condition in the uniqueness premise. Every solution in univ on
   every order-connected I containing 0 agrees on I intersect Ioo(-T₁,T₁).
   The bounds retain abs(t)≤T, including both endpoints and T=0. There is no
   assertion of uniqueness of total functions outside the solution interval.

6. **Action perturbation signs.** Factoring a²−b² and using abs(a+b)≤s+s′
   pays each square difference by e(s+s′); division of their sum by two pays
   the action difference with the same constant. A coordinate premise implies
   e≥0, which is used explicitly by mul_le_mul. No positivity premise omitted
   from the requested interface has been assumed.

## Definitions and source fidelity

There are **no new def, abbrev, structure, instances or alternative carriers**
in either file. The phase space is exactly `(Fin n → ℝ) × (Fin n → ℝ)`;
complex flow coordinates use the corresponding complex carrier. Actions are
literally the frozen `(p²+q²)/2` with p=second, q=first coordinate.

The inherited stepChart/stepChartInv are real restrictions of time ±1 of the
complex Hamiltonian flow. Its total definition has an initial-point fallback
outside existence. Every use here discharges the small-field and interior
conditions of the real-flow theorems before deriving displacement or inverse
identities. No result depends on that fallback. No new conclusion-shaped
bundled premise is introduced.

No suspected mathematical source or blueprint erratum found. This is the
specified elementary original-coordinate deduction, not a new claim about
GLS17/CL20 or an independent re-audit of all inherited analytic proofs.
The asymmetric perturbation form strengthens the requested equal-radius form.
No implementation deviation changes the requested physical theorem.

## Notes (nonblocking)

- **N1, stale documentation:** OscillatorPhysical.lean:17 says
  “`oscillatorStep_physical` (in `OscillatorPhysical/Main`)”. The theorem is in
  OscillatorPhysical.lean itself; there is no such split module. Handoff's
  249-line count is also stale: the audited file has 250 lines. These do not
  change the proof or public interface; report-only scope leaves them untouched.
- **N2, smoke scope:** OscillatorPhysicalSmoke.lean:29 assumes A(z₀)≤0,
  which forces z₀=0. The proof genuinely instantiates the harmonic oscillator
  H=cartAction 0, χ=[], Nact=cartQVar 0, P=[], L=1, ρ=5, δ=δc=1,
  ε=0, a=a′=s=d=η=0, b=1, εb=T=1, r=2. Its exported statement drops
  the ODE/lifetime/uniqueness clauses after obtaining them. It verifies the
  requested zero-drift application but does not exercise a nonzero orbit,
  nontrivial chart displacement or remainder. No stronger smoke coverage is
  claimed by this audit.

## Validation receipts

All Lean/Lake calls were serial. Every such command was wrapped with:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 \
  nice -n 10 env LEAN_NUM_THREADS=1 <command>
```

The gate itself runs `nice -n 5 lake build`, as required. No heartbeat,
recursion-depth or synthesis budget was overridden. No clean, update, cache
fetch, full library build, provider edit or generated-root edit was performed.

Targeted builds, in this order (each exit 0, no warnings):

```text
/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b2orig KAM.EffectiveStability.OscillatorPhysical
[inp-gate] slot 1 acquired 01:50:27 for KAM.EffectiveStability.OscillatorPhysical
Build completed successfully (2985 jobs).

/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b2orig KAM.EffectiveStability.OscillatorPhysicalSmoke
[inp-gate] slot 1 acquired 01:50:48 for KAM.EffectiveStability.OscillatorPhysicalSmoke
Build completed successfully (2986 jobs).
```

A scratch file `.lake/abi-scratch/B2OrigAudit1.lean` imported
KAM.EffectiveStability.OscillatorPhysicalSmoke and contained `#print axioms`
for every public theorem. Command `lake env lean .lake/abi-scratch/B2OrigAudit1.lean`
exited 0, with exactly:

```text
'KAM.EffectiveStability.realFlow_coord_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.stepChart_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.stepChartInv_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.stepChart_stepChartInv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscillatorAction_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscillatorStep_physical' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.physicalSmoke_zeroDrift' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay (one invocation, exit 0):

```text
lake env leanchecker --verbose KAM.EffectiveStability.OscillatorPhysical KAM.EffectiveStability.OscillatorPhysicalSmoke
replaying KAM.EffectiveStability.OscillatorPhysicalSmoke
replaying KAM.EffectiveStability.OscillatorPhysical
```

Public short-name command (exit 0):

```text
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-b2orig KAM.EffectiveStability.OscillatorPhysical KAM.EffectiveStability.OscillatorPhysicalSmoke
short-name check OK (no reused public short name)
```

Direct line/width inspection: OscillatorPhysical.lean has 250 lines, maximum
width 100; OscillatorPhysicalSmoke.lean has 60 lines, maximum width 95;
no overwidth lines. Both have copyright, module, public import, docstring and
`@[expose] public noncomputable section`. No forbidden escapes, banned
carrier, resource override or unauthorized production provider import found.
`git diff --check inp...HEAD` exits 0 with no output.
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.
