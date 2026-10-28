# S5 independent package audit 1

**Overall verdict: PASS WITH NOTES for the S5 slice.** Its four public declarations match the
signed contracts exactly. All assigned `sb-sm-*` obligations are established, including genuine
integrability and the local radicand margin. No mathematical or signature defect was found in
`KAM/Planetary/SecularBox/Smooth.lean`. Repository validation notes are recorded below; they
must not be reported as a clean whole-branch hygiene pass.

No frozen theorem anchor or provider is assigned to S5. In particular this report does not
certify or seal `secularBoxSafety` or `secularBoxAtCitedMasses`. Provider/frozen-type equality
and a frozen seal-body application are inapplicable to this infrastructure package.

Scope: only `KAM/Planetary/SecularBox/Smooth.lean`, HEAD
`0dbb6ad42fd605a3b5f38cf5ae707b5c2001ecb4`, branch `inp-p14-s5`, 2026-10-28.
The user-specified report path in this worktree overrides the generic brief's main-worktree
output instruction. The pre-existing untracked S5 handoff was left untouched.

Read AGENTS.md, PLAN, DECISIONS, the package brief and S5 handoff; P14 design row S5 and
node table, both P14 design audits, the authoritative signature file, track P statement,
blueprint `p14b-secular-box.tex` lines 175–205 and downstream consumers, corresponding
`P-p14b.nodes.md` contracts, the frozen secular-box safety anchor, and the frozen definitions
used by the proof. These nodes are explicitly ours/direct calculations from frozen definitions;
no additional claim about an external pinned source is needed for this package.

Audited source SHA-256:
`b6ca308a447d28214f6b49590ca6da97a0b4f874c909c7267af378b14595956a`.
Signature file `/root/code/KAM-inp/.drafts/design/P14Signatures.lean` SHA-256:
`24916d5937451954a71ba5349789bcbda5b06b70f40fe3a6ba24eec9bd533f88`.
Design SHA-256:
`04c358878699851e0e45adcccbfd06048e2474b6cffe015821df5e072f36fca3`.

## Declaration and node ledger

Names are in `KAM.Planetary`; line locators refer to `SecularBox/Smooth.lean`.

| Node / role | Declaration / proof location | Verdict | Reason |
|---|---|---|---|
| Explicit integrand, proposition (a),(b) | `explicitSecularIntegrand`, 224–227 | PASS | Definition, including body, is byte-identical to signatures 449–451. Literal full moving Hamiltonian, both Jacobians, correct phase carrier. |
| `sb-sm-1`, signed helper | `secular_integrand_identity`, 244–251 | PASS | Header byte-identical to signatures 452–455. All masses, couplings, phases and integration variables retained; no positivity premise. Unfolds the actual frozen objects and block identities. |
| `sb-sm-2`, signed helper | `secular_integrand_smooth`, 295–315 | PASS | Header byte-identical to signatures 457–464. Joint C∞ on S×univ plus global coordinatewise 2π periodicity. No added conclusion premise or mass/coupling restriction. |
| `bpP:p14:sb-smooth-prop` | `sb_smooth_prop`, 317–363 | PASS | Header byte-identical to signatures 441–447. C∞ on S, literal four-clause SecularRegular, and global lambda-independence. |
| `sb-sm-1`, integral and independence | local `hH`, 328–334; final conjunct, 360–363 | PASS | Exact normalized integral identity proved for every w; independence holds for arbitrary replacement lambda, hence in particular on S. |
| `sb-sm-2`, chart/radicand obligations | private chain, 35–222 and 261–293 | PASS | Positive radicand, positive denominators and collision-free lengths supplied before smooth composition. Local quantitative margin is proved, not assumed. |
| `sb-sm-3`, parameter integral | local `hcd`, 335–341 | PASS | Applies S4 `secular_parametric_integral` for every finite k and uses `contDiffOn_infty`; compact box and open S are proved. |
| `sb-sm-4`, integrability and differentiability | 343–359, especially 347 and 350–359 | PASS | Actual frozen integrand identified with explicit integrand, continuous on compact box, then IntegrableOn. Ambient differentiability follows from C∞ and openness. |
| S7 boundary | `secular_field_components` absent | PASS / outside S5 | Design 456–457 explicitly assigns it to S7; row S7 is SecularBox/Field. No missing S5 export. |

There are precisely one new public definition and three new public theorems. Every other
module-level declaration is private; no unsigned public theorem borrowing a graph-node name
claims a narrowed conclusion. The node table at design 230–234 assigns the parent and all four
steps to Smooth; the ledger accounts for each internally or through its prescribed signed export.

## Definitions, proof and consumer fidelity

`explicitSecularIntegrand` is the only new def/abbrev/structure. It is the intended object on
its entire carrier: the actual frozen `movingHamiltonian 1 1 m mu (ellipsePhase m w F)` times
`∏ i, longitudeJacobian w i (F i)`. No branch, junk witness, substitute Hamiltonian, changed
normalizer, truncation or assumed identification is introduced. It inherits the frozen total
real sqrt/division operations off the physical domain. No analytic/safety claim exploits those
total values: smoothness is restricted to S and physical regularity includes positive masses,
positive fast actions, ellipticity, positive Jacobians and every-phase NoCollision.

The auxiliary moving-Hamiltonian smoothness lemma permits arbitrary fixed m because inverse
masses are constants with respect to the phase. This causes no false physical assertion;
`sbSmooth_hm` proves both actual masses positive from the closed Saturn interval when packing
SecularRegular. The coupling mu is any real number, as the blueprint explicitly permits.

The private chain proves smoothness coordinatewise on the literal Pi/max-norm phase carrier.
The only variable square root is handled at a positive argument; lengths use
`analyticAt_planeLength` away from zero, composed with the smooth body vectors. Momentum's
`fast * longitudeJacobian` denominator is positive, and `1 + secularRoot` is nonzero.
`sb_s` supplies every-phase NoCollision and Jacobian >4/5. Product/chain rules then give joint
C∞. Periodicity is an algebraic consequence of sin/cos and holds for every w and F, including
outside S; it makes no assertion of physical regularity there.

The S3 margin is not an unpaid dependency. At 123–139, private
`sbSmooth_radicand_margin` proves both
`99/100 < 1 - Gamma/(2*Lambda)` and
`99/(100*Lambda) < (1-Gamma/(2*Lambda))/Lambda`
from Lambda>0 and 50*Gamma<Lambda. At 146 the first margin is consumed by
`sbSmooth_reg`, giving positive radicand; `sbSmooth_cd_scale` consumes this at 158–162.
The second quantitative inequality is also established locally, although the analytic chain
needs only positivity. Region's missing public margin does not block this proof, and this
report does not certify that S3's own node is complete. Replacing the local lemma with a
future Region export is optional maintenance, not a present proof obligation.

The compact parameter box is literally `Set.pi univ (fun _ => Icc 0 (2*pi))`, and `hH`
retains the frozen `(2*pi)^(-2)` normalization. All finite-order smoothness comes from S4;
its first-derivative integral identity is available in that imported supplier, so the
blueprint's differentiation-under-the-integral route is retained. S5 assumes no integrability
or smoothness conclusion. It separately proves IntegrableOn for clause (iii), rather than
using a total Bochner integral as a stand-in. Clause (iv) is actual ambient differentiability
at w, obtained using the open-set neighborhood.

Signed `sb_smooth_prop` packages fewer intermediate facts than the full proposition, exactly
as the design requires: the integral identity is internal and recoverable by unfolding
`exactSecularHamiltonian`/`secularAverage` and using public `secular_integrand_identity`.
The public smooth-integrand export supplies joint continuity and periodicity to rotation
and parameter-integral consumers. The main export supplies C∞ and regularity to the
predicate, field, flow and safety consumers. Its global lambda replacement equality supplies
the fast-angle derivative argument and is stronger than the on-S statement; this is already
declared departure D4 at design 328–329. No consumer needs a strengthened source premise.

## Validation receipts

All audit Lean/Lake invocations ran serially, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
There were no resource overrides, package updates, clean builds or source edits.

Targeted build:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-s5 KAM.Planetary.SecularBox.Smooth
```

Exit 0; output:

```text
[inp-gate] slot 3 acquired 18:55:56 for KAM.Planetary.SecularBox.Smooth
Build completed successfully (9104 jobs).
```

The wrapper uses the existing worktree build overlay; the job count is Lake's build graph
receipt, not an assertion that the library was rebuilt from scratch. No warning or sorry
appeared in this build output.

Fresh untracked probe (removed after checks):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S5Audit.lean
```

Exit 0. The probe copied each signed theorem header under a fresh `audit_...` name, proved
it by the corresponding S5 theorem applied to exactly its explicit binders in order, and
checked `example : type_of% @audit_name := @name`. It imported only the completed Smooth
module, never the admitted signature file. A separate rfl example checked the entire
integrand body. Independent Python text comparison found each of the three headers and
the one full definition byte-identical to the authoritative signatures.

Exact axiom output:

```text
'KAM.Planetary.sb_smooth_prop' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.secular_integrand_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.secular_integrand_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.explicitSecularIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay, one invocation for the sole assigned module (S5 has no separate provider):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularBox.Smooth
```

Exit 0; exact output:

```text
replaying KAM.Planetary.SecularBox.Smooth
```

Repository lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**; exact output:

```text
Lean lines over 100 characters:
/root/code/KAM-inp-p14-s5/KAM/Frozen/Planetary/Theorems/AmdConfinement.lean:77:101
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (889 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The generated-root diagnostic is the brief's explicit permitted exception. The 101-character
frozen AMD line is an additional inherited failure, outside S5, and is **not** covered by
that exception. Whole-worktree lint therefore does not pass even after discounting the
stale root. Smooth itself satisfies both length limits. Frozen-anchor and elaborated ABI
checks pass, as shown above. No protected/generated file was repaired during this audit.


Static/source checks: Smooth has 367 physical lines, no line over 100 characters, no
forbidden token or resource override, and the required copyright, module header,
public imports, docstring and exposed public noncomputable section. No EuclideanSpace,
new instance, root namespace shadow, or reused public declaration short name was found.
A declaration search of all other KAM Lean files found no site for any of the four names.
A recursive source-import check found 58 project modules: 51 frozen imports, all definitions;
no provider module, frozen theorem or frozen import containing sorry is reachable.
`git diff --check inp...HEAD -- KAM/Planetary/SecularBox/Smooth.lean` exits 0.

## Repository notes, defects and limitations

The required `git diff inp...HEAD` warns:

```text
warning: inp...HEAD: multiple merge bases, using da66a38ef57f49caf021d7535abf5069e1a8cc18
```

At inspection `inp` was `7413c7f87f6e8cdabb0c32c8683d46b65135ef5e`.
The chosen three-dot diff contains 111 files, including inherited work outside S5.
The requested protected-path check is **not empty**:

```sh
git diff inp...HEAD --name-only -- KAM/Frozen manifest KAM.lean README.md
```

```text
KAM.lean
KAM/Frozen/Planetary/Theorems/AmdConfinement.lean
manifest/frozen-anchors.json
```

Those changes include an inherited AMD seal and its manifest state change, and generated
root imports. They are not certified by this S5-only audit. Attribution is checked separately:
`git diff --name-only HEAD~2 HEAD` prints only Smooth; both S5 commits (`f2aab7f1`,
`0dbb6ad4`) touch only that module, and
`git diff --quiet HEAD~2 HEAD -- KAM/Frozen manifest KAM.lean README.md` exits 0.
Thus the literal whole-comparison hygiene condition fails, while S5 itself has no protected
file edit. Do not silently reinterpret the requested three-dot comparison as an empty diff.

No new suspected mathematical blueprint/source defect was found. The known S3 export gap
is worked around by a proved private lemma, as explicitly requested in the handoff addendum.
Declared departures introduced by S5: the local proof duplication just described; no change
to any signed statement, frozen definition, law, carrier, normalizer or public hypothesis.
The predeclared global independence strengthening remains D4. No production file or git
state was modified by the auditor. This report is the only persistent repository addition
from the audit; the pre-existing handoff remains unmodified. Scratch probes/logs are deleted
once their receipts have been transcribed here.
