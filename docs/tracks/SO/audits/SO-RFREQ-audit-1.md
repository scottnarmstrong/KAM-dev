# SO-RFREQ independent audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-sorfreq`.
Audited HEAD: `eab2bb8b6d490f759251c2ce9759f195f45f668e`.
Comparison ref `inp`: `9fd72f92acceab80b1cb91ba74de449c0ea8b697`.

**Overall verdict: FAIL under the handoff's literal no-reused-public-short-name requirement.**
The complete signed mathematical slice passes statement, definition, proof, axiom, build and kernel checks.
The sole blocking finding is the signed public name `isDiophantine_smul`, already used in KAM.
There is no frozen theorem anchor or provider export in this package; no seal-readiness claim applies.

## Scope and authority

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`,
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and
`docs/tracks/SO/audits/SO-RFREQ-handoff.md`.
Applied the user's exact report destination, overriding the generic brief's MAIN-worktree destination.
Audited only `KAM/SpinOrbit/RotFreq.lean`; dependencies were read to verify its meanings and provenance.
Compared the full `git diff inp...HEAD`: exactly one added file, 81 lines.
The handoff was already untracked before this audit and was left untouched.

Controlling statements: `/root/code/KAM-inp/.drafts/design/SOSignaturesLunar.lean:314-342`
(§I.3), and `/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md`
Revision 5, O5 row at line 77, frequency discussion at lines 443-451,
module/slice split at lines 539-549, and Appendix A §I.3 at lines 2154-2182.
The named SO slice, rather than unrelated I/N/P anchors and blueprints, supplies the package contract.

## Declaration review

All names below are fully qualified by `KAM.SpinOrbit`.
All five theorem headers match the signed source **byte for byte**, and the definition's entire
single-line declaration/body matches byte for byte. Namespace placement also agrees with the
signed file's `namespace KAM.SpinOrbit` at line 237. No missing signed declaration, changed binder,
added premise, weakened conclusion, or increased constant dependence was found.

| Node / location in RotFreq.lean | Declaration | Verdict | Reason |
|---|---|---|---|
| SO-RFREQ, 28 | `lunarRotFreq` | PASS | Exactly `![(κ : ℝ) * (ν - 1), κ]`, signed carrier `Fin 2 → ℝ`. |
| SO-RFREQ, 35 | `lunarRotFreqMinus_eq` | PASS | Signed coefficients `[[-79 * κ / 3118, κ / 3118], [κ]]`; no positivity premise. |
| SO-RFREQ, 42 | `lunarRotFreqPlus_eq` | PASS | Signed coefficients `[[79 * κ / 3118, -κ / 3118], [κ]]`; no positivity premise. |
| SO-RFREQ, 50 | `isDiophantine_smul` | FAIL (naming only); proof/type PASS | Exactly signed positive scaling with constant `t * γ`; short name reused. |
| SO-RFREQ, 67 | `lunarRotFreqMinus_isDiophantine` | PASS | Only signed premise `0 < κ`; constant `κ/42`, exponent 1; uses SO-ROTDIO minus theorem. |
| SO-RFREQ, 74 | `lunarRotFreqPlus_isDiophantine` | PASS | Only signed premise `0 < κ`; constant `κ/42`, exponent 1; uses SO-ROTDIO plus theorem. |
| Internal, 30 | private `algFreq_two'` | PASS | Finite polynomial evaluation at two coordinates. |
| Internal, 61 | private `lunarRotFreq_eq_smul` | PASS | Coordinatewise scalar-multiplication identity. |

## Definitions, proof soundness, and rational boxes

The only new definition is `lunarRotFreq`: a total, intended two-coordinate vector for every real
`ν` and rational `κ`, including zero and negative `κ`. There are no fallbacks, junk values,
structures, bundled assumptions, instances, or hidden conclusion-shaped premises. Positivity is
required only where the signed Diophantine corollaries and scaling lemma require it.

`QuadraticDiophantine.lean:32-35` defines the landed frequencies as
`ν± = 1 ± 1/(40 + lunarG)`. Its exact identities at lines 58-62 imply
`ν₋ - 1 = (-79 + √5)/3118` and `ν₊ - 1 = (79 - √5)/3118`.
Thus both polynomial lists describe exactly the rotated reference vector, with second coordinate
`κ`; they do not inadvertently describe the unrotated or half-frequency vectors.
The exact equalities hold for all rational `κ`.

The scaling proof factors `t` from the finite dot product, rewrites `|t| = t`, and multiplies
both sides of the original Diophantine inequality by positive `t`. It does not assume `γ > 0`,
`τ ≥ 0`, or `n > 0`, and none is needed. The lunar proofs explicitly invoke
`KAM.Certificate.lunarNuMinus_rot_isDiophantine` and
`KAM.Certificate.lunarNuPlus_rot_isDiophantine`, respectively, from SO-ROTDIO
(`DiophantineTransfer.lean:106-116`). Their exact conclusions are
`IsDiophantine (1/42) 1 ![lunarNu± - 1, 1]`.

Fresh Lean examples also verified both rational-box connections: given
`(lo : ℝ) ≤ √5 ∧ √5 ≤ hi` and `checkAlgBox 2 <signed coefficient list> lo hi box = true`,
rewriting with the corresponding `_eq` theorem and applying `algFreq_encloses` proves
`FreqEncloses 2 box (lunarRotFreq lunarNu± κ)`.
The landed `algFreq` evaluates ascending polynomial powers, so coefficient signs and order agree.
There is **no concrete lunar certificate box in this signed slice**. Concrete box checks,
root-enclosure data and final `lunar{Lower,Upper}Cert_freq` remain downstream SO-DATA obligations
(the signed file places those at lines 508-513). This audit verifies the exact enclosure interface,
not a numerical radius or a final certificate's actual enclosure. It is not missing SO-RFREQ scope.

## Blocking finding: signed-name conflict

`RotFreq.lean:50` declares the public `KAM.SpinOrbit.isDiophantine_smul`.
`KAM/Iso/Linear/Tools.lean:38-39`, already present on `inp`, declares the public
`KAM.Iso.Linear.isDiophantine_smul`. The latter assumes `1 ≤ s` and preserves `γ`;
the new theorem assumes `0 < t` and scales `γ`. They are distinct full names and statements,
but share exactly the public short name forbidden by the handoff's AUDIT FOCUS:

> no public short name reused from KAM or Mathlib

An independent source scan of KAM and this worktree's Mathlib found this collision and no other
collision among the six public names. There is no harmful root shadow: all exports remain in
`KAM.SpinOrbit`, with no `_root_` declaration or root alias.

The shared checker nevertheless prints `short-name check OK (no reused public short name)`.
Inspection of `/mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py:118-127`
shows why: it exempts names appearing in a design signature file; `IPart123Signatures.lean:244` already
contains this short name. Its later dotted-name scan likewise exempts signed names.
Thus the checker's success does not establish the handoff's literal uniqueness requirement.
The handoff itself acknowledges the collision but lists no explicit owner exception.

Resolution requires an explicit ruling that this signed name is exempt, or a coordinated revision
of the signed name and implementation. Renaming only the implementation would violate the equally
explicit exact-signature requirement. No such repair or policy exception was silently made here.

## Independent validation

All Lean/Lake invocations were serialized and used `LEAN_NUM_THREADS=1`; build and explicit
Lean/kernel invocations used `nice -n 5`. The initial required lint run used the literal
`LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh`; because its ABI subprocess invokes Lake internally,
a final lint run was repeated under `nice -n 5` to give that subprocess the required niceness.
No heartbeat, recursion or synthesis overrides were introduced.

1. Full scope and protected-path checks:

   ```text
   git diff --stat inp...HEAD
    KAM/SpinOrbit/RotFreq.lean | 81 ++++++++++++++++++++++++++++++++++++++++++++++
    1 file changed, 81 insertions(+)
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   [empty]
   git diff inp...HEAD --check
   [empty; exit 0]
   ```

2. Targeted compile-gate build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sorfreq KAM.SpinOrbit.RotFreq
   [inp-gate] slot 1 acquired 15:06:39 for KAM.SpinOrbit.RotFreq
   Build completed successfully (2199 jobs).
   exit 0
   ```

   The gate internally runs `nice -n 5 lake build`.

3. Probe, signed fresh-name declarations, and axioms:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SORFreqAudit.lean
   'KAM.SpinOrbit.lunarRotFreqMinus_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.SpinOrbit.lunarRotFreqPlus_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.SpinOrbit.isDiophantine_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.SpinOrbit.lunarRotFreqMinus_isDiophantine' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.SpinOrbit.lunarRotFreqPlus_isDiophantine' depends on axioms: [propext, Classical.choice, Quot.sound]
   exit 0
   ```

   Probe statements were copied directly from the signed file under fresh names, with bodies
   applying the fully qualified implementation exports to exactly their explicit binders.
   It also checked the definition by `rfl` and both enclosure-interface applications above.
   No frozen seal-copy test applies: this module has no frozen anchor/provider pair.
   The temporary probe was removed after validation.

4. Kernel replay (one invocation for the one audited module):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.SpinOrbit.RotFreq
   replaying KAM.SpinOrbit.RotFreq
   exit 0
   ```

5. Repository lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1315 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1 (only the explicitly permitted generated-root staleness)
   ```

6. Additional static checks: 81 total lines, maximum 97 Unicode characters per line;
   module/copyright/import/docstring/public-section structure is valid; exposed definition body.
   No `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `native_decide`, `EuclideanSpace`, or resource
   overrides in the audited source. Local import closure: six KAM modules, no provider or frozen
   theorem anchor; only frozen import is `KAM.Frozen.Defs.IsDiophantine`, manifest state `SEALED`.
   Axioms independently confirm no imported draft assumption is used.

7. Shared naming check (with the limitation explained above):

   ```text
   python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-sorfreq KAM.SpinOrbit.RotFreq
   short-name check OK (no reused public short name)
   exit 0
   ```

## Source defects, deviations, and remaining uncertainty

No suspected mathematical erratum in a pinned source, frozen definition, or SO-RFREQ statement
was found. The signed surface and literal naming policy conflict as documented above; this is a
contract/hygiene defect, not a refutation of either Diophantine theorem. Generated-root staleness
is the brief's permitted lint exception and was not repaired. No numerical certificate or lunar
confinement theorem is claimed by this package audit.

Only this report was added to the repository by the auditor; scratch probes were confined to
`.lake/abi-scratch/` and deleted. No state-changing Git command, production-source edit, frozen or
manifest edit, generated-root regeneration, or dependency/cache update was performed.

Final report verification: no pending placeholders; scratch probe absent; `git diff --check`
and `git diff --no-index --check /dev/null <report>` both exit 0. Final Git status contains
only the pre-existing untracked handoff and this new untracked report.
