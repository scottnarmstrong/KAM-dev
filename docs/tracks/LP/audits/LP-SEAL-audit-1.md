Audited HEAD: `f5729cf8af5bfb688326d989161db2d865fbeead`.
Initial static-audit HEAD: `9a23d75ccc0adca4b8a179d366886eff86dc9c39`.
Approved draft: `de343000` (`inp-lp-freeze7`, D62).
Comparison base: `8e6f75d0` (merged implementation immediately before installation).
Existing-manifest baseline: `inp@fc55b79512be84ee028470d409482b30fc434a71`.

# Independent LP freeze-and-seal audit 1

**PASS WITH NOTES.** All ten seal-audit checks pass at the audited HEAD, within the binding
revised kernel scope. There are no blocking findings and no required source changes.
All 128 approved files retain their authorized identity; all 39 anchor/provider pairs are
raw Expr-equal and standard-axiom-only; all 167 new frozen/provider modules independently
replay successfully. Final lint exits 0. The notes preserve the approved closure convention,
the source-facing export scope, and the lander's separately assigned full 284-module replay.

Fresh independent session, refute-first, no subagents. Read AGENTS.md, PLAN, DECISIONS, the full
brief at `/root/code/KAM-inp-lp/docs/tracks/LP/freeze/AUDIT-SEAL-BRIEF.md`, RUNBOOK §§2 and 6
and its closing rulings; applied `/root/.claude/skills/lean-statement-audit/SKILL.md`.
Read live main's D53/D58/D59/D62, the approved proposal and manifest-entry drafts from git,
the local source MAIN and AMENDMENTS, both statement-audit reports, the actual providers,
rebase scripts and guard/hash code. Prior statement-audit evidence is kept distinct from
fresh seal checks. The brief and the orchestrator's staging note control the single-pass
freeze/seal staging; no intermediate state is approved for landing.

Only this report is a durable audit edit. No source, frozen file, manifest, generated root,
application data, or previous report was changed. No commit, root generation, whole-branch
build or certificate-library build was performed. Every audit Lean/Lake invocation
uses the D53 4 GB scope from this worktree. Calls were initially serial behind the 8 GB gate;
the later binding root-b8 ruling authorizes three parallel kernel workers behind a 6 GB gate,
each independently capped at 4 GB with no swap and one Lean thread.

## Findings and dispositions

| ID | Class | Finding | Exact disposition |
|---|---|---|---|
| N1 | NOTE | The approved `definition_closure` lists follow the runbook's frozen-definition-edge traversal, including inherited core definitions. All 128 reproduce under that convention. Following every implementation/provider import instead reaches additional frozen definitions for 38 theorem anchors. These are distinct notions of closure; file-hash checks do not establish proof closure. | No fix. Retain the approved lists: the actual Expr traversal confirms every statement-reachable project definition is covered for all 39 anchors, while provider kernel/axiom checks cover the proof side. Do not silently change approved non-hash manifest fields. |
| N2 | NOTE | Generated `KAM/Root/Provider.lean` imports sealed providers. This is expressly authorized by the 2026-10-29 root exception, extended to root parts; `scripts/lint_sources.sh:60–66` and GUARDS document it. | No fix. Quarantine scan excludes authorized generated roots and finds no remaining violation. |
| N3 | NOTE | Draft-7 audit N3 remains: radial incidence, element errors and half gaps are exported; standalone L16 on arbitrary safe compact sets and geometric tangency are outside these anchors. | Preserve that scope in every closure claim. |
| N4 | NOTE — resolved | The prior delta audit's editorial R2 is already repaired in the approval object: only the two source-map role paragraphs differ between `c9c2b904` and `de343000`, using exactly its requested literal-formula / `N/A_LITERAL` text. R1's 101-column implementation docstring is also rewrapped before installation. | No fix. The approval object, rather than an earlier report snapshot, controls. |
| N5 | NOTE | The binding root-b8 update assigns the complete 284-module replay to landing. The author's 128 frozen-module receipts are copied below; the auditor independently covers all 78 required theorem/provider modules and, from work completed before that update, all 89 definitions too. | No source fix. Use the lander's three-worker full replay as the authoritative landing gate; this audit does not claim the remaining 117 implementation replays. |

BLOCKING: 0. CHANGE-RECOMMENDED: 0. No unpaid premise, statement repair, hash mismatch,
kernel failure or axiom gap remains in the audited seal set.

## Ten-check ledger

| Check | Fresh evidence / status |
|---|---|
| 1 Authority | D62 on main quotes “approve draft 7”, identifies `de343000`, 89 definitions and 39 theorems, and authorizes seals after this audit. Draft 8 is excluded. No new manifest ID beyond the approved 128 occurs. |
| 2 Identity | `lp_identity_check.py --pin`: 128 files, ALL IDENTICAL, exit 0. Independent `git show` / `sha256sum` and byte substitution also pass all 128; every raw draft digest agrees with `verification-draft-7r1.txt`. Outside the proof markers only the two approved placeholders change. |
| 3 Manifest | All approved non-hash fields agree, apart from the expressly authorized approval/ruling/state updates. All 128 entries are SEALED. Guard digest/region code reproduces 2,225 whole-file, prefix, suffix and closure hashes. All 179 old entries are JSON-equal to pinned inp. Commit C changes only those 128 ABI placeholders; both independent ABI runs reproduce every final value and agree exactly. Top-level guard configuration is unchanged. |
| 4 Seal bodies | All 39 use exactly `by exact <registered provider> <explicit binders>` in guard order and within 3 lines / 240 bytes. Prefix/suffix match approved text after substitution. Guard reports no region error. |
| 5 Providers | All 39 full statement texts match their anchors, including let-bound time windows. Five closing providers are byte-identical to staging `f2fa9f88`; 34 characterization proofs match their pre-freeze implementation bytes. Two sibling proofs are privately inlined, exactly as disclosed. No provider-to-provider or frozen-theorem import; no forbidden proof token. Actual probe: 39/39 raw Expr-equal types, 39/39 exact applications, 78/78 standard-only theorem axiom sets. |
| 6 Rebase | Independent in-memory reconstruction: exactly 89 definition blocks and 34 theorem blocks removed across 13 implementation paths, with only approved imports added; every retained byte agrees, and no other implementation path changes. Lists agree with proposal §7. Namespace-aware scan finds exactly one owner for each of the 89 definitions, in its frozen file. Derivative is byte-unchanged against inp and the pre-install base; no lunar data changed. |
| 7 Axioms/kernel | 39 anchors + 39 providers have exactly `[propext, Classical.choice, Quot.sound]`; 89 definitions have a subset, with no sorryAx. Independent replay: 167 unique modules, all exit 0, including the entire binding 78-module set. Author partial receipt: 128/128 frozen modules exit 0. |
| 8 Quarantine/roots | `gen_root_imports.py --check`: exit 0. Independent source scan: no non-root/non-anchor provider importer; all new entries SEALED; no LP DRAFT_SORRY. Max new frozen/provider file length 152 lines. `check_frozen_anchors.py`: FROZEN-ANCHOR GUARD OK, exit 0. |
| 9 Carry-forward | N3 scope preserved. N1 actual real-module types, semantic closure, axioms and kernel checks pass. N4: all 34 characterization anchors are sealed and sorry-free in the same installation as their definitions, before consumer admission. No broader graph/source-node promotion is inferred from the old simulated draft checks. |
| 10 Records | Commit C installs FREEZE.md and exactly 128 D62 rows, with one owner per entry; every path, export, provider and literal seal body agrees. Final commit f5729cf8 adds the handoff and partial-replay receipt and updates FREEZE.md to state the 128/284 stop and landing responsibility. All three documentation changes were checked; KAM and manifest bytes are unchanged. |

## Independent static verification

The rebase check starts from git's `8e6f75d0:<implementation path>`, removes each approved
declaration block and adds only its frozen imports in memory, then compares every remaining
byte to the installed source. It also checks the complete changed-path set. This is stronger
than signature equality for surviving declarations: their proofs and surrounding bytes
also remain unchanged. The 34 moved proofs are compared separately from statements,
including both private sibling copies.

The full provider telescope comparison runs from `theorem <name>` to the final assignment
before the frozen proof marker. It includes the `let T := ...` in the safety conclusions;
a split at the first `:=` alone would miss part of these statements. It finds zero differences.
The five closing bodies apply:
- `lp0_planar_barrier_source`;
- `lp1_planar_strongAMD_safety_source_isDiophantine`;
- `lp1_planar_strongAMD_safety_source_isDiophantine_halfInteger`;
- `lp2_spatial_strongAMD_safety_source_isDiophantine`;
- `lp2_spatial_strongAMD_safety_source_isDiophantine_halfInteger`.

The two private sibling inlinings are `sourceOscAxis_pos` inside `SourceOscPeriPos`, and
`orderedCrossThreshold_isLeast` inside `OrderedStrongThresholdIsLeast`. Both copied proof
bodies are byte-identical to the original implementation proofs. They add no public premise.

Source pins independently reproduced from the approved commit:
- MAIN.md: `68e9167f04e4a04689ea163c74e02ffcaea657b252726080abdbe37bdba48c1b`.
- AMENDMENTS.md: `c887d1e27354a3db7fb8a20d8bf3e33a9ef95ff3173f925ba5ebfab192651881`.
- Approved manifest-entries.json: `46b7dec753a746bfc5bbfb8058190c77c0bcc219748ee6ca65f68463ec7a9e33`.
- Independent ordered `path + space + raw sha256` aggregate (newline-separated, no trailing
  newline): `2fd621b1752aab3557edf5fcf69ef3efdd290a9254f1f637d70770a9ffc42214`.

The earlier delta audit is available at
`/root/code/KAM-inp-lp-fz7r-audit/docs/tracks/LP/freeze/STATEMENT-AUDIT-DRAFT7-2.md`,
SHA-256 `9096e4a5bcbf166d633977f1dba37dde023913849a4bab0a4ece89f1d3896e43`.
Its statement verdict is PASS WITH NOTES at `c9c2b904`; this report independently binds
the final approval object at `de343000` rather than treating that earlier HEAD as the approval.

## Commands and outputs

All paths below are relative to `/root/code/KAM-inp-lp-sealaud`, unless absolute.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -I -B docs/tracks/LP/freeze/lp_identity_check.py \
  --root /root/code/KAM-inp-lp-sealaud \
  --approved de343000:docs/tracks/LP/freeze/draft7 \
  --date 2026-11-01 --decision D62 --pin
# 128 files checked
# ALL IDENTICAL
# exit 0

# Independent, for each approved draft:
git show de343000:docs/tracks/LP/freeze/draft7/<frozen-path>.txt | sha256sum
# 128/128 agree with both hashlib and verification-draft-7r1.txt

PYTHONDONTWRITEBYTECODE=1 python3 -B -I scripts/gen_root_imports.py --check
# no output; exit 0

PYTHONDONTWRITEBYTECODE=1 python3 -B -I scripts/check_frozen_anchors.py \
  --root /root/code/KAM-inp-lp-sealaud --manifest manifest/frozen-anchors.json
# FROZEN-ANCHOR GUARD OK
# exit 0
```

No new suspected defect in the pinned mathematical source has been found during these seal
checks. No mathematical deviation was introduced. The single-pass SEALED installation is the
brief's explicit adjustment to the older runbook's intermediate DRAFT_SORRY staging.


## Source-facing binder and carrier ledger

This ledger records the approved five-anchor source surface and is rechecked against the
installed exact statements, MAIN §1/L5/T15/T19 and normative amendments. It carries forward
the earlier statement audit's classifications; the seal audit does not invent new source
premises. Each provider copies the *whole* corresponding telescope, so there are no additional
provider binders. The table applies separately to LP1, LP2, LP1-H and LP2-H. Rows marked
general only are omitted in the two corollaries. The spatial `h₀` remains before the initial-axis
and Diophantine inputs; planar `h₀` remains after `hch`.

| Expanded input | Bin | Source or justification |
|---|---|---|
| implicit `n : ℕ` | TYPING | MAIN:11 |
| `hn : 2≤n` | STANDING | MAIN:11 |
| `ν : Fin n→ℝ` | STANDING | MAIN:11 |
| `hν : ∀i,0<ν_i` | STANDING | MAIN:11 |
| `hνmax : ∃i,ν_i=1` | STANDING | MAIN:11; D59 OD-3 |
| `hνle : ∀i,ν_i≤1` | STANDING | MAIN:11; D59 OD-3 |
| `A` | STANDING | MAIN:11–14 |
| `hA : IsCompact A` | STANDING | MAIN:11–15; empty allowed |
| `hAord`, positive axes | STANDING | MAIN:13 |
| `hAord`, all ordered pairs of axes | STANDING | MAIN:13 |
| `δ` | STANDING | MAIN:15 |
| `γ` | STANDING | MAIN:15 |
| `τ` (general only) | STANDING | MAIN:15 |
| `hδ` | STANDING | MAIN:15 |
| `hγ` | STANDING | MAIN:15 |
| `hτ` (general only) | STANDING | MAIN:15; D59 OD-4 |
| `μ` | SOURCE | MAIN:70 |
| `0<μ` (named `hμ` spatially) | SOURCE | MAIN:70 |
| anonymous `μ≤μ₀` | SOURCE | MAIN:70 |
| `z₀ : Phase (n*d)` | TYPING | MAIN:26–37,70 |
| physical premise: all star distances positive | SOURCE | MAIN:70 |
| physical premise: all Kepler energies negative | SOURCE | MAIN:70; Lean energy is ν_i times specific E_i |
| initial axes belong to A | SOURCE | MAIN:72 |
| every nonzero integer mode satisfies (5) | SOURCE | MAIN:64–65 |
| `hch`: positive actions | TYPING | positive masses and negative energies |
| `hch`: ordered action axes | TYPING | axes in A; Λ_i²=ν_i²a_i |
| `h₀`: positive masses | TYPING | duplicate of hν |
| `h₀`: nonzero positions | TYPING | duplicate physical premise |
| `h₀`: negative energies | TYPING | duplicate physical premise |
| source AMD ≤ ordered B − δ | SOURCE | MAIN:35,72; D59 OD-1/2/11 |

Counts per general anchor: SOURCE 8, STANDING 15, TYPING 7, EXCESS 0,
CONCLUSION-SHAPED 0. Counts per half-integer anchor: SOURCE 8, STANDING 13,
TYPING 7, EXCESS 0, CONCLUSION-SHAPED 0. RULED corrections add no extra hypothesis;
D59 fixes conventions rather than authorizing excess premises.

The internal Diophantine quantifiers `k : Fin n→ℤ`, `k≠0`, and finite summation index `i` are
SOURCE/TYPING indexing of (5), not an additional arithmetic gate. The frozen `KAM.IsDiophantine` expands using exactly
`Σ |(k_i:ℝ)|`, with no 2π factor. Both corollary signatures are byte-identical to the general
signature after the declared theorem-name change, deletion of τ/hτ, substitution of `n−1/2` in (5),
and explicit replacement of the time denominator by `2n+1`. No other premise or conclusion changes.

### LP0 (new sourceStrongAMD text)

Evidence: the installed `KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDBarrier.lean`,
whose complete approved bytes were independently reproduced above.

| Expanded input | Bin | Source or justification |
|---|---|---|
| implicit n | TYPING | MAIN:11 |
| hn | STANDING | MAIN:11 |
| ν | STANDING | MAIN:11; L4/L5 arbitrary positive masses |
| hν | STANDING | MAIN:11; L4/L5 |
| U | SOURCE | MAIN:164 |
| compact hU | SOURCE | MAIN:164 |
| hUch: positive actions | SOURCE | MAIN:43,164 |
| hUch: ordered axes | SOURCE | MAIN:43,164 |
| m | SOURCE | MAIN:164 |
| hm | SOURCE | MAIN:164 |
| physical z | TYPING | MAIN:26–37 |
| nonzero positions | STANDING | MAIN:24,28 |
| negative energies | SOURCE | MAIN:164 |
| hΛ: actions in U | SOURCE | MAIN:164 |
| h: positive masses | TYPING | hν |
| h: nonzero positions | TYPING | preceding physical premise |
| h: negative energies | TYPING | preceding physical premise |
| source AMD ≤ B−m | SOURCE | MAIN:164 |

Physical-branch counts: SOURCE 9, STANDING 4, TYPING 5, EXCESS 0,
CONCLUSION-SHAPED 0. The extra typing proof is supplied by `⟨hν,hphys⟩`, after hΛ;
it asserts no separation, nonradiality or dynamical conclusion.

| Abstract-list branch input (after dStar,dPair are chosen) | Bin | Source |
|---|---|---|
| I | TYPING | MAIN:164 |
| hI:I∈U | SOURCE | MAIN:164 |
| e | TYPING | MAIN:164 |
| all e_i≥0 | SOURCE | MAIN:164 |
| all e_i≤1 | SOURCE | MAIN:164 |
| Σ I_i D(e_i)≤B−m | SOURCE | MAIN:164 |

Here SOURCE 4, TYPING 2, all other bins zero. The compact K is chosen before every physical
state and is contained in the collision-free negative-energy region. The final `|L_i|≥m`
and `L_i L>0` encode precisely the planar invariable-frame lower bound. No `max ν=1` input is
needed in the static L5 statement; the proposal discloses this extension, already reviewed in rounds 1–3.


All nine dynamical constants precede μ and the initial state. The general exponent remains
`1/(2*(τ+1))`, the corollary exponent `1/(2*n+1)`, and the physical-time interval is closed
and symmetric. Both endpoint-error smallness inequalities are chosen before μ. Negative
energy, collision-free solutionhood, overlap uniqueness, Newtonian reconstruction, action
and axis drift in the Pi sup norm, orientation-free AMD, radial incidence and the half gaps
remain conclusion clauses. There is no secular, prograde, inclination or assumed drift input.

The source canonical carriers expand to positive masses, nonzero star positions and negative
energy. The osculating carriers additionally require μ>0 and negative actual-velocity energy
with eccentricity <1; these are the domain of the characterization lemmas and *outputs* along
the safety orbit. `OrderedActions` expands to positive actions and strictly ordered axes; its
physical interpretation remains under standing positive masses. The internal total helpers'
off-domain values are not certified as physical source objects.

For the 34 characterization exports, the complete binder families are:

| Expanded binder or carrier field | Bin | Source / applicability |
|---|---|---|
| implicit `n : ℕ` | TYPING | MAIN finite planet index; all 34 |
| implicit `ν : Fin n → ℝ` | TYPING | Mass parameter; physical interpretation under standing positive ν |
| implicit `μ : ℝ` | TYPING | Actual-velocity osculating families only |
| `I : OrderedActions ν` underlying action vector | TYPING | MAIN (3), four threshold exports |
| `I` carrier: each action positive | SOURCE | MAIN action chamber (3) |
| `I` carrier: axes strictly ordered | SOURCE | MAIN action chamber (3) |
| `i : Fin n` | TYPING | Pair threshold and per-planet characterizations |
| `j : Fin n` | TYPING | The two pair-threshold exports |
| `hij : i < j` | SOURCE | MAIN (3), the two pair-threshold exports |
| `hn : 2 ≤ n` | STANDING | MAIN §1, cross/strong-threshold minima |
| `z` underlying physical phase | TYPING | MAIN (2), canonical or L16 osculating family |
| `z` carrier: each mass positive | SOURCE | MAIN (2)/L16 |
| `z` carrier: each star position nonzero | SOURCE | MAIN (2)/L16 |
| `z` carrier: each canonical energy negative | SOURCE | Canonical family, MAIN (2) |
| `z` carrier: μ positive | SOURCE | Osculating family, MAIN L16 |
| `z` carrier: each osculating energy negative | SOURCE | Osculating family, MAIN L16 source domain |
| `z` carrier: each osculating eccentricity <1 | SOURCE | Osculating family, MAIN L16 nondegenerate ellipse domain |

All 34 family-specific signatures have been checked against the approved statements and the
providers: EXCESS 0, RULED extra premises 0, conclusion-shaped hypotheses 0. Each pair-threshold
export has TYPING 5 and SOURCE 3; each cross/strong threshold export has TYPING 3, SOURCE 2
and STANDING 1. Canonical per-planet exports have TYPING 4 and SOURCE 3, canonical aggregate
exports TYPING 3 and SOURCE 3. Osculating per-planet exports have TYPING 5 and SOURCE 5.
No classical choice of an orbit or minimizer was introduced at the seal. `IsLeast` and unique
value characterization certify the scalar minimum, without asserting a unique eccentricity
minimizer. The two sibling copies are private proved lemmas, never hypotheses.

## Approved-object raw SHA-256 table

Recomputed by the auditor from git objects; installed bytes are compared after the two
literal substitutions and, only for the 39 theorem anchors, proof-region normalization.
All 128 file digests were also independently passed through `sha256sum` and matched the
pinned revision-1 verification record.

```text
45562cb9d9dbac3e230b519f306050e3dbef1f191812cc5f0613006eb4515def  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/ActionAxis.lean.txt
41813632236e667231f339ee6f3c631777463265e4641cb04dd847ee666eb9b9  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/Chamber.lean.txt
9db41fee9c0ca4bf899eb4c3db7fee34dd836385ce2b928975341abccb4e968e  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/EccDeficit.lean.txt
719ed9291a50a21c105e0b7c6a50ea6133282b94ec3592570c72c986ecb1b97f  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/PairFeasible.lean.txt
4bb4e1a3735f79913d43e7e1363a17c9b81001caf195dce1411acb38db4e1663  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/PairObjective.lean.txt
d43801ab244a2c23c1dab370811f111bc2af0a8b5643adeb7363a79585811191  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/PairThreshold.lean.txt
81778d63da9fa4922e502ab05b7bfedb8cf33bb1f11e75865e667850db3467a5  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/AdjIdx.lean.txt
34cfa5827c8eab8b0b84bf0dca08ef5f0b8d8d12c997e5e055a8de8fd020553d  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/AdjIdxUpperIdx.lean.txt
44b7db16e8e16c8712e2787c7053fde74b1e76d07f9e3ab2202aecef11932681  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/OrderedActions.lean.txt
72663f2d80b49453bf650010b737f0de146335dfe5016d6f44a90011fa209c3c  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/OrderedPairThreshold.lean.txt
eae8820d0d4fce8450d79d2fa41ee800aaf0a2066e737045a33c8de3fdc268da  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/OrderedCrossThreshold.lean.txt
67d751fb8c60e02f039c93006b49cf43504686faec89d08aa91ce2abec2e008a  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/OrderedStrongThreshold.lean.txt
3ee732a67ba755553517a917f8776853f70178c9e9e461ba74e637e4393c741a  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/StrongAMD.lean.txt
d593032eab9cf449c5f08ae56a193d140f7a339de54af22547a53dfca0a2d161  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/KeplerPeri.lean.txt
e7f21727f94d1197f6ba569e1b2606696a8deb96ba128a22d9972ebf1bdd91e6  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/KeplerApo.lean.txt
316093ef96f5d09b04c982b2e8b202c82234e9a5b7258cbb5a42a255c8e79255  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/OscVelocity.lean.txt
b34e8c78d2875371ad8c562454fa547ee18b994004cdb865bd16a4f6f5d85844  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/OscParam.lean.txt
baa3597969c17e876de5b3e9182b732cbac16b7bc59f9dfa34d65f9a69e64cd8  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/OscEnergy.lean.txt
75e0f2753d65458396efaeefdcf06cc8c7ef3d43dadc273846bc05cf0f9927c4  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/OscAxis.lean.txt
0e3ddba0208fd9ea495daf3c2211833540d213ff98cbf6d4995642c1e1654949  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/OscEccVector.lean.txt
69b2cb9ed88c7aea95cfc22b7a0a0f953981af5d4667179efa6fd45bd1db8fd7  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/OscEcc.lean.txt
9d95bcdf1757d48cd08e6abf370c644ca7fea3676bed48df0d914c461337d47d  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/OscPeri.lean.txt
38955b313364a7d5836b1d19406db623a9e3730daa03abb85e92f7358168e9b4  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/OscApo.lean.txt
b712f070cda9f5b92ccdb6f9e8ce9ceb73837193c8dd6a221a1ab9f0865ff043  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/SourceCanonicalPhase.lean.txt
09218bca19bdf92fc3cf19d851dfe1e30db008e50f45aeeb7551c7f1194a62ba  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/SourceOsculatingPhase.lean.txt
9956baf8aa1783affa72564695369a831f53b7566542f84db61855220f66930c  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/SourceStrongAMD.lean.txt
7fde2f9beb8e137ae7ac89ac2964c002f0a4016153f529f85d7ce5aa3021f810  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/SourceKeplerPeri.lean.txt
0475743e9a88e2b52ae930ed8ac699c12598699d2cdd550f4de04d32b679f90b  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/SourceKeplerApo.lean.txt
e04103f3c46bc282569848da90ac5287f4be4de90162017618ca2ddf7f60a117  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscVelocity.lean.txt
861a34708ff2cd30e06fe5baa51506b1d774d2108f3ac4d6a930d1ec81c3dafc  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscParam.lean.txt
62b704deeff396924899b15ad13b4c1e49152854c44fcb60523449ccf19e5dc2  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscEnergy.lean.txt
a74e9aa6d585b00867f827f953c72c211f7f101de0fbe721863060fd3206093b  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscAxis.lean.txt
3af0158aee2f588b94d2e7078771656ec8817af656ec99178497b10b3f6beff7  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscEccVector.lean.txt
aa8bf762593f8d2cf911d62f1a8365fa6469bd26cd331fe5934b617e1ceaeb94  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscEcc.lean.txt
080d479e9ea6d29a92c57514dd5a227e4802fb8d40c1ae0c8f22ff6037345d40  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscPeri.lean.txt
4b61d86c089c97e1883749c05875835ec50a1b4c46af0bb2a43409609234477c  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscApo.lean.txt
bd3bb69cbf4c494cbd89c7d1b6d836217df2c2aba8d90e2fb8d7e26b37d96ef1  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpaceDot.lean.txt
a3c7f33aff9603838eb4cb4dce50216277464d6040b74b9afd2cedc50a8f145b  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpaceSq.lean.txt
759126ff46a6e06fa3a40ad3f5ee29d2f678e6f602d3c5edea04d93de659b380  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpaceLength.lean.txt
f19b76568450526d90497584b58408adb0d56abd3783cd0ebabd4cd1525f30ce  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpaceCross.lean.txt
4d5d6e98955db3ce546956191be69af7345d1f5b57526c5e8e6621f11a024b55  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/BodyVector3.lean.txt
26d75a20f126a739bb24ea7e5c8b25edec8da17b96f2d97c143dc11188e1bc0e  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/PlanetAngularMomentum3.lean.txt
ceb02a9b4ae97844f516fa97ae8c2068847eefa4a1e283fca1284250a8b9eb08  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/AngularMomentum3.lean.txt
bdb765fd2ecf72e8c44f06c394362a3637efcb9163c091b0e5958d67df87df24  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialHamiltonian.lean.txt
691a8eacb3d09d04a90af69a351b2388966ffe2a675481d1f8b30c93e4793e62  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialNoCollision.lean.txt
5c837d440459fee2408c8cf4f0c6df09146a1f771538e6eeac727c7fbc1dde08  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/IsSpatialMovingSolutionOn.lean.txt
0b7d6132b67f9a7ac3135e7d64987308b8de4a8a5a068bf49525c5ebb994ea6a  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialMovingUniqueOn.lean.txt
26ae35fc1dbeaab2c3e006c392c9751acd95ec9fbfff3352bcc8914f8b038240  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialBarycentricPositions.lean.txt
112cb4515465de509948f8c7e2026546402d5f166f0c07505f2f8700cc491d2f  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialBarycentricVelocities.lean.txt
760a36f1ed5df6fc1b670429baa9974752c966213a79cacfc260d8e01571cd81  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialMasses.lean.txt
fbfff5ba4f0c9309bd47ae2e3d9986cf95049bee98a55ab59063932dcac405de  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/IsSpatialNewtonSolutionOn.lean.txt
2f4d1a498b1ef2e55d5e53f05d3348d8837e97c65bc6da1419401f82ab67b3bf  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerEnergy.lean.txt
92a851c479df688500388129201c019d4a9e011aa02924597cab43b5e66fe778  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerAxis.lean.txt
a3cae2838e26f49003f8184b962944b5b914824b63943b51ec0b20092638a8b3  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerAction.lean.txt
6c31b6f62065d67b8764e88c38dc014a1463778c5eb602c8cb13198e65d01386  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerEccVector.lean.txt
5303eede186c637e51a53e55f4d2d3bc32c6d3730662a32d4af64a34e721d9b3  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialNegativeEnergy.lean.txt
392a8c7a5ec27d25f46229355f826e6db8d58e300f9ea2fdd7f85d638730ce14  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialElliptic.lean.txt
b6e18b290f0baa2084e90fad6182b12814b42406d60a6ca5d901a11d2400222c  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerPeri.lean.txt
2ad30856785136b0568595a55fd117de1d7ca6ee289ad756ed991e16858cb910  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerApo.lean.txt
2a9e3d53efffd30527db96e614098389e6a5551f83aa6c95c9fe97b6f834c9ab  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialOscVelocity.lean.txt
ef4ca8bec55febfdae8562bf3f1a029781ac9fbec202493097091319298bd372  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialOscParam.lean.txt
f1f2469d6e6b30004773215e675aad46a1b32730d5c67d792eba89006e489096  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialOscEnergy.lean.txt
3831fd08ab7e14c56f37df37f03f7b8bbb5f9bc4c38b57b67c6d00fb7b1039b1  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialOscAxis.lean.txt
5b496a73ce06b3e0c77c0035040dc3e3d953767d94b14f4ebe48bd30abc257a3  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialOscEccVector.lean.txt
d8cea5d7d0bd42e219825dc04a64cd55e52d63599898e44770d00d3be65e67f5  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialOscEcc.lean.txt
f5070777ea9d17603c236dddc2556e680065c693eaaab092a8065a1fcd468e12  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialOscPeri.lean.txt
5d5444f8f942757001fe53d4270a85cdf7d3197c47873a7aa7b16d71c52b1f96  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialOscApo.lean.txt
906de901c5b0c0596a0e34c0f05966f02644475d5206363c57c7828eee1e071b  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialOscPhase.lean.txt
94e7885cce423029b8c47198acf0258bd8b0349529ad8e7fbe8a2b402f1d5ee7  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceCanonicalPhase.lean.txt
9b6ee0efebbca9e99eb0c706af00239e7e7ffa49eef7bb208c7bb7587b8877af  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOsculatingPhase.lean.txt
7a84d098a6f218e2f6f96ca21eb7fdb803b265b4334f1a132ee5c3874a1e5408  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerAxis.lean.txt
bf80fa1b7c8f27d2bbc23137e3d3ff919aedc445c042ed47024848b0669b3025  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerAction.lean.txt
156b8998ee409908a4ae7bd849f5dd6a08202b049f3a006a6ca3243173b05d24  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerEccVector.lean.txt
e63353bc2af09853743b6f69bb86a987e980fba0143ae78ed74a14dba50a3c60  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerEcc.lean.txt
a74eacd5be976c9f41fb4f6068526f65046de9ea006f9d76f36d00bdddde4e2a  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialSourcePlanetAngularMomentum.lean.txt
704addb3cba46c595072146aa8776b4cb43f0fb055f4a7c27bb61f137e51d294  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceAngularMomentum.lean.txt
0286bd24cc47a22e4877ef20b1079b3008b57027d06fc31646bbab56a85fe7e1  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceStrongAMD.lean.txt
8eaeeb3786b44d1d4266a1e0c28110ac6023ff9db5fb86a4ed1fc73b55dc7176  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerPeri.lean.txt
023f08f1c32ed3480baa791c51597dfb370e1c852eee6f5311670e55573f9e3a  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerApo.lean.txt
371b2197fc7c1c42afa419cfe3e59b55201081583024fb92c6f264a6695c02e4  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscVelocity.lean.txt
6d54b525ac031b064496e0778af1399773bb4b14c82721923d83f69f427ae7f9  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscParam.lean.txt
ca350350a2c7c5ce3c413b1f260ecb23e226b5dd933774528f5bedc188babd08  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscEnergy.lean.txt
62fdc7ad7d8e8183578fdc560cc23f88d101d8c1c35fc28d8fb4913adc2cbf0d  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscAxis.lean.txt
0599a23fd0f75b43aa99865409ee8cdc14b64083287d2e352132ce41b6170f0e  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscEccVector.lean.txt
7d8ad4f616107348a2eec97db898e72bd6aba5dca26c7f24b926a5a3afc61c71  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscEcc.lean.txt
5d5001830983bae49e16811ebb1c50f75f09eecc437fcee99325e190c81c8d39  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscPeri.lean.txt
58b9678a950a95cce2ac488a662d0cf6bccfb53979da4c3f333216654ea10a7b  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscApo.lean.txt
4eedae89b53f87bd561848ff5abba7aa7b303e78abe5726f18cebe9fda8276a7  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceBarycentricPositions.lean.txt
66131bbe66cced31d9adeace23acd18bc17d32d8b9fb3a2d24c369cdccadac33  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceBarycentricVelocities.lean.txt
5f40bbea12803f06ffe169be59be73c2bc32b7cdabe9a3196298a987b132b6b1  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Theorems/OrderedPairThresholdIsLeast.lean.txt
4de6b22ce92b696e4042a540264252c153b2de442262a959dcf4fe2d7c64f84d  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Theorems/OrderedPairThresholdExistsUniqueValue.lean.txt
6538efcf4ccc8ab8763b7015f8974805318b9ec09d9207b69d827c00cec39ddc  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Theorems/OrderedCrossThresholdIsLeast.lean.txt
0aa28696820e65f3d0873707d004da8c4c85cf2d324bdbdd217a3f4a0104f748  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Theorems/OrderedStrongThresholdIsLeast.lean.txt
989a7fdeceb8fa6d17d21d46a128d2113086777664b10aab8df319148e4ef3ed  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Theorems/SourceStrongAMDNonneg.lean.txt
2b11cb1f7fc921f21a55a58e40ac3ce04ee0db52c25111f70b8365f75cc45142  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Theorems/SumActionMulEccDeficitLeSourceStrongAMD.lean.txt
c9adf8bb75e938d2ff3a85dffb4a4e645a1ce9d9e3ab11fafba762ff0ab79a8c  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Theorems/SourceKeplerAxisPos.lean.txt
750b90f6cba58c9896e73062a45725e47458b649b1d07ed5909becbc63c7a1d0  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Theorems/SourceKeplerEccLeOne.lean.txt
b49de10535edb47e9953aaf7d145c3d45ee16aff0e8614e92d46c19b0ff06405  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Theorems/SourceKeplerPeriLePlaneLength.lean.txt
bd187c6c070a54c65c0bbee046b8144b910980f5d670dc89eacbb2dd277fc625  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Theorems/PlaneLengthLeSourceKeplerApo.lean.txt
9423ec80104154276eb92596ed5e14f08850c3ff475d5d97dd68417582240460  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Theorems/SourceOscAxisPos.lean.txt
4a81394364fb18d36a4bfaeff2930d2e51d3b7c83fa47a2ddd272aef7f3066eb  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Theorems/SourceOscPeriPos.lean.txt
8d75dcdd136d700f03483f21b3264844fd17d7baa8f6398e8478d5e7860d92d8  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Theorems/SourceOscPeriLePlaneLength.lean.txt
005d08f143826e71a199235a8fbb9011072bea3814235471489362b4c0dbdc7f  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Theorems/PlaneLengthLeSourceOscApo.lean.txt
c9754af8064003b6288a4e8f4ca77b657eb7279250faa1bca3cbaceb63645d85  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerAxisPos.lean.txt
3c728238075e405a45e33892d3d9b447cc43316da5d913f58e955d92575b18ef  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerActionPos.lean.txt
51caf9c54f6b8fcc4b93e1a836aa524d9add2f835c8226b2d6fd606c2f089d1b  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerActionSq.lean.txt
fa190719f835861588da78d3e29c82b28693e0f752c59715325a81f3c556377c  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerEccSq.lean.txt
3c9a6bdb379d5be56b9c51260f0f58c5ed2f5473746bce87e67c20dff1eb1b77  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerEccNonneg.lean.txt
722ea6cada0b45f469c2e080c1b9c07e180178e460e97b19f545ffc2ad6ec8c6  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerEccLeOne.lean.txt
309c4b8a3b4f8351970311558ed69e37fe9a9f57727a9ed738b2dd2e55b02e9c  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourcePlanetAngularMomentumLength.lean.txt
459b7d96c427103a75859deed4291e38aed0a65a73a3a9df30c4c72512fb3e2a  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourcePlanetAngularMomentumLengthLe.lean.txt
18a4c8e82155d4becf36b7a039ebd56cab1c0bafe83e5d0820cc54cc0b1f7841  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerPeriLeLength.lean.txt
f60239ae12cdfb8366d73cb2dedfb0cae2a144047bdc6bd0f76d17a0c37aa391  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerApoGeLength.lean.txt
8895f41419db699592c840a6fabca6555cd6c0018b9f4454e07d7f3a03e41128  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceStrongAMDNonneg.lean.txt
eb784b11a4e504e9a1691eaa1ddad604aa4e5545f6a2abd7102b76683f8ef9cd  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceActionMulEccDeficitLe.lean.txt
cfeecc6a32ce7ec4c0dc32c62fdf4dbf8f2452710814b61cadb32fbdf7bcb05a  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscParamPos.lean.txt
28dbff3e5c08c36346d171149652cf145966a37d483b4150b89d2c202bbda34d  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscEnergyNeg.lean.txt
84cc1c749c0794cf924a7888d39d54981be1819f4579542c68525ed28ca75ff9  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscEccLtOne.lean.txt
eff3bd0adbd20e96a6ad7bb60192dc751c8c2e5a3605f38bf646e3c55b46c849  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscEccNonneg.lean.txt
871b6828cd44b93946d7d531cd503ce1f4cc2341324f1118608a4241fccbab4d  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscAxisPos.lean.txt
9fe05eb9ba9b5c4c443f3491a3cebb5b7d94bcea4715796ac1be053211ae8a48  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscPeriPos.lean.txt
acf0fb738a0107ef07696872590a1388ea69b09e58548cdde3f0b7ab4f3531de  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscPeriLeLength.lean.txt
b9b7163305bbd97ea5f688adfdbd57bb4dcd118e5ec9cf2fc40e541b7bffb631  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscApoGeLength.lean.txt
9225cd300094fd5a8c94b1169357408faeebd479e492798c1735e9e59575dc47  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDBarrier.lean.txt
905551e7500bdd04536a665cccecf27fa97c84a1b517c74fffb45e7d86470da6  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafety.lean.txt
12200cc6d69d94039471ca13b620d971ad6e27be4de7d5c76945462104a90ad4  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafetyHalfInteger.lean.txt
ac0c594150fe8b6718b733cbfee22ef9cae063a0c6f13bd4f9830a84c70ce051  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafety.lean.txt
b7d723783f413a4c7b6ae7b44bdd0228300df7cefb6a44eed9ad27227bfc5e2b  docs/tracks/LP/freeze/draft7/KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafetyHalfInteger.lean.txt
46b7dec753a746bfc5bbfb8058190c77c0bcc219748ee6ca65f68463ec7a9e33  docs/tracks/LP/freeze/draft7/manifest-entries.json
```

## Independent real-module probe output

The transient probe was generated independently from the installed manifest, imported all
128 real frozen modules, and was deleted after execution. Each pair used:

```lean
example : type_of% @Anchor := @Provider
run_cmd do
  let env ← getEnv
  let some a := env.find? ``Anchor | throwError "missing anchor"
  let some b := env.find? ``Provider | throwError "missing provider"
  unless a.type.eqv b.type do throwError "EXPR_MISMATCH"
  logInfo m!"EXPR_EQV Anchor; raw equality: {a.type == b.type}"
#print axioms Anchor
#print axioms Provider
```

Here `Anchor` and `Provider` stand for each fully qualified registered export, not aliases.
All 89 definitions were also passed to `#print axioms`. The exact output follows.

```text
EXPR_EQV KAM.Planetary.StrongAMD.orderedPairThreshold_isLeast; raw equality: true
'KAM.Planetary.StrongAMD.orderedPairThreshold_isLeast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.StrongAMD.orderedPairThreshold_isLeast' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXPR_EQV KAM.Planetary.StrongAMD.orderedPairThreshold_existsUnique_value; raw equality: true
'KAM.Planetary.StrongAMD.orderedPairThreshold_existsUnique_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Provider.Planetary.StrongAMD.orderedPairThreshold_existsUnique_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXPR_EQV KAM.Planetary.StrongAMD.orderedCrossThreshold_isLeast; raw equality: true
'KAM.Planetary.StrongAMD.orderedCrossThreshold_isLeast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.StrongAMD.orderedCrossThreshold_isLeast' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXPR_EQV KAM.Planetary.StrongAMD.orderedStrongThreshold_isLeast; raw equality: true
'KAM.Planetary.StrongAMD.orderedStrongThreshold_isLeast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.StrongAMD.orderedStrongThreshold_isLeast' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXPR_EQV KAM.Planetary.StrongAMD.sourceStrongAMD_nonneg; raw equality: true
'KAM.Planetary.StrongAMD.sourceStrongAMD_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.StrongAMD.sourceStrongAMD_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
EXPR_EQV KAM.Planetary.StrongAMD.sum_action_mul_eccDeficit_le_sourceStrongAMD; raw equality: true
'KAM.Planetary.StrongAMD.sum_action_mul_eccDeficit_le_sourceStrongAMD' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Provider.Planetary.StrongAMD.sum_action_mul_eccDeficit_le_sourceStrongAMD' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXPR_EQV KAM.Planetary.StrongAMD.sourceKepler_axis_pos; raw equality: true
'KAM.Planetary.StrongAMD.sourceKepler_axis_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.StrongAMD.sourceKepler_axis_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
EXPR_EQV KAM.Planetary.StrongAMD.sourceKepler_ecc_le_one; raw equality: true
'KAM.Planetary.StrongAMD.sourceKepler_ecc_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.StrongAMD.sourceKepler_ecc_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
EXPR_EQV KAM.Planetary.StrongAMD.sourceKeplerPeri_le_planeLength; raw equality: true
'KAM.Planetary.StrongAMD.sourceKeplerPeri_le_planeLength' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.StrongAMD.sourceKeplerPeri_le_planeLength' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXPR_EQV KAM.Planetary.StrongAMD.planeLength_le_sourceKeplerApo; raw equality: true
'KAM.Planetary.StrongAMD.planeLength_le_sourceKeplerApo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.StrongAMD.planeLength_le_sourceKeplerApo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXPR_EQV KAM.Planetary.StrongAMD.sourceOscAxis_pos; raw equality: true
'KAM.Planetary.StrongAMD.sourceOscAxis_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.StrongAMD.sourceOscAxis_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
EXPR_EQV KAM.Planetary.StrongAMD.sourceOscPeri_pos; raw equality: true
'KAM.Planetary.StrongAMD.sourceOscPeri_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.StrongAMD.sourceOscPeri_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
EXPR_EQV KAM.Planetary.StrongAMD.sourceOscPeri_le_planeLength; raw equality: true
'KAM.Planetary.StrongAMD.sourceOscPeri_le_planeLength' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.StrongAMD.sourceOscPeri_le_planeLength' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXPR_EQV KAM.Planetary.StrongAMD.planeLength_le_sourceOscApo; raw equality: true
'KAM.Planetary.StrongAMD.planeLength_le_sourceOscApo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.StrongAMD.planeLength_le_sourceOscApo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXPR_EQV KAM.Planetary.Spatial.spatialSourceKeplerAxis_pos; raw equality: true
'KAM.Planetary.Spatial.spatialSourceKeplerAxis_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.Spatial.spatialSourceKeplerAxis_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
EXPR_EQV KAM.Planetary.Spatial.spatialSourceKeplerAction_pos; raw equality: true
'KAM.Planetary.Spatial.spatialSourceKeplerAction_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.Spatial.spatialSourceKeplerAction_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXPR_EQV KAM.Planetary.Spatial.spatialSourceKeplerAction_sq; raw equality: true
'KAM.Planetary.Spatial.spatialSourceKeplerAction_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.Spatial.spatialSourceKeplerAction_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
EXPR_EQV KAM.Planetary.Spatial.spatialSourceKeplerEcc_sq; raw equality: true
'KAM.Planetary.Spatial.spatialSourceKeplerEcc_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.Spatial.spatialSourceKeplerEcc_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
EXPR_EQV KAM.Planetary.Spatial.spatialSourceKeplerEcc_nonneg; raw equality: true
'KAM.Planetary.Spatial.spatialSourceKeplerEcc_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.Spatial.spatialSourceKeplerEcc_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXPR_EQV KAM.Planetary.Spatial.spatialSourceKeplerEcc_le_one; raw equality: true
'KAM.Planetary.Spatial.spatialSourceKeplerEcc_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.Spatial.spatialSourceKeplerEcc_le_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXPR_EQV KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length; raw equality: true
'KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Provider.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXPR_EQV KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length_le; raw equality: true
'KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Provider.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXPR_EQV KAM.Planetary.Spatial.spatialSourceKeplerPeri_le_length; raw equality: true
'KAM.Planetary.Spatial.spatialSourceKeplerPeri_le_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.Spatial.spatialSourceKeplerPeri_le_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXPR_EQV KAM.Planetary.Spatial.spatialSourceKeplerApo_ge_length; raw equality: true
'KAM.Planetary.Spatial.spatialSourceKeplerApo_ge_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.Spatial.spatialSourceKeplerApo_ge_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXPR_EQV KAM.Planetary.Spatial.spatialSourceStrongAMD_nonneg; raw equality: true
'KAM.Planetary.Spatial.spatialSourceStrongAMD_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.Spatial.spatialSourceStrongAMD_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXPR_EQV KAM.Planetary.Spatial.spatialSourceAction_mul_eccDeficit_le; raw equality: true
'KAM.Planetary.Spatial.spatialSourceAction_mul_eccDeficit_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.Spatial.spatialSourceAction_mul_eccDeficit_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXPR_EQV KAM.Planetary.Spatial.spatialSourceOscParam_pos; raw equality: true
'KAM.Planetary.Spatial.spatialSourceOscParam_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.Spatial.spatialSourceOscParam_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
EXPR_EQV KAM.Planetary.Spatial.spatialSourceOscEnergy_neg; raw equality: true
'KAM.Planetary.Spatial.spatialSourceOscEnergy_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.Spatial.spatialSourceOscEnergy_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
EXPR_EQV KAM.Planetary.Spatial.spatialSourceOscEcc_lt_one; raw equality: true
'KAM.Planetary.Spatial.spatialSourceOscEcc_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.Spatial.spatialSourceOscEcc_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
EXPR_EQV KAM.Planetary.Spatial.spatialSourceOscEcc_nonneg; raw equality: true
'KAM.Planetary.Spatial.spatialSourceOscEcc_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.Spatial.spatialSourceOscEcc_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
EXPR_EQV KAM.Planetary.Spatial.spatialSourceOscAxis_pos; raw equality: true
'KAM.Planetary.Spatial.spatialSourceOscAxis_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.Spatial.spatialSourceOscAxis_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
EXPR_EQV KAM.Planetary.Spatial.spatialSourceOscPeri_pos; raw equality: true
'KAM.Planetary.Spatial.spatialSourceOscPeri_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.Spatial.spatialSourceOscPeri_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
EXPR_EQV KAM.Planetary.Spatial.spatialSourceOscPeri_le_length; raw equality: true
'KAM.Planetary.Spatial.spatialSourceOscPeri_le_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.Spatial.spatialSourceOscPeri_le_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXPR_EQV KAM.Planetary.Spatial.spatialSourceOscApo_ge_length; raw equality: true
'KAM.Planetary.Spatial.spatialSourceOscApo_ge_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.Spatial.spatialSourceOscApo_ge_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXPR_EQV KAM.Planetary.StrongAMD.planar_strongAMD_barrier; raw equality: true
'KAM.Planetary.StrongAMD.planar_strongAMD_barrier' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.StrongAMD.planar_strongAMD_barrier' depends on axioms: [propext, Classical.choice, Quot.sound]
EXPR_EQV KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety; raw equality: true
'KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.StrongAMD.planar_strongAMD_exponentialSafety' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXPR_EQV KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_halfInteger; raw equality: true
'KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_halfInteger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Provider.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_halfInteger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXPR_EQV KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety; raw equality: true
'KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.Spatial.spatial_strongAMD_exponentialSafety' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXPR_EQV KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety_halfInteger; raw equality: true
'KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety_halfInteger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Provider.Planetary.Spatial.spatial_strongAMD_exponentialSafety_halfInteger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Planetary.StrongAMD.actionAxis' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.chamber' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.eccDeficit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.pairFeasible' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.pairObjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.pairThreshold' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.AdjIdx' does not depend on any axioms
'KAM.Planetary.StrongAMD.AdjIdx.upperIdx' does not depend on any axioms
'KAM.Planetary.StrongAMD.OrderedActions' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.orderedPairThreshold' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.orderedCrossThreshold' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.orderedStrongThreshold' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.strongAMD' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.keplerPeri' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.keplerApo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.oscVelocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.oscParam' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.oscEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.oscAxis' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.oscEccVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.oscEcc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.oscPeri' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.oscApo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.SourceCanonicalPhase' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.SourceOsculatingPhase' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.sourceStrongAMD' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.sourceKeplerPeri' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.sourceKeplerApo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.sourceOscVelocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.sourceOscParam' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.sourceOscEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.sourceOscAxis' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.sourceOscEccVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.sourceOscEcc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.sourceOscPeri' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.sourceOscApo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spaceDot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spaceSq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spaceLength' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spaceCross' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.bodyVector3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.planetAngularMomentum3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.angularMomentum3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.SpatialNoCollision' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.IsSpatialMovingSolutionOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.SpatialMovingUniqueOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialBarycentricPositions' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialBarycentricVelocities' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialMasses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.IsSpatialNewtonSolutionOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialKeplerEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialKeplerAxis' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialKeplerAction' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialKeplerEccVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.SpatialNegativeEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.SpatialElliptic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialKeplerPeri' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialKeplerApo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialOscVelocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialOscParam' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialOscEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialOscAxis' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialOscEccVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialOscEcc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialOscPeri' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialOscApo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.SpatialOscPhase' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.SpatialSourceCanonicalPhase' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.SpatialSourceOsculatingPhase' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialSourceKeplerAxis' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialSourceKeplerAction' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialSourceKeplerEccVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialSourceKeplerEcc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialSourceAngularMomentum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialSourceStrongAMD' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialSourceKeplerPeri' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialSourceKeplerApo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialSourceOscVelocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialSourceOscParam' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialSourceOscEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialSourceOscAxis' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialSourceOscEccVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialSourceOscEcc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialSourceOscPeri' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialSourceOscApo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialSourceBarycentricPositions' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialSourceBarycentricVelocities' depends on axioms: [propext, Classical.choice, Quot.sound]


PROBE_EXIT 0
EXPR_EQV_COUNT 39
RAW_TRUE_COUNT 39
THEOREM_AXIOM_MISMATCHES []
DEFINITION_AXIOM_MISMATCHES []
INDEPENDENT_PROBE_ALL_OK: 39 pairs, 78 theorem axiom sets, 89 definition axiom sets

```


## Commit C and independent ABI receipts

Updated with `git checkout --detach inp-lp-freeze` after the orchestrator confirmed the build
snapshot was synced. Commit C changes exactly eight paths: the manifest, FREEZE.md,
MANIFEST-CHANGES.md, two audit scripts and three textual check artifacts. The only manifest
changes are the 128 new `abi_sha256` fields. No frozen, provider, implementation or generated
root bytes change. All earlier source-byte checks therefore remain valid at this HEAD.

The auditor reran identity and generated-root checks (exit 0 each), reconstructed all 128
manifest entries with the guard's code and approval-D62.json (zero differences), rechecked
the 179 pinned existing entries (all unchanged), and checked all 128 D62 record rows against
the installed bytes (zero mismatches).

Two independently executed capped calls of `scripts/abi_hashes.py` on a transient manifest
containing exactly the 128 approved LP entries produced:

```text
ABI_RUN 1 EXIT 0
ABI_MISMATCHES []
ABI_RUN 2 EXIT 0
ABI_MISMATCHES []
TWO_ABI_RUNS_IDENTICAL True
REPRODUCED_ABI_EXPORTS 128
ABI_JSON_SHA256 dccbab3c1cd182241c09ffaf8cdb7d512933388d4085fd5f04b2e850ceee6422
```

The digest is SHA-256 of `json.dumps(result, sort_keys=True).encode()`. Each call was
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env
LEAN_NUM_THREADS=1 python3 -B -I scripts/abi_hashes.py <worktree> <filtered-manifest>`.
The repository tool launches `lake env lean` inside that same scope. The manifest and the
tool's Lean scratch file were deleted afterwards. No certificate library was selected.

## Author partial kernel receipt (copied verbatim)

Read from `/root/code/KAM-inp-lp-freeze/.drafts/exec/replay.out` after the binding
orchestrator stop. These are supporting author receipts, distinct from the independent
auditor replay. The authoritative complete 284-module replay belongs to landing.

```text
KAM.Frozen.Planetary.Spatial.Defs.AngularMomentum3 replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.BodyVector3 replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.IsSpatialMovingSolutionOn replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.IsSpatialNewtonSolutionOn replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.PlanetAngularMomentum3 replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpaceCross replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpaceDot replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpaceLength replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpaceSq replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialBarycentricPositions replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialBarycentricVelocities replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialElliptic replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialHamiltonian replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialKeplerAction replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialKeplerApo replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialKeplerAxis replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialKeplerEccVector replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialKeplerEnergy replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialKeplerPeri replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialMasses replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialMovingUniqueOn replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialNegativeEnergy replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialNoCollision replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialOscApo replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialOscAxis replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialOscEcc replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialOscEccVector replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialOscEnergy replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialOscParam replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialOscPeri replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialOscPhase replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialOscVelocity replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceAngularMomentum replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceBarycentricPositions replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceBarycentricVelocities replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceCanonicalPhase replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceKeplerAction replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceKeplerApo replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceKeplerAxis replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceKeplerEcc replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceKeplerEccVector replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceKeplerPeri replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscApo replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscAxis replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscEcc replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscEccVector replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscEnergy replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscParam replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscPeri replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscVelocity replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOsculatingPhase replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialSourcePlanetAngularMomentum replay exit 0
KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceStrongAMD replay exit 0
KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceActionMulEccDeficitLe replay exit 0
KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceKeplerActionPos replay exit 0
KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceKeplerActionSq replay exit 0
KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceKeplerApoGeLength replay exit 0
KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceKeplerAxisPos replay exit 0
KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceKeplerEccLeOne replay exit 0
KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceKeplerEccNonneg replay exit 0
KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceKeplerEccSq replay exit 0
KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceKeplerPeriLeLength replay exit 0
KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceOscApoGeLength replay exit 0
KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceOscAxisPos replay exit 0
KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceOscEccLtOne replay exit 0
KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceOscEccNonneg replay exit 0
KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceOscEnergyNeg replay exit 0
KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceOscParamPos replay exit 0
KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceOscPeriLeLength replay exit 0
KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceOscPeriPos replay exit 0
KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourcePlanetAngularMomentumLength replay exit 0
KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourcePlanetAngularMomentumLengthLe replay exit 0
KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceStrongAMDNonneg replay exit 0
KAM.Frozen.Planetary.Spatial.Theorems.SpatialStrongAMDExponentialSafety replay exit 0
KAM.Frozen.Planetary.Spatial.Theorems.SpatialStrongAMDExponentialSafetyHalfInteger replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.ActionAxis replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.AdjIdx replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.AdjIdxUpperIdx replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.Chamber replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.EccDeficit replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.KeplerApo replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.KeplerPeri replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.OrderedActions replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.OrderedCrossThreshold replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.OrderedPairThreshold replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.OrderedStrongThreshold replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.OscApo replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.OscAxis replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.OscEcc replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.OscEccVector replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.OscEnergy replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.OscParam replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.OscPeri replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.OscVelocity replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.PairFeasible replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.PairObjective replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.PairThreshold replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.SourceCanonicalPhase replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.SourceKeplerApo replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.SourceKeplerPeri replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscApo replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscAxis replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscEcc replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscEccVector replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscEnergy replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscParam replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscPeri replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscVelocity replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.SourceOsculatingPhase replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.SourceStrongAMD replay exit 0
KAM.Frozen.Planetary.StrongAMD.Defs.StrongAMD replay exit 0
KAM.Frozen.Planetary.StrongAMD.Theorems.OrderedCrossThresholdIsLeast replay exit 0
KAM.Frozen.Planetary.StrongAMD.Theorems.OrderedPairThresholdExistsUniqueValue replay exit 0
KAM.Frozen.Planetary.StrongAMD.Theorems.OrderedPairThresholdIsLeast replay exit 0
KAM.Frozen.Planetary.StrongAMD.Theorems.OrderedStrongThresholdIsLeast replay exit 0
KAM.Frozen.Planetary.StrongAMD.Theorems.PlanarStrongAMDBarrier replay exit 0
KAM.Frozen.Planetary.StrongAMD.Theorems.PlanarStrongAMDExponentialSafety replay exit 0
KAM.Frozen.Planetary.StrongAMD.Theorems.PlanarStrongAMDExponentialSafetyHalfInteger replay exit 0
KAM.Frozen.Planetary.StrongAMD.Theorems.PlaneLengthLeSourceKeplerApo replay exit 0
KAM.Frozen.Planetary.StrongAMD.Theorems.PlaneLengthLeSourceOscApo replay exit 0
KAM.Frozen.Planetary.StrongAMD.Theorems.SourceKeplerAxisPos replay exit 0
KAM.Frozen.Planetary.StrongAMD.Theorems.SourceKeplerEccLeOne replay exit 0
KAM.Frozen.Planetary.StrongAMD.Theorems.SourceKeplerPeriLePlaneLength replay exit 0
KAM.Frozen.Planetary.StrongAMD.Theorems.SourceOscAxisPos replay exit 0
KAM.Frozen.Planetary.StrongAMD.Theorems.SourceOscPeriLePlaneLength replay exit 0
KAM.Frozen.Planetary.StrongAMD.Theorems.SourceOscPeriPos replay exit 0
KAM.Frozen.Planetary.StrongAMD.Theorems.SourceStrongAMDNonneg replay exit 0
KAM.Frozen.Planetary.StrongAMD.Theorems.SumActionMulEccDeficitLeSourceStrongAMD replay exit 0
```

## Final documentation delta and revised kernel ruling

Updated with `git checkout --detach inp-lp-freeze` to
`f5729cf8af5bfb688326d989161db2d865fbeead`. The exact delta from a4eecfc1 is:

```text
docs/tracks/LP/FREEZE.md
docs/tracks/LP/audits/LP-FREEZE-EXEC-handoff.md
docs/tracks/LP/freeze/replay-prelanding.txt
```

FREEZE.md changes only its kernel-replay receipt to state the orchestrator stop at 128/284
and the full replay at landing. The handoff accurately lists the commits, identities,
manifest, ABI, lint and probe receipts, the two private inlinings, and the same stopped-replay
scope. `replay-prelanding.txt` begins with the exact 128 lines copied from the author's live
receipt, followed only by the explicit STOPPED explanation. No KAM, manifest or root bytes
change, so the independently checked a4eecfc1 type/axiom/ABI evidence binds this final HEAD.

The later user message, relaying binding root-b8 direction, supersedes the original serial
full-replay staging: do not wait for the author's full stream; retain the author's 128-module
receipt and require the auditor's 39 theorem-anchor plus 39 provider replays with 2–3 workers,
each capped at 4 GB behind MemAvailable ≥6 GB. The authoritative replay of all 284 modules is
the lander's three-worker replay. This is an explicit revised validation boundary, not an
inferred waiver.

At that ruling the auditor had already completed all 128 frozen modules and eight providers
(136 successful receipts). The serial manager was deliberately stopped while switching
scheduling; its exit 137 is a control action, not a kernel-check failure. Any invocation
without a recorded successful result is included in the remaining-provider queue. A first
parallel-driver launch had a Python memory-gate regex parsing error before any Lean call;
it was corrected and restarted. The remaining 31 providers run with three workers under
the revised cap/gate. No frozen definition is replayed again after the revised ruling.

## Independent kernel replay receipts

The auditor independently replayed all 128 frozen modules and all 39 providers: 167 unique
modules, every recorded result exit 0. In particular the binding 39-anchor/39-provider set
is covered in full (78/78). Successful serial receipts were retained when switching to the
three-worker schedule; an interrupted invocation was requeued rather than treated as passed.
The aggregate is 136 successful serial receipts plus 31 successful parallel receipts.

Each invocation, from this worktree, was exactly:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 \
  nice -n 10 env LEAN_NUM_THREADS=1 lake env leanchecker <Module>
```

The serial calls used the 8 GB gate; the three-worker remainder used the revised 6 GB gate.
No `kernel_replay.sh --mem-gb`, fresh library build, or certificate application was used.
These receipts certify the new module set. The full 284-module landing replay remains the
lander's separately assigned gate, as the binding instruction expressly requires.

```text
REPLAY 1/167 KAM.Frozen.Planetary.Spatial.Defs.AngularMomentum3: exit 0
REPLAY 2/167 KAM.Frozen.Planetary.Spatial.Defs.BodyVector3: exit 0
REPLAY 3/167 KAM.Frozen.Planetary.Spatial.Defs.IsSpatialMovingSolutionOn: exit 0
REPLAY 4/167 KAM.Frozen.Planetary.Spatial.Defs.IsSpatialNewtonSolutionOn: exit 0
REPLAY 5/167 KAM.Frozen.Planetary.Spatial.Defs.PlanetAngularMomentum3: exit 0
REPLAY 6/167 KAM.Frozen.Planetary.Spatial.Defs.SpaceCross: exit 0
REPLAY 7/167 KAM.Frozen.Planetary.Spatial.Defs.SpaceDot: exit 0
REPLAY 8/167 KAM.Frozen.Planetary.Spatial.Defs.SpaceLength: exit 0
REPLAY 9/167 KAM.Frozen.Planetary.Spatial.Defs.SpaceSq: exit 0
REPLAY 10/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialBarycentricPositions: exit 0
REPLAY 11/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialBarycentricVelocities: exit 0
REPLAY 12/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialElliptic: exit 0
REPLAY 13/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialHamiltonian: exit 0
REPLAY 14/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialKeplerAction: exit 0
REPLAY 15/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialKeplerApo: exit 0
REPLAY 16/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialKeplerAxis: exit 0
REPLAY 17/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialKeplerEccVector: exit 0
REPLAY 18/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialKeplerEnergy: exit 0
REPLAY 19/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialKeplerPeri: exit 0
REPLAY 20/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialMasses: exit 0
REPLAY 21/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialMovingUniqueOn: exit 0
REPLAY 22/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialNegativeEnergy: exit 0
REPLAY 23/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialNoCollision: exit 0
REPLAY 24/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialOscApo: exit 0
REPLAY 25/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialOscAxis: exit 0
REPLAY 26/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialOscEcc: exit 0
REPLAY 27/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialOscEccVector: exit 0
REPLAY 28/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialOscEnergy: exit 0
REPLAY 29/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialOscParam: exit 0
REPLAY 30/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialOscPeri: exit 0
REPLAY 31/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialOscPhase: exit 0
REPLAY 32/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialOscVelocity: exit 0
REPLAY 33/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceAngularMomentum: exit 0
REPLAY 34/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceBarycentricPositions: exit 0
REPLAY 35/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceBarycentricVelocities: exit 0
REPLAY 36/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceCanonicalPhase: exit 0
REPLAY 37/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceKeplerAction: exit 0
REPLAY 38/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceKeplerApo: exit 0
REPLAY 39/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceKeplerAxis: exit 0
REPLAY 40/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceKeplerEcc: exit 0
REPLAY 41/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceKeplerEccVector: exit 0
REPLAY 42/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceKeplerPeri: exit 0
REPLAY 43/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscApo: exit 0
REPLAY 44/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscAxis: exit 0
REPLAY 45/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscEcc: exit 0
REPLAY 46/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscEccVector: exit 0
REPLAY 47/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscEnergy: exit 0
REPLAY 48/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscParam: exit 0
REPLAY 49/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscPeri: exit 0
REPLAY 50/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOscVelocity: exit 0
REPLAY 51/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOsculatingPhase: exit 0
REPLAY 52/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialSourcePlanetAngularMomentum: exit 0
REPLAY 53/167 KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceStrongAMD: exit 0
REPLAY 54/167 KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceActionMulEccDeficitLe: exit 0
REPLAY 55/167 KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceKeplerActionPos: exit 0
REPLAY 56/167 KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceKeplerActionSq: exit 0
REPLAY 57/167 KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceKeplerApoGeLength: exit 0
REPLAY 58/167 KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceKeplerAxisPos: exit 0
REPLAY 59/167 KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceKeplerEccLeOne: exit 0
REPLAY 60/167 KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceKeplerEccNonneg: exit 0
REPLAY 61/167 KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceKeplerEccSq: exit 0
REPLAY 62/167 KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceKeplerPeriLeLength: exit 0
REPLAY 63/167 KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceOscApoGeLength: exit 0
REPLAY 64/167 KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceOscAxisPos: exit 0
REPLAY 65/167 KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceOscEccLtOne: exit 0
REPLAY 66/167 KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceOscEccNonneg: exit 0
REPLAY 67/167 KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceOscEnergyNeg: exit 0
REPLAY 68/167 KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceOscParamPos: exit 0
REPLAY 69/167 KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceOscPeriLeLength: exit 0
REPLAY 70/167 KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceOscPeriPos: exit 0
REPLAY 71/167 KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourcePlanetAngularMomentumLength: exit 0
REPLAY 72/167 KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourcePlanetAngularMomentumLengthLe: exit 0
REPLAY 73/167 KAM.Frozen.Planetary.Spatial.Theorems.SpatialSourceStrongAMDNonneg: exit 0
REPLAY 74/167 KAM.Frozen.Planetary.Spatial.Theorems.SpatialStrongAMDExponentialSafety: exit 0
REPLAY 75/167 KAM.Frozen.Planetary.Spatial.Theorems.SpatialStrongAMDExponentialSafetyHalfInteger: exit 0
REPLAY 76/167 KAM.Frozen.Planetary.StrongAMD.Defs.ActionAxis: exit 0
REPLAY 77/167 KAM.Frozen.Planetary.StrongAMD.Defs.AdjIdx: exit 0
REPLAY 78/167 KAM.Frozen.Planetary.StrongAMD.Defs.AdjIdxUpperIdx: exit 0
REPLAY 79/167 KAM.Frozen.Planetary.StrongAMD.Defs.Chamber: exit 0
REPLAY 80/167 KAM.Frozen.Planetary.StrongAMD.Defs.EccDeficit: exit 0
REPLAY 81/167 KAM.Frozen.Planetary.StrongAMD.Defs.KeplerApo: exit 0
REPLAY 82/167 KAM.Frozen.Planetary.StrongAMD.Defs.KeplerPeri: exit 0
REPLAY 83/167 KAM.Frozen.Planetary.StrongAMD.Defs.OrderedActions: exit 0
REPLAY 84/167 KAM.Frozen.Planetary.StrongAMD.Defs.OrderedCrossThreshold: exit 0
REPLAY 85/167 KAM.Frozen.Planetary.StrongAMD.Defs.OrderedPairThreshold: exit 0
REPLAY 86/167 KAM.Frozen.Planetary.StrongAMD.Defs.OrderedStrongThreshold: exit 0
REPLAY 87/167 KAM.Frozen.Planetary.StrongAMD.Defs.OscApo: exit 0
REPLAY 88/167 KAM.Frozen.Planetary.StrongAMD.Defs.OscAxis: exit 0
REPLAY 89/167 KAM.Frozen.Planetary.StrongAMD.Defs.OscEcc: exit 0
REPLAY 90/167 KAM.Frozen.Planetary.StrongAMD.Defs.OscEccVector: exit 0
REPLAY 91/167 KAM.Frozen.Planetary.StrongAMD.Defs.OscEnergy: exit 0
REPLAY 92/167 KAM.Frozen.Planetary.StrongAMD.Defs.OscParam: exit 0
REPLAY 93/167 KAM.Frozen.Planetary.StrongAMD.Defs.OscPeri: exit 0
REPLAY 94/167 KAM.Frozen.Planetary.StrongAMD.Defs.OscVelocity: exit 0
REPLAY 95/167 KAM.Frozen.Planetary.StrongAMD.Defs.PairFeasible: exit 0
REPLAY 96/167 KAM.Frozen.Planetary.StrongAMD.Defs.PairObjective: exit 0
REPLAY 97/167 KAM.Frozen.Planetary.StrongAMD.Defs.PairThreshold: exit 0
REPLAY 98/167 KAM.Frozen.Planetary.StrongAMD.Defs.SourceCanonicalPhase: exit 0
REPLAY 99/167 KAM.Frozen.Planetary.StrongAMD.Defs.SourceKeplerApo: exit 0
REPLAY 100/167 KAM.Frozen.Planetary.StrongAMD.Defs.SourceKeplerPeri: exit 0
REPLAY 101/167 KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscApo: exit 0
REPLAY 102/167 KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscAxis: exit 0
REPLAY 103/167 KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscEcc: exit 0
REPLAY 104/167 KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscEccVector: exit 0
REPLAY 105/167 KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscEnergy: exit 0
REPLAY 106/167 KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscParam: exit 0
REPLAY 107/167 KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscPeri: exit 0
REPLAY 108/167 KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscVelocity: exit 0
REPLAY 109/167 KAM.Frozen.Planetary.StrongAMD.Defs.SourceOsculatingPhase: exit 0
REPLAY 110/167 KAM.Frozen.Planetary.StrongAMD.Defs.SourceStrongAMD: exit 0
REPLAY 111/167 KAM.Frozen.Planetary.StrongAMD.Defs.StrongAMD: exit 0
REPLAY 112/167 KAM.Frozen.Planetary.StrongAMD.Theorems.OrderedCrossThresholdIsLeast: exit 0
REPLAY 113/167 KAM.Frozen.Planetary.StrongAMD.Theorems.OrderedPairThresholdExistsUniqueValue: exit 0
REPLAY 114/167 KAM.Frozen.Planetary.StrongAMD.Theorems.OrderedPairThresholdIsLeast: exit 0
REPLAY 115/167 KAM.Frozen.Planetary.StrongAMD.Theorems.OrderedStrongThresholdIsLeast: exit 0
REPLAY 116/167 KAM.Frozen.Planetary.StrongAMD.Theorems.PlanarStrongAMDBarrier: exit 0
REPLAY 117/167 KAM.Frozen.Planetary.StrongAMD.Theorems.PlanarStrongAMDExponentialSafety: exit 0
REPLAY 118/167 KAM.Frozen.Planetary.StrongAMD.Theorems.PlanarStrongAMDExponentialSafetyHalfInteger: exit 0
REPLAY 119/167 KAM.Frozen.Planetary.StrongAMD.Theorems.PlaneLengthLeSourceKeplerApo: exit 0
REPLAY 120/167 KAM.Frozen.Planetary.StrongAMD.Theorems.PlaneLengthLeSourceOscApo: exit 0
REPLAY 121/167 KAM.Frozen.Planetary.StrongAMD.Theorems.SourceKeplerAxisPos: exit 0
REPLAY 122/167 KAM.Frozen.Planetary.StrongAMD.Theorems.SourceKeplerEccLeOne: exit 0
REPLAY 123/167 KAM.Frozen.Planetary.StrongAMD.Theorems.SourceKeplerPeriLePlaneLength: exit 0
REPLAY 124/167 KAM.Frozen.Planetary.StrongAMD.Theorems.SourceOscAxisPos: exit 0
REPLAY 125/167 KAM.Frozen.Planetary.StrongAMD.Theorems.SourceOscPeriLePlaneLength: exit 0
REPLAY 126/167 KAM.Frozen.Planetary.StrongAMD.Theorems.SourceOscPeriPos: exit 0
REPLAY 127/167 KAM.Frozen.Planetary.StrongAMD.Theorems.SourceStrongAMDNonneg: exit 0
REPLAY 128/167 KAM.Frozen.Planetary.StrongAMD.Theorems.SumActionMulEccDeficitLeSourceStrongAMD: exit 0
REPLAY 129/167 KAM.Provider.Planetary.Spatial.SpatialSourceActionMulEccDeficitLe: exit 0
REPLAY 130/167 KAM.Provider.Planetary.Spatial.SpatialSourceKeplerActionPos: exit 0
REPLAY 131/167 KAM.Provider.Planetary.Spatial.SpatialSourceKeplerActionSq: exit 0
REPLAY 132/167 KAM.Provider.Planetary.Spatial.SpatialSourceKeplerApoGeLength: exit 0
REPLAY 133/167 KAM.Provider.Planetary.Spatial.SpatialSourceKeplerAxisPos: exit 0
REPLAY 134/167 KAM.Provider.Planetary.Spatial.SpatialSourceKeplerEccLeOne: exit 0
REPLAY 135/167 KAM.Provider.Planetary.Spatial.SpatialSourceKeplerEccNonneg: exit 0
REPLAY 136/167 KAM.Provider.Planetary.Spatial.SpatialSourceKeplerEccSq: exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.Spatial.SpatialSourceOscApoGeLength : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.Spatial.SpatialSourceKeplerPeriLeLength : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.Spatial.SpatialSourceOscAxisPos : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.Spatial.SpatialSourceOscEnergyNeg : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.Spatial.SpatialSourceOscEccLtOne : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.Spatial.SpatialSourceOscEccNonneg : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.Spatial.SpatialSourceOscParamPos : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.Spatial.SpatialSourceOscPeriLeLength : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.Spatial.SpatialSourceOscPeriPos : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.Spatial.SpatialSourcePlanetAngularMomentumLength : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.Spatial.SpatialSourcePlanetAngularMomentumLengthLe : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.Spatial.SpatialSourceStrongAMDNonneg : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.StrongAMD.OrderedCrossThresholdIsLeast : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.Spatial.SpatialStrongAMDExponentialSafety : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.Spatial.SpatialStrongAMDExponentialSafetyHalfInteger : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.StrongAMD.OrderedPairThresholdExistsUniqueValue : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.StrongAMD.OrderedStrongThresholdIsLeast : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.StrongAMD.OrderedPairThresholdIsLeast : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.StrongAMD.PlanarStrongAMDExponentialSafety : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.StrongAMD.PlanarStrongAMDBarrier : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.StrongAMD.PlanarStrongAMDExponentialSafetyHalfInteger : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.StrongAMD.SourceKeplerAxisPos : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.StrongAMD.PlaneLengthLeSourceOscApo : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.StrongAMD.PlaneLengthLeSourceKeplerApo : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.StrongAMD.SourceKeplerEccLeOne : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.StrongAMD.SourceOscAxisPos : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.StrongAMD.SourceKeplerPeriLePlaneLength : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.StrongAMD.SourceStrongAMDNonneg : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.StrongAMD.SourceOscPeriLePlaneLength : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.StrongAMD.SourceOscPeriPos : exit 0
PARALLEL_REPLAY KAM.Provider.Planetary.StrongAMD.SumActionMulEccDeficitLeSourceStrongAMD : exit 0
INDEPENDENT_REPLAY_TOTAL 167 OK; 0 FAIL
REQUIRED_78_COVERED 78
```

## Actual statement semantic closure

A separate transient 976-line Lean probe traversed each real anchor's type, then the types
and values of every reachable `KAM.*` definition (theorems contribute their types, not
proof bodies). For every definition it obtained the defining module from the environment
and required that module's frozen path to occur in that anchor's `definition_closure`.
All 39 anchors passed. This independently discharges completeness for the statement's
meaning-carrying definitions; the broader implementation-import graph mentioned in N1
includes proof dependencies, checked separately by provider replay and axiom closure.

The first version needed an explicit `Nat` annotation for the diagnostic counter (Lean
otherwise inferred `MessageData` from interpolation). It was corrected without a resource
override. This was an auditor probe typing error, not an anchor/provider failure. Both
transient files were deleted. The successful run used the same 4 GB wrapper with one Lean
thread and default heartbeat limits.

```text
SEMANTIC_CLOSURE_OK KAM.Planetary.StrongAMD.orderedPairThreshold_isLeast: 8 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.StrongAMD.orderedPairThreshold_existsUnique_value: 6 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.StrongAMD.orderedCrossThreshold_isLeast: 11 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.StrongAMD.orderedStrongThreshold_isLeast: 12 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.StrongAMD.sourceStrongAMD_nonneg: 12 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.StrongAMD.sum_action_mul_eccDeficit_le_sourceStrongAMD: 15 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.StrongAMD.sourceKepler_axis_pos: 7 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.StrongAMD.sourceKepler_ecc_le_one: 8 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.StrongAMD.sourceKeplerPeri_le_planeLength: 11 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.StrongAMD.planeLength_le_sourceKeplerApo: 11 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.StrongAMD.sourceOscAxis_pos: 13 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.StrongAMD.sourceOscPeri_pos: 14 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.StrongAMD.sourceOscPeri_le_planeLength: 14 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.StrongAMD.planeLength_le_sourceOscApo: 14 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.Spatial.spatialSourceKeplerAxis_pos: 10 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.Spatial.spatialSourceKeplerAction_pos: 11 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.Spatial.spatialSourceKeplerAction_sq: 12 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.Spatial.spatialSourceKeplerEcc_sq: 18 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.Spatial.spatialSourceKeplerEcc_nonneg: 12 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.Spatial.spatialSourceKeplerEcc_le_one: 12 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length: 18 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length_le: 14 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.Spatial.spatialSourceKeplerPeri_le_length: 13 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.Spatial.spatialSourceKeplerApo_ge_length: 13 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.Spatial.spatialSourceStrongAMD_nonneg: 15 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.Spatial.spatialSourceAction_mul_eccDeficit_le: 19 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.Spatial.spatialSourceOscParam_pos: 13 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.Spatial.spatialSourceOscEnergy_neg: 13 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.Spatial.spatialSourceOscEcc_lt_one: 13 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.Spatial.spatialSourceOscEcc_nonneg: 13 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.Spatial.spatialSourceOscAxis_pos: 14 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.Spatial.spatialSourceOscPeri_pos: 15 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.Spatial.spatialSourceOscPeri_le_length: 15 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.Spatial.spatialSourceOscApo_ge_length: 15 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.StrongAMD.planar_strongAMD_barrier: 27 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety: 56 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_halfInteger: 56 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety: 63 project definitions
SEMANTIC_CLOSURE_OK KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety_halfInteger: 63 project definitions

CLOSURE_PROBE_EXIT 0
CLOSURE_OK_COUNT 39

```



## Final lint and handoff

Run from `/root/code/KAM-inp-lp-sealaud`, only through the mandated wrapper:

```sh
PYTHONDONTWRITEBYTECODE=1 /root/code/KAM-inp/.drafts/LP/lp_lint.sh /root/code/KAM-inp-lp-sealaud
```

The wrapper applies the D53 4 GB/no-swap scope, nice 10, one Lean thread and its
8 GB memory gate. It builds no module and selects no certificate library.

```text
check_lean_modules: PASS (4225 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (305 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
exit 0
```

Files edited by this auditor: only `docs/tracks/LP/audits/LP-SEAL-audit-1.md`.
The author build receipt is `Build completed successfully (11090 jobs)`, rc 0,
for the three targeted root parts; the auditor compiled transient real-module probes and
replayed the exact new modules using the synced build, and authored no Lean module needing
a separate target build. All transient probe files were removed. No commit was made.

Main-result axioms: exactly `propext`, `Classical.choice`, `Quot.sound` for each of the
39 anchors and its provider. No new suspected pinned-source erratum or mathematical
deviation was found. The disclosed procedural adjustments are the authorized single-pass
SEALED installation and the binding revised replay schedule; the two private sibling
proof copies are exactly the approved rebase mechanism.

Final acceptance scope: the 128 D62-approved frozen files and their 39 providers at
`f5729cf8af5bfb688326d989161db2d865fbeead`, with the manifest, rebase and records checked above.
The full 284-module implementation replay belongs to landing under the binding root-b8 ruling.
