Audited HEAD: 4a27d970e5c599d3f4c062c7a710a266d42877c5
Branch: inp-lp-freeze8r
Worktree: /root/code/KAM-inp-lp-freeze8r
Date: 2026-11-01
Auditor: independent Codex session; refute-first; no delegation.

# STATEMENT-AUDIT-DRAFT8-1

**Verdict: PASS WITH NOTES.** Both complete proposed declarations satisfy the LP3 delta against the real D62 frozen templates. No blocking statement, definition-closure, provider-type or seal-body defect was found. The prose correction below does not require changing either candidate Lean text.

This is a draft-8 statement audit, not a re-audit of draft 7, D62, the Nekhoroshev proof or the LP3 implementation proof. No LP3 frozen export has been installed or approved by this audit. Each candidate retains one proposed proof hole. The real providers and the scratch sealed declarations separately pass standard axiom closure.

## Findings and exact replacements

| ID | Class | Evidence and finding | Exact replacement / disposition |
|---|---|---|---|
| C1 | CHANGE-RECOMMENDED | docs/tracks/LP/FREEZE-PROPOSAL-DRAFT8.md:405,410 calls the half-integer choice the “best” LP1/LP2 time exponent. The frozen family permits every τ > n − 1; τ = n − 1/2 is a chosen corollary, not an optimizer of 1/(2(τ+1)). For example τ = n − 3/4 is allowed and gives the larger power 1/(2n+1/2), on its corresponding Diophantine locus. | At line 405 replace “best” with “the half-integer choice”. At line 410 replace “LP1/LP2's best time exponent” with “LP1-H/LP2-H's time exponent”. No Lean replacement. |
| N1 | NOTE | .drafts/freeze8r/c8r_verification.lean:302–304: spatial anchor vs raw-map implementation is TYPE_NOT_EQV before unfolding, TYPE_EQV after expanding exactly the two D62 source barycentric maps. Exact application elaborates. Anchor vs staged provider is literally TYPE_EQV under both probe commands. | Retain the qualified wording: “LP3-2's implementation type is Expr-equal after unfolding exactly the two frozen source barycentric maps; its provider type is Expr-equal without unfolding.” No statement replacement. |
| N2 | NOTE | Fresh lint reports only “KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/Provider.lean)”. Staged providers are absent from roots. This is the explicit accepted staging deviation in brief check 6. | Retain staged quarantine; leave generated roots unchanged during this audit. No replacement. |
| N3 | NOTE | KAM/Planetary/StrongAMD/Nek/PlanarSafety/Source.lean:15,36 says “LP:MAIN L15 (502–506)”; docs/tracks/LP/source/MAIN.md:502 is Theorem 15. The producer already reported this nit. | In those implementation docstrings replace “LP:MAIN L15 (502–506)” with “LP:MAIN T15 (502–506)”. No frozen-text replacement; not edited here. |
| N4 | NOTE | Auditor execution deviation: the first two verbatim check-(a) commands were launched before the first session's completion was collected, so serial execution was not ensured. Both were individually D53-capped and exited 0. | Superseded by the recorded six-file serial rerun. Execution instruction: “Wait for completion of each wrapped Lean/Lake command before starting another.” No repository replacement. |

No BLOCKING finding. C1 concerns proposal prose, not an erratum in pinned MAIN. No new suspected mathematical source erratum. N3 was already recorded by LP-FREEZE8R. N4 is an audit-process deviation, disclosed rather than omitted.

## Scope and pinned objects

Read the worktree AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the complete brief at /root/code/KAM-inp-lp/docs/tracks/LP/freeze/AUDIT-DRAFT8-BRIEF.md, and /root/.claude/skills/lean-statement-audit/SKILL.md. The skill was applied without delegation. The local decisions file ends before D53; the controlling D53 wrapper is the launcher's binding instruction. D56/D59/D62 were read from git show main:docs/DECISIONS.md, as directed, together with LP3-PLAN §1.

Read the original LP-FREEZE8 handoff and staging record, the LP-FREEZE8R regeneration handoff, and the LP-FREEZE7R F1 handoff. The original stand-in verification is superseded by the real-import checks here. No old stand-in result is used as current closure evidence.

Abbreviations used below:

- P = docs/tracks/LP/freeze/draft8/KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafetyNoArith.lean.txt.
- S = docs/tracks/LP/freeze/draft8/KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafetyNoArith.lean.txt.
- EP/ES = the two entries in docs/tracks/LP/freeze/draft8/manifest-entries.json, beginning at lines 5/355, with closures at 24/374 and draft states at 346/764.
- MAIN = docs/tracks/LP/source/MAIN.md, as amended by source/AMENDMENTS.md.
- PLAN = docs/tracks/LP/lp3/LP3-PLAN.md.

The D62 template files are byte-equal at audited HEAD, main and f46b94fb:

- KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafety.lean.
- KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafety.lean.

The independent Python check below verifies that identity directly. Fresh lint checks the live frozen prefix/suffix and ABI integrity. The LP3 candidates are absent from the live manifest and their future frozen paths.

| Object | SHA-256 |
|---|---|
| P | 77c6bb5ee337d2c6b96bed50a06e5ca835acb33d3b9ee0813498df8b5be6cff8 |
| S | ba6087a8953f445bb8dcea8f8a7ea074caf1d95442c80e27121f464efeea1374 |
| planar provider | 956c7e7648eb1c74468344d90038811202ef1738a5ac33f054ad93c1eed9304e |
| spatial provider | 34e337b7af0e90f8e6472acdf2093e68b0add2f2e476e7552c2cc58fe60b0904 |

The manifest source revision is a regeneration-base pin, KAM-inp@2bbacd66, not this audit HEAD. All three full hashes embedded there independently match the current MAIN, AMENDMENTS and PLAN bytes.

## The six required checks

| Check | Result and file:line evidence |
|---|---|
| 1. Exactly three LP3 changes | PASS. Compared the entire theorem text through its final conclusion, excluding only the proof body and normalizing whitespace. From frozen LP1/LP2: remove γ τ, hγ hτ and exactly one complete KAM.IsDiophantine premise; replace exactly one horizon exponent and exactly three square-root drift terms; rename the theorem. This equals P/S in full. P:68–139; S:69–145. No additional substitution. |
| 1. Unchanged clauses | P:73–84 and S:74–86 retain the nine-constant order, positivity, N10 bounds, physical initial state, compact axis set, chamber and source-carrier premises. P:86–139 and S:88–145 retain existence, uniqueness, Newtonian reconstruction, δ/2, canonical annuli, star/all-pair distances, osculating ellipticity, element errors, Aosc * μ errors and half gaps. |
| 1. Spatial F1 | PASS. S:77 binds ∀ hμ : 0 < μ; S:92–93 passes the actual theorem's hν hμ to both frozen source barycentric maps. These lines are unchanged from frozen LP2, not reconstructed from stand-ins. |
| 2. Exponents | PASS. KAM/Frozen/Planetary/Defs/PlanetaryTimeExponent.lean:34–35 gives 2/(6n²−3n+14) and explicitly says n counts planets. PlanetaryDriftExponent.lean:35–36 gives 3 * planetaryTimeExponent n / 2, hence 3/(6n²−3n+14). P:68,77,85,100,102,107 and S:69,78,87,103,106,109 use the same n as ν : Fin n → ℝ, not 2n or 3n. This implements PLAN §1.1 O-1 and §1.3's fast dimension. |
| 3. Closure | PASS. No new definition. Direct frozen-import delta is exactly minus KAM.Frozen.Defs.IsDiophantine, plus the two exponent modules. Every recursively imported definition is a SEALED live-manifest entry. EP has 79 distinct closure files; ES has 96; independently recomputed missing/extra sets are empty. Definition meanings are bound to these unchanged frozen versions; no D62 definition re-audit is asserted. |
| 3. Semantic/file closure | The fresh check-(c) constant listing agrees with verification §5's 104 definitions across both anchors, including the source-map wrappers; none is a new project definition. The spatial file-import closure grows through existing exponent-module imports, not added spatial assumptions. The only newly directly referenced definitions relative to the frozen LP1/LP2 types are the two exponents. |
| 4. Names, paths, form | PASS. EP/ES names, mirrored frozen/provider paths and exports agree with P/S. Copyright, module, public frozen definition imports, private own-provider import, module docstring, exposed public section, namespace and single marked proof body are present (P:1–68,140–148; S:1–69,146–154). The suffix noArith aptly identifies absence of arithmetic hypotheses without promising resonant-only data or a stronger time/drift power. |
| 5. Verification | PASS. Fresh (c), all four (a) files, both exact sealed scratch files and the provider probe exit 0. Every reused scratch declaration type was independently checked against P/S bytes before its run was used as evidence. Real frozen imports and real implementation/provider modules; no inline substitute declaration or stand-in. Provider types are literally Expr-equal to anchors. |
| 6. Quarantine | PASS within the brief's explicit accepted staging scope. Neither provider module occurs in KAM/Root/*.lean. Fresh lint has only accepted generated-provider-root staleness. No roots regenerated. |

The newly referenced exponent definitions are literal, unchanged D25 formulas. For their reuse in this delta: BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS. No choice-defined object, off-carrier fallback or new characterization obligation is introduced.

## Expanded premise and binder audit

Each row applies separately to P and S; physical formulas have planar/spatial alternatives. TYPING for hch/h₀ means precisely the inherited D59 OD-11(b) source-subtype membership, not an analytic estimate. All per-body indices have type Fin n. The formulas retain their displayed bounded quantifiers; these index variables are typing data, not additional logical assumptions. There are no extra instance binders.

| Input / expanded field | Bin | Source/ruling and candidate locus |
|---|---|---|
| {n : ℕ} | TYPING | MAIN §1; P:68 / S:69 |
| hn : 2 ≤ n | SOURCE | MAIN §1; PLAN §1.1; P:68 / S:69 |
| ν : Fin n → ℝ | TYPING | MAIN §1 masses; P:68 / S:69 |
| hν : ∀ i, 0 < ν i | SOURCE | MAIN §1 positive masses; P:69 / S:70 |
| hνmax : ∃ i, ν i = 1 | RULED | D59 OD-3; P:69 / S:70 (the existential index witnesses normalization) |
| hνle : ∀ i, ν i ≤ 1 | RULED | D59 OD-3; P:69 / S:70 |
| A : Set (Fin n → ℝ) | TYPING | MAIN §1 compact axis data; P:70 / S:71 |
| hA : IsCompact A | SOURCE | MAIN §1; P:70 / S:71 |
| hAord: ∀ a ∈ A, ∀ i, 0 < a i | SOURCE | MAIN §1 positive ordered axes; P:71 / S:72 |
| hAord: ∀ a ∈ A, ∀ i j, i < j → a i < a j | SOURCE | MAIN §1 ordering; P:71 / S:72 |
| δ : ℝ | TYPING | MAIN §1 fixed margin; P:72 / S:73 |
| hδ : 0 < δ | SOURCE | MAIN §1; P:72 / S:73 |
| μ : ℝ | TYPING | MAIN §1 small parameter; P:76 / S:77 |
| 0 < μ (named hμ in S) | SOURCE | MAIN §1/L1; P:76 / S:77; D62 F1 preserves the proof name |
| μ ≤ μ₀ | SOURCE | MAIN (6)–(7); P:76 / S:77 |
| z₀ : Phase (n*2) / Phase (n*3) | TYPING | MAIN T15/T19 dimensions; P:77 / S:78 |
| physical premise: ∀ i, positive star distance | SOURCE | MAIN (6); P:78 / S:79 |
| physical premise: ∀ i, negative Kepler energy | SOURCE | MAIN (6); P:78 / S:79 |
| initial axis vector ∈ A | SOURCE | MAIN (6); P:79 / S:82 |
| hch expanded: ∀ i, positive initial action | TYPING | D59 OD-11(b); frozen Chamber.lean:28–29; P:80 / S:83–84 |
| hch expanded: ∀ i j, i < j → ordered actionAxis | TYPING | Same chamber definition/ruling and candidate loci |
| h₀ expanded: ∀ i, positive ν | TYPING | D59 OD-11(b) source carrier; P:81–82 / S:80–81 |
| h₀ expanded: ∀ i, positive star distance | TYPING | Same source carrier/ruling and loci |
| h₀ expanded: ∀ i, negative Kepler energy | TYPING | Same source carrier/ruling and loci |
| source strong AMD ≤ orderedStrongThreshold hn ⟨_,hch⟩ − δ | SOURCE | MAIN (6), AMENDMENTS N8, D59 OD-1; P:83–84 / S:85–86 |

Per anchor, expanded logical-input rows: SOURCE **12**, STANDING **0**, TYPING **11**, RULED **2**, EXCESS **0** (25 rows). Unexpanded surface: SOURCE 10, TYPING 8, RULED 2 (20 inputs). The order/physical conjunctions and chamber/carrier bundles are expanded above. No hidden project assumption remains in them. SpatialSourceCanonicalPhase unfolds through SpatialElliptic to SpatialNegativeEnergy, whose complete predicate is the three per-body inequalities (SpatialNegativeEnergy.lean:30–31); planar SourceCanonicalPhase.lean:32–34 is the corresponding subtype. IsCompact A is the source compactness premise, not a project result bundle.

The nine constants μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem are existential OUTPUTS, before μ and z₀. Positivity and N10 are conclusions, not inputs. Likewise z, hcht, hs, ho and their inequalities are existential outputs. Universal t and t ∈ Icc (-T) T delimit the orbit guarantees. Their scopes are unchanged by the complete-type comparison. Constants depend only on (n,ν,A,δ) and proofs of those data, never μ, z₀, γ or τ. No secular, prograde, alignment, nonzero-angular-momentum or stopped-drift premise was added.

Draft-status separation:

- DECLARATION_FIDELITY: PASS, both candidates.
- DRAFT_ALLOWLIST: PASS for the proposed single marked hole and no other provisional body; no live allowlisting or author approval is claimed.
- PROOF_STATUS: FROZEN_UNPROVED is the skill's classification for a draft theorem body. These actual artifacts are still **PROPOSED / NOT FROZEN**. Scratch sealed copies and real providers separately have standard axiom closure. This audit does not promote candidate sorry bodies into proved frozen exports.

## Commands and fresh outputs

All commands ran from /root/code/KAM-inp-lp-freeze8r. No Lean/Lake command was run without the launcher's memory cap. Except for the disclosed preliminary pair (N4), commands were run serially. No heartbeat, recursion-depth or synthesis-budget override was used.

The common wrapper W below means exactly:

    systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1

W is an abbreviation in this report, not a shell variable that was used at runtime. Read-only pin commands included git rev-parse HEAD, git branch --show-current, git status --short and git show main:docs/DECISIONS.md, plus the cited file reads. Initial status was empty.

### Check (c)

    W lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .drafts/freeze8r/c8r_verification.lean

Exit 0. Both scratch anchors print axioms [propext, Classical.choice, Quot.sound]. Planar vs implementation: TYPE_EQV THEOREM REDUCIBILITY_SAME, also TYPE_EQV after the map-unfold probe. Spatial vs implementation: TYPE_NOT_EQV THEOREM REDUCIBILITY_SAME, then TYPE_EQV after expanding exactly the two source maps. The command also prints the frozen constant-closure listing.

Meta probes were inspected: they read environment types, compare Exprs and enumerate constants; they do not add axioms or alter theorem types. The exact closing applications are at c8r_verification.lean:209,298; axiom prints and comparisons at 213–215,302–304.

### Provider type, composition and exact seal bodies

    W lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .drafts/freeze8r/prov8r_check.lean

Exit 0. EACH planar/spatial comparison prints:

    TYPE_EQV THEOREM REDUCIBILITY_SAME
    TYPECHECK <anchor> <provider>: TYPE_EQV

Both examples of type_of% @X := @Pv elaborate. All four axiom prints (two scratch anchors, two real providers) are exactly:

    [propext, Classical.choice, Quot.sound]

Literal bodies, examples and prints: prov8r_check.lean:160–169,252–261. Each exact seal body is the candidate's prescribed application of its provider to hn ν hν hνmax hνle A hA hAord δ hδ.

### Authoritative serial check-(a) and sealed-file rerun

The exact shell loop was:

    for f in .drafts/freeze8r/a/*.lean .drafts/freeze8r/seal/*.lean; do
      systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false "$f"
      rc=$?
      echo "EXIT $rc $f"
      if [ "$rc" -ne 0 ]; then exit "$rc"; fi
    done

All SIX files print EXIT 0, in this order (prefix .drafts/freeze8r/):

    a/KAM_Frozen_Planetary_Spatial_Theorems_SpatialStrongAMDExponentialSafetyNoArith.lean
    a/KAM_Frozen_Planetary_Spatial_Theorems_SpatialStrongAMDExponentialSafetyNoArith__verbatim.lean
    a/KAM_Frozen_Planetary_StrongAMD_Theorems_PlanarStrongAMDExponentialSafetyNoArith.lean
    a/KAM_Frozen_Planetary_StrongAMD_Theorems_PlanarStrongAMDExponentialSafetyNoArith__verbatim.lean
    seal/KAM_Frozen_Planetary_Spatial_Theorems_SpatialStrongAMDExponentialSafetyNoArith.lean
    seal/KAM_Frozen_Planetary_StrongAMD_Theorems_PlanarStrongAMDExponentialSafetyNoArith.lean

Each a-file has only the expected “declaration uses sorry” warning, at spatial lines 68/69 and planar lines 67/68 (without/with private provider import). Both seal-files produce no warning or error. Independent byte checks establish that a-files are exactly candidate/candidate minus its own provider-import line; seal-files are candidate plus the two dummy approval fills and the prescribed seal body.

The superseded preliminary pair used the same wrapped Lean command separately on the two a/*__verbatim.lean paths, each exiting 0 with the expected sorry warning. The launch-sequencing deviation is N4.

### Targeted builds

    for m in KAM.Provider.Planetary.StrongAMD.PlanarStrongAMDExponentialSafetyNoArith KAM.Provider.Planetary.Spatial.SpatialStrongAMDExponentialSafetyNoArith; do
      systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake build "$m"
      rc=$?
      echo "EXIT $rc $m"
      if [ "$rc" -ne 0 ]; then exit "$rc"; fi
    done

Both builds exit 0. The captured output ends “Build completed successfully (9507 jobs).” Lake replays existing dependency warnings: unused variables, unused simp arguments and the existing dif_pos deprecation. No new provider elaboration failure or default-heartbeat failure. No full-library/application build, clean, root regeneration or budget override.

### Lint

    W scripts/lint_sources.sh

The entire script, including its internal ABI Lean subprocess, runs inside the same D53 systemd scope, with LEAN_NUM_THREADS=1. Exit **1**, complete substantive output:

    KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/Provider.lean)
    check_lean_modules: PASS (4233 Lean files, 0 comparator configurations)
    FROZEN-ANCHOR GUARD OK
    ABI HASHES OK (305 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))

Only the first line is a failure, exactly the brief's accepted staging deviation. No other lint failure.

### Independent read-only structural check

The following Python command imports no producer generator, calls no Lean/Lake process, and edits no artifact. It independently checks full types, D62 blob identity, source hashes, import closure, provider text types, actual probe bytes, exact seal-body substitution and root quarantine. Exit 0, output:


    KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_noArith: FULL_TYPE_3_CHANGES_ONLY; D62_BLOB_EQUAL; CHECK_BYTES_EQUAL; PROVIDER_TYPE_TEXT_EQUAL
      closure 79 missing 0 extra 0 all SEALED definitions
      draft sha256 77c6bb5ee337d2c6b96bed50a06e5ca835acb33d3b9ee0813498df8b5be6cff8
      provider sha256 956c7e7648eb1c74468344d90038811202ef1738a5ac33f054ad93c1eed9304e
    KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety_noArith: FULL_TYPE_3_CHANGES_ONLY; D62_BLOB_EQUAL; CHECK_BYTES_EQUAL; PROVIDER_TYPE_TEXT_EQUAL
      closure 96 missing 0 extra 0 all SEALED definitions
      draft sha256 ba6087a8953f445bb8dcea8f8a7ea074caf1d95442c80e27121f464efeea1374
      provider sha256 34e337b7af0e90f8e6472acdf2093e68b0add2f2e476e7552c2cc58fe60b0904
    SOURCE_HASHES_MATCH
    PROVIDERS_ABSENT_FROM_ROOTS
    

Complete reproducible command:

    python3 -B - <<'PY'
    import pathlib, re, json, hashlib, subprocess
    R=pathlib.Path.cwd()
    D=R/'docs/tracks/LP/freeze/draft8'
    M=json.loads((R/'manifest/frozen-anchors.json').read_text())['anchors']
    B={a['path']:a for a in M}
    E=json.loads((D/'manifest-entries.json').read_text())['entries']
    def stmt(t):
        return re.search(r'^theorem .*?(?=\n  -- FROZEN_ANCHOR_PROOF_BEGIN)',t,re.M|re.S).group().removesuffix(' :=')
    def norm(t): return ' '.join(t.split())
    def imports(t): return re.findall(r'^(?:public )?import (\S+)$',t,re.M)
    def closure(t):
        seen=set(); todo=imports(t)
        while todo:
            m=todo.pop()
            if not m.startswith('KAM.Frozen.') or '.Defs.' not in m or m in seen: continue
            seen.add(m)
            todo+=imports((R/(m.replace('.','/')+'.lean')).read_text())
        return {m.replace('.','/')+'.lean' for m in seen}
    for e in E:
        p=e['path']; old=p.replace('NoArith','')
        t=(D/(p+'.txt')).read_text(); b=(R/old).read_text()
        for rev in ['main','f46b94fb']:
            assert subprocess.check_output(['git','show',rev+':'+old])==(R/old).read_bytes()
        a=stmt(b)
        a=a.replace('exponentialSafety {','exponentialSafety_noArith {',1)
        assert a.count('(δ γ τ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) (hτ : (n : ℝ) - 1 < τ)')==1
        a=a.replace('(δ γ τ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) (hτ : (n : ℝ) - 1 < τ)',
                    '(δ : ℝ) (hδ : 0 < δ)',1)
        a,k=re.subn(r'\n        KAM\.IsDiophantine γ τ .*? →(?=\n)', '', a, flags=re.S)
        assert k==1
        assert a.count('μ ^ (-(1 / (2 * (τ + 1)))))')==1
        a=a.replace('μ ^ (-(1 / (2 * (τ + 1)))))','μ ^ (-planetaryTimeExponent n))',1)
        assert a.count('Real.sqrt μ')==3
        a=a.replace('Real.sqrt μ','μ ^ planetaryDriftExponent n')
        assert norm(a)==norm(stmt(t)),p
        assert t.count('by sorry')==1
        assert not re.search(r'γ|τ|IsDiophantine',stmt(t))
        assert e['export'].split('.')[-1] in stmt(t)
        assert e['kind']=='theorem' and e['state']=='DRAFT_SORRY'
        assert e['author_approval']=='PENDING (D59 approves rulings only)'
        assert not (R/p).exists() and p not in B
        cl=closure(t); declared={c['path'] for c in e['definition_closure']}
        assert cl==declared and len(cl)==len(e['definition_closure'])
        assert all(B[c]['kind']=='definition' and B[c]['state']=='SEALED' for c in cl)
        oldimp=set(imports(b)); newimp=set(imports(t))
        assert {i for i in newimp-oldimp if i.startswith('KAM.Frozen.')}=={
            'KAM.Frozen.Planetary.Defs.PlanetaryTimeExponent','KAM.Frozen.Planetary.Defs.PlanetaryDriftExponent'}
        assert {i for i in oldimp-newimp if i.startswith('KAM.Frozen.')}=={'KAM.Frozen.Defs.IsDiophantine'}
        stem=p[:-5].replace('/','_')
        for suff in ['', '__verbatim']:
            probe=R/('.drafts/freeze8r/a/'+stem+suff+'.lean')
            expected=t if suff else re.sub(r'^import KAM\.Provider\..*\n','',t,flags=re.M)
            assert probe.read_text()==expected
        seal=(R/('.drafts/freeze8r/seal/'+stem+'.lean')).read_text()
        pv=e['implementation']['export']; args='hn ν hν hνmax hνle A hA hAord δ hδ'
        sealbody=seal.split('  -- FROZEN_ANCHOR_PROOF_BEGIN\n')[1].split('  -- FROZEN_ANCHOR_PROOF_END')[0]
        assert norm(sealbody)=='by exact '+pv+' '+args
        assert t.replace('<APPROVAL-DATE>','YYYY-MM-DD').replace('<DECISION>','Dnn').replace('  by sorry\n',sealbody)==seal
        for probe in ['c8r_verification.lean','prov8r_check.lean']:
            text=(R/('.drafts/freeze8r/'+probe)).read_text()
            hit=re.search(r'^theorem '+re.escape(e['export'].split('.')[-1])+r' .*? :=\n',text,re.M|re.S)
            assert hit and norm(hit.group().removesuffix(' :=\n'))==norm(stmt(t)),probe
        provider=R/(e['implementation']['module'].replace('.','/')+'.lean')
        pp=provider.read_text()
        hit=re.search(r'^theorem .*? :=\n',pp,re.M|re.S)
        assert norm(hit.group().removesuffix(' :=\n'))==norm(stmt(t))
        print(e['export']+': FULL_TYPE_3_CHANGES_ONLY; D62_BLOB_EQUAL; CHECK_BYTES_EQUAL; PROVIDER_TYPE_TEXT_EQUAL')
        print('  closure',len(cl),'missing',len(cl-declared),'extra',len(declared-cl),'all SEALED definitions')
        print('  draft sha256',hashlib.sha256(t.encode()).hexdigest())
        print('  provider sha256',hashlib.sha256(pp.encode()).hexdigest())
    for e in E:
        for path,sha in re.findall(r'(docs/tracks/LP/[\w/.-]+) \(sha256 ([0-9a-f]{64})\)',e['source']['revision']):
            assert hashlib.sha256((R/path).read_bytes()).hexdigest()==sha
    print('SOURCE_HASHES_MATCH')
    roots='\n'.join(p.read_text() for p in (R/'KAM/Root').glob('*.lean'))
    assert all(e['implementation']['module'] not in roots for e in E)
    print('PROVIDERS_ABSENT_FROM_ROOTS')
    
    PY

## Handoff boundary

Only docs/tracks/LP/freeze/STATEMENT-AUDIT-DRAFT8-1.md is authored by this audit. No commit. No frozen, manifest, generated root, provider or source edit. Existing scratch probes were inspected and executed, not regenerated. Lean/Lake may update disposable build caches; lint creates and removes its ABI scratch internally. No new Lean brief or Lean source was authored.

Remaining limits: final installed bytes/hashes depend on the future exact-text approval and placeholder fills; a dedicated installed seal audit remains separate. No new source uncertainty or unpaid statement obligation was found beyond the notes above.

