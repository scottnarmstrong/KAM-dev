# SO-CEXP prover handoff (branch inp-socexp, 1aae3439; track SO package run by the main orchestrator)


Files: KAM/Certificate/Arith/ComplexExp.lean (new, ~80 lines).
Declarations: `KAM.Certificate.certCExpReduced`, `certCExpReduced_sound` (signatures exactly as signed).
Deviation: two extra PUBLIC helpers, `certBallSquareIter` (structural recursion, squares a ball s times)
and `mem_certBallSquareIter` (exp (2^s * v) soundness). Private helpers cannot appear in the body of a
public def under the module system; the names were grep-checked unique in KAM.
Approach: reduced ball = `times ⟨z,zRad⟩ (ofRat (1/2^s))`; `mem_times`+`mem_ofRat` put w/2^s in it;
`certCExpSmall_sound` + `certCExp_sound_of_small` give exp(w/2^s); induction on s with
exp(2u)=exp u * exp u and `mem_times`; 2^s*(w/2^s)=w.
Checks: gate build of KAM.Certificate.Arith.ComplexExp: "Build completed successfully", no warnings in
the file. `sh scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK;
only "KAM.lean is out of date" (generated; orchestrator must run scripts/gen_root_imports.py).
#print axioms certCExpReduced_sound: [propext, Classical.choice, Quot.sound].
No heartbeat options, no sorry, lines <= 100 cols. Uncertainties: none; no sanity example added.
Errata: none.

CONTEXT: track SO (plan /root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md; design /root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md, Revision 4); draft signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean. The orchestrator fixed the two signed declarations (brief /root/code/KAM-inp/.drafts/briefs/offload-main/SO-CEXP.md; design Revision 4 adopts them verbatim, signature file section A 'Arith/ComplexExp'). Design audit 3 finding F10 (/root/code/KAM-inp-design-so/docs/tracks/SO/audits/SO-DESIGN-audit-3.md) motivates it. Check that certCExpReduced_sound holds for EVERY input ball with NO size hypothesis (soundness only on the some branch), that the scaling by 2^-s and the s squarings carry every radius and rounding contribution, and that the definition is kernel-reducible (no well-founded recursion).

AUDIT FOCUS: the package's signed declarations match the draft signatures verbatim; every proof is sound with no added premise; the slice the design assigns to these modules is complete. Audit ONLY KAM/Certificate/Arith/ComplexExp.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY (including fully qualified names); (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100, no native_decide or axiom.
