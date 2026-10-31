# W-w0c delta review

Reviewer: sol-delta3-W-w0c (sol-delta3-W-batch; independent, refute-first).

Verdict: **PASS**.

Scope: only records still PROPOSED in the current packet, under REVIEW-BRIEF rule 9 and the final SPEC change-log entry (inp merge, corpus re-pin, writer revisions r2). Previously REVIEWED records are context only. All six CORPUS.sha256 entries verified OK. No git, Lean, lake or lint was run.

## Nodes

| id | verdict | spans or reason |
|---|---|---|
| bpW:w0:twosided | PASS | blueprint-W/parts/w0-conventions.tex#bpW:w0:twosided@L66-L75 |
| bpW:w0:H | PASS | blueprint-W/parts/w0-conventions.tex#bpW:w0:H@L91-L98 |
| bpW:w0:Gq#cubicGrad | PASS | blueprint-W/parts/w0-conventions.tex#bpW:w0:Gq@L102-L109 |

## Coverage

No PROPOSED coverage records.

All other coverage items PASS within this delta scope; already REVIEWED items are not re-adjudicated.

## Findings and source checks

The three restated source records match w0-conventions.tex L66-L75, L91-L98 and L102-L109. Convolution is restricted to s >= 0; the negative-s example is correctly recorded. The extensions of G and G_q explicitly use a > 0 and recon-bounded with arbitrary p. Gradient and smoothing citations are forward pointers, correctly omitted from DEPS.

The cubicGrad anchor remains the weighted-coordinate specialization q = coeff y in l^{1,1}; the general blueprint definition is not a new frozen Lean domain. Its frozen file, export, anchor ID, contract ID/version and ABI hash match the manifest identity. The current CubicGrad.lean SHA-256 is bd4cba1cda91a3094fb53c9c4a830d9772c592aa8dde4b514254f13efb2064f1, matching the recorded file hash. The inspected declaration has the unchanged m, hm, y, l binders and the stated integral divided by sqrt(lam).

## Suspected blueprint defects

None newly identified in the reviewed delta. Findings above concern graph records; they do not reopen the repaired source gaps or assert Lean proof status.
