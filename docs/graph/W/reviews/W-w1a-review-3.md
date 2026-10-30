# W-w1a delta review

Reviewer: sol-delta3-W-w1a (sol-delta3-W-batch; independent, refute-first).

Verdict: **PASS**.

Scope: only records still PROPOSED in the current packet, under REVIEW-BRIEF rule 9 and the final SPEC change-log entry (inp merge, corpus re-pin, writer revisions r2). Previously REVIEWED records are context only. All six CORPUS.sha256 entries verified OK. No git, Lean, lake or lint was run.

## Nodes

| id | verdict | spans or reason |
|---|---|---|
| stepW:w1:ext | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:ext@L325-L329 |
| stepW:w1:restr | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:restr@L330-L334 |
| bpW:w1:ext-rect | PASS | blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-rect@L117-L125 |

## Coverage

| id | verdict | spans |
|---|---|---|
| bpW:w1:ext-rect | PASS | blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-rect@L117-L125 |

All other coverage items PASS within this delta scope; already REVIEWED items are not re-adjudicated.

## Findings and source checks

Extensions and restriction are self-contained for a >= 0 and arbitrary real p; the W0 steps are explicitly comparisons, not proof inputs. The lambda-facts and lam edges locate the actual inequalities. W1-E9 states the Banach-valued rectangle theorem and Fubini on boxes, including oriented endpoints; it is a labelled W external leaf. The K rectangle mention is provenance, not an import. Its addition is expressly authorized by the final SPEC change-log entry.

## Suspected blueprint defects

None newly identified in the reviewed delta. Findings above concern graph records; they do not reopen the repaired source gaps or assert Lean proof status.
