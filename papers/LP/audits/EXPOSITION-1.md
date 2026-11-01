# EXPOSITION-1: independent exposition audit of the LP paper

Target: commit `cda28701`, worktree `/mnt/HC_Volume_106379410/kam-paper/KAM-paper-lp`, `papers/LP/main.pdf` (23 pp).
Style authority: `latex-math-writing` skill (HCP-final exemplar, scott-style overlay, banned-word list).
Auditor wrote none of the text. No `.tex` file was edited.

```
f3ff73e5d17bc33caf1b7b2208ff88bd9cb03afc1804b23ba9a6fe81cf7018f7  papers/LP/sections/abstract.tex
ada83f3d7164acae9789f09af5b1f7f12c14c89976fa433fd8d809971660e9b6  papers/LP/sections/barrier.tex
a181b6562a9f7227abbf3108d53db74e5f23fd7fbf3e07c8acfd13c473f2da8e  papers/LP/sections/formal.tex
80434fbe44a19b4cbc64237446be9a3302097858d31365048a2e7d3260f3726a  papers/LP/sections/intro.tex
5959168e64b3799604c8f027d25f618d884e4b770ee7df2548d474a8a7c1e3c5  papers/LP/sections/outlook.tex
b2ac9581303d74a1e4b2e1b7378c02e68ddd75795445bbdcaa1c5dbcea1295f9  papers/LP/sections/planar.tex
971762711fd9c61e45f1358b2ddaeef31e343aaaf91d97717bf20daf93091736  papers/LP/sections/resonant.tex
be293bf790dea4e255f293b3afb4d54d4d0ac283c490ec066eac4314c313d347  papers/LP/sections/results.tex
fcadf891d3ac3ae65c274041ab3c30be77c98ecce7726aff1b89a3d10e4698a3  papers/LP/sections/spatial.tex
```

Checks run: `pdftotext -layout` of `main.pdf`; all 23 pages rendered (`pdftoppm -r 80`) and inspected; fresh
`latexmk` into a scratch directory (23 pp, no overfull boxes, no undefined references; two underfull boxes, both in
bibliography entry [2]); banned-word grep from the skill (no reader-visible hit; `engine` occurs only in the label
`rem:engine`); campaign-jargon grep (hits listed in the findings).

## Verdict: FAIL (repairable)

The mathematics reads cleanly and in order, the main theorems can be stated after §§1–2, and the page count (23)
is within the cap. Two blockers: a priority claim made while the paper says the closest prior work was not read,
and the full proofs of the Diophantine normal form (Lemmas 4.3–4.6) exist only in an internal Markdown file that
the bibliography cites by a campaign path. After those two and the Majors below are repaired, I expect PASS WITH
NOTES.

## Findings

### Blockers

**B1. The paper claims priority while saying it has not read Niederman's paper.**
- `outlook.tex:38-39` (p. 20): "Niederman \cite{Nie96} proved exponential stability results in the planetary
  problem. We have not inspected that paper; a precise comparison of hypotheses, domains and exponents remains to
  be made."
- `intro.tex:32` (p. 4): "To our knowledge, the statement in this sharp form has not appeared."
- `intro.tex:30` (p. 4) describes Nie96 only second-hand ("as described in~\cite[\S1.3]{CFG24}").

A published paper cannot ask an open question about whether it has read a cited paper, and the two sentences
together make the novelty claim unreliable. Nie96 is the result closest to Theorems B–E: it addresses the same
mechanism, conservation of angular momentum near circular coplanar motion.
*Repair:* read Nie96 and replace the second-hand sentence in `intro.tex:30` with a direct, pinned comparison
(hypothesis region, exponents, drift, whether large eccentricities are allowed). Delete open question 5
(`outlook.tex:38-39`). If Nie96 cannot be read before submission, delete "To our knowledge, the statement in this
sharp form has not appeared." and keep only "We do not present the normal form as new."

**B2. The human-readable proof of Theorem B is incomplete, and its completion is in an internal file.**
- `planar.tex:81` (p. 12): "The next three lemmas are standard Nekhoroshev-type estimates … Proofs are in~\cite{KAMnotes}."
  Lemmas 4.3–4.5 and 4.1, 5.1 have only `[Sketch]` proofs.
- `refs.bib:40-45` (bibliography [2], p. 22): `howpublished = {\texttt{docs/tracks/LP/source/MAIN.md} and
  \texttt{AMENDMENTS.md} in the repository …}`. This is a campaign path ("tracks", "AMENDMENTS") and a Markdown
  file with amendments, not a citable document.
- `formal.tex:69-71` (p. 21): the Lean proof does not cover Lemmas 4.3–4.6, because it uses a different
  normal form (Remark 4.7).

So the paper's proof of Lemmas 4.3–4.6 is neither written out nor formally checked. The reader is left with sketches
plus a pointer to an internal file. The intro (`intro.tex:34`: "Complete proofs, with all details omitted here, are
written out in~\cite{KAMnotes}") makes this the advertised route.
*Repair (choose one):* (a) write out the proofs of Lemmas 4.3–4.5 (about 1.5 pp, which fits under the cap), or
(b) replace Lemmas 4.3–4.6 by an exact citation of a published normal-form lemma with slow variables (Pöschel's
Normal Form Lemma does not cover slow variables as stated; check this), or (c) present the Lean finite-cutoff
normal form (Remark 4.7) as the proof and state it precisely as a lemma. Whichever route is chosen, publish the
proof notes as a versioned PDF (arXiv companion or a repository release) and cite it as
`Armstrong, Komargodski, \emph{Proof notes for …}, 2026, <stable URL>`, with no `docs/tracks/…` path.

### Major

**M1. The status of Theorem E's formal proof is inconsistent and reads as campaign status.**
- `intro.tex:34` (p. 4): "A formal proof of Theorem~E is in preparation in the same repository."
- `formal.tex:5` (p. 21): "The formal proof of Theorem~E is in preparation".
- `formal.tex:63` (Table 2): "and their normalized forms (in preparation)".
- `formal.tex:105-111` (p. 22): "The same is reported for the development version of the formal proof of
  Theorem~E." / "Theorem~E is proved on a development version; its independent review is in progress. The exact
  statement texts of all results are under final review."
- `resonant.tex:39` (p. 18): Proposition 6.1 "is proved in this form in Lean".

A reader cannot tell whether Theorem E is formally proved. "Under final review" also makes Theorems A–D look
unsettled.
*Repair:* use one status sentence, the same in the abstract, the intro and Appendix A. Either land E and give its
names and lines, or say: "Theorem~E and Proposition~6.1 have formal proofs on a development branch that are not
part of the cited commit; we do not claim them as verified." Delete "The exact statement texts of all results are
under final review." and "its independent review is in progress".

**M2. The axiom statement is hedged, and the "no sorry" claim is misleading.**
- `formal.tex:101`: "As reported by the project's build checks at commit a994efdf, …". This is hearsay.
- `formal.tex:74-77`: "its statement was fixed in advance … The file containing that proof, at commit a994efdf,
  contains no sorry." At a994efdf the cited file `KAM/Frozen/Nekhoroshev/Theorems/PartialConvexNekhoroshev.lean`
  is an 87-line statement whose body is a single call to `KAM.Provider.Nekhoroshev.partialConvex_nekhoroshev`. The
  proof is in another file, so "contains no sorry" is true but says nothing.

*Repair:* "Running `#print axioms` on the declarations of Table~2 at commit a994efdf gives `propext`,
`Classical.choice`, `Quot.sound`." Apply the same sentence to Proposition 6.1 and drop the file-level "no sorry".
Replace "its statement was fixed in advance" with "its statement was written, from \cite[Theorem~4.4]{Nek77},
before its proof". Also see M6 (the `Frozen` path).

**M3. Symbols with two or more meanings.** All of these collide within a few pages of each other:
- **m:** planet masses `m_i=\mu\nu_i` (`results.tex:5`) versus the margin `m` of Theorem A and Lemmas 3.3, 3.5
  (`results.tex:57`), plus `m_k` in the intro formula. *Repair:* rename the margin to `\kappa` or `\varepsilon_0`,
  or use `\delta'`.
- **C:** the AMD versus the time horizon `C>0` in Proposition 6.1 and §6.3 (`resonant.tex:28,32`, "with $C=t$").
  *Repair:* use `T'` or `t_1` for the time.
- **γ:** the Diophantine constant versus the LP mass ratio `\gamma=\nu_i/\nu_j` (`barrier.tex:66`) and Nekhoroshev's
  angular-momentum bound `\abs N\ge\gamma` (`intro.tex:30`). *Repair:* in `barrier.tex:66` write "$C_c(\alpha,\nu_i/\nu_j)$
  … with mass ratio $\nu_i/\nu_j$" and drop the γ. In the intro, write "a lower bound on $\abs N$ exceeding the
  largest value …".
- **η:** a slow coordinate `(\xi,\eta)` and the cell radius `\eta=w/4` in the same section
  (`resonant.tex:12-13` versus `:50`). *Repair:* rename the cell radius `r_c`.
- **d:** the space dimension versus the denominator lower bound `d` (`planar.tex:68-74`) and the erosion distance
  `X\ominus d` (`resonant.tex:14`). *Repair:* use `d_0` in Lemma 4.2 and `X\ominus\rho` in §6.
- **k, l:** a Fourier index `k\in\Z^n`, the eccentricity components `k=\varrho x`, `l=-\varrho y` (`planar.tex:12`),
  the osculating parameter `k_i=1+\mu\nu_i` (`results.tex:48`), and `l` as the planet index in Theorem A(ii) and
  Theorem B(iv). *Repair:* write the eccentricity components as `(\kappa,\iota)`, or simply `\ev=(e^1,e^2)`, which the
  lemma already identifies with the eccentricity vector. Call the osculating parameter `\varkappa_i` or `1+\mu\nu_i`
  inline.
- **β, α:** `\beta=1-\Gamma/\Lambda` in the chart versus Nekhoroshev's box `\alpha_i\le a_i\le\beta_i`
  (`intro.tex:30`) and `\alpha=a_i/a_j` (`barrier.tex:55`). *Repair:* in the intro, write "boxes of semi-major
  axes", with no letters.
- **D:** `\Dfn(u)`, `D_F`, `\mathsf D` (a dimension), the Hessian `D^2h`, `D_0` (Remark 4.7, undefined), and
  `\varepsilon_D` (Lemma 6.2). *Repair:* call the dimension `N_{\mathrm{dim}}` or `2n+2n_s` inline, write
  `\varepsilon_D` as `\varepsilon_1`, and delete `D_0` (see M5).
- **H:** the Hamiltonian `H_\mu` and `H` in Lemmas 4.4–4.5 versus the projections `H_i=L_i\cdot L/\abs L`
  (Lemma 3.3). *Repair:* rename the projections `L_i^\parallel` or `\Pi_i`.
- **K:** the compact set of states in Theorem A versus the compact `K\subset\Ach` in the proof of Lemma 3.4 and the
  Fourier cutoff `K` in Remark 4.7.
- **M:** the mass maximum (§2.3), the bound `M` (Lemma 4.2), the matrix `\mathbf M`, and `M=1+\mu\sum\nu_i`
  (proof of Lemma 3.1).
- **μ₀, c:** the threshold `\mu_0` in Proposition 6.1 versus the theorem constant `\mu_0`; the time constant `c`
  versus `c(F)`, `c_0`, `c_{\mathsf D}`, `c_U` (undefined, `planar.tex:207`) and the cell centres `c_j`.
- **S:** a compact slow set (§4.2) versus an open slow set (Proposition 6.1).
- **F:** the eccentric longitude `F` versus the perturbation `F` (Lemma 4.5) versus the domain `F` (Proposition 6.1).

The scott-style overlay lists "one symbol with two meanings" as a known anger trigger. Fix at least m, C, γ, η, d
and k/l. The others are MINOR.

**M4. Undefined or forward symbols in the intro.**
- `intro.tex:9` (p. 3), Theorem A bullet: "Every state with axes in a compact set of the chamber and AMD at most
  $B(\Lambda)-m$". Neither "the chamber" nor `m` is defined in §1.
- `intro.tex:14`: "(and $\gamma,\tau$)". γ is never introduced in §1.

*Repair:* "Every state whose semi-major axes lie in a compact set of ordered axes and whose AMD is at most
$B(\Lambda)-m$, for a fixed $m>0$, has …". For γ: "… with constant $\gamma$ and exponent $\tau$" in the Theorems B/C
bullet.

**M5. Remark 4.7 is formalization commentary placed in the mathematics, and it is not self-contained.**
- `planar.tex:173-176` (p. 14): "The formal proof replaces Lemmas 4.3–4.6 by a finite-cutoff normal form … available in
  the formal library~\cite{KAMrepo}, fed with the data of Lemma~4.2 … action radius $r=D_0\sqrt\mu$ … time
  $\ge\exp(c_1\mu^{-\vartheta})$".

`D_0`, `c_1` and `K` are undefined, and "fed with" is informal. The appendix bullet (`formal.tex:69-71`) already
says that the formal proof takes a different route.
*Repair:* if B2 is repaired by route (c), turn this remark into the stated lemma. Otherwise delete Remark 4.7 and
move a two-sentence version into Appendix A.1, with the constants named in words.

**M6. Campaign jargon and internal names reach the reader.**
- In the bibliography, outside Appendix A: [2] `docs/tracks/LP/source/MAIN.md`, `AMENDMENTS.md` (see B2).
- Bibliography entries [3], [4] and [9] print "Locators refer to arXiv:…v1" (`refs-A.bib:10,20,29`), an internal
  note. *Repair:* delete the `note` fields. If the page locators really refer to arXiv versions, cite the arXiv
  version instead.
- Appendix tables (pp. 22–23): `lp0_planar_barrier`, `lp1_…`, `lp2_…`, `lp3_…`, `lemma8_complete`,
  `lemma18_complete` (these numbers are internal note numbers, not the paper's Lemma 4.2/5.2), and the path
  `KAM/Frozen/Nekhoroshev/…`. Lean names are allowed in Appendix A, but "lp0–lp3" and "lemma8" will confuse a
  reader and "Frozen" is campaign vocabulary. *Repair:* add one sentence, "Declaration names follow an internal
  numbering and are listed verbatim." Better, rename them in the Lean repository before release (the
  `lean-public-release` skill covers this).
- `formal.tex:35` "its statement was fixed in advance" and `formal.tex:110` "under final review" (see M1, M2).
- `formal.tex:154` (TeX source comment): `% FOR OWNER: confirm wording`. It is not rendered, but it ships with an
  arXiv source upload. Remove it once the wording is settled.

**M7. The scope disclaimer appears four times and the B-versus-E comparison twice.**
- "Asymptotic, constants not explicit, nothing about real systems": abstract; `intro.tex:17` (Scope); `results.tex:72`
  (What is not claimed); `outlook.tex:3-8` (The results are asymptotic) and `:22-25`.
- B versus E: `results.tex:76` (paragraph "Theorems B and E") and Table 1 (`resonant.tex:209-223`), which floats onto
  p. 20 inside §7.
- The bootstrap mechanism: `intro.tex:7`, `intro.tex:19`, `planar.tex:4-6`.

*Repair:* keep Scope in §1 and the first two paragraphs of §7. Delete the paragraph "What is not claimed"
(`results.tex:72`), except its last sentence, which can join "Constants". Delete Table 1, or delete the paragraph
`results.tex:76` and keep the table in §2.3 instead of the proof of Theorem E. This saves about 0.4 pp.

**M8. Lemma 4.8 has a hypothesis that refers to other lemmas, and §6.3 relies on proof-by-reference.**
- `planar.tex:184`: "and for which the conclusions of Lemmas~4.2 and~4.6 hold. Then there are … depending only on
  … and the chart". A hypothesis of this form is a conditional helper.
- `resonant.tex:186-207`: "Lemma~4.8 uses the normal form only through this estimate … the proof of Lemma~4.8 applies
  unchanged." The reader has to recheck Lemma 4.8's proof with r/4 replaced by r/2, different constants (`A_Λ`,
  `T_0`, `c`), and a different time.

*Repair:* state Lemma 4.8 with an explicit hypothesis, the stopped drift estimate: "(SD) there are $T,r$ with
$r\le r_g$, $nr+\Omega_B(r)\le\delta/4$, such that every prograde solution satisfying \eqref{eq:stopped} on
$[0,t]$, $\abs t\le T$, has $\nrm{\Lambda(t)-\Lambda^0}\le r/2$". The conclusion then holds on $[-T,T]$ with drift
$r/2$. Lemma 4.6 and §6.3 each verify (SD), and "applies unchanged" disappears. This also makes the remark in
M5 unnecessary.

**M9. Placement: Lemma 4.9 (osculating elements) is used before it is stated and re-defines §2's notation.**
- `planar.tex:211` (proof of Theorem B) uses Lemma 4.9. `planar.tex:214` then repeats: "The velocity-osculating
  elements … of Section 2 use the heliocentric velocity $V_i=\dot q_i=\ldots$ and the parameter $k_i=1+\mu\nu_i$."

*Repair:* move Lemma 4.9 to just before the proof of Theorem B, for example to the start of §4.4. It uses only the
compact set K and involves no small divisors. Do not move it into §3, which opens with "contains no small parameter".
Delete `planar.tex:214`. The proof of Theorem B then cites only earlier results.

### Minor

**m1.** `barrier.tex:69` (p. 9). This sentence does not parse: "the minimizers of $B_{ij}$ are nondegenerate
eccentricities, two coplanar prograde ellipses with these eccentricities, opposite perihelion directions, and the
inner aphelion and outer perihelion on one ray touch with combined AMD $B_{ij}$". *Repair:* "If $(u,v)$ minimizes
$B_{ij}$, two coplanar prograde ellipses with eccentricities $u,v$ and opposite perihelion directions touch, the
inner aphelion meeting the outer perihelion, and their combined deficit is $B_{ij}$. A radial orbit has deficit
$\Lambda_i$ and is the limit of prograde ellipses as $e_i\uparrow1$." Drop "nondegenerate", which is never proved.

**m2.** Corollary D (`results.tex:85-87`) is a parameter specialization of B/C. Its proof is one line, and the
scott-style overlay says such corollaries should be removed. *Repair:* make it a sentence after Theorem C: "For
$\tau=n-\nf12$, which is allowed for almost every $\Lambda(0)$, $T_\mu=T_0\exp(c\mu^{-1/(2n+1)})$." Keep it as
Corollary D only if the Lean table needs a letter. It does now, so this is the owner's call.

**m3.** Abstract (`abstract.tex:2`): "The results under the Diophantine condition are formally verified". Theorem A,
which is also verified, has no Diophantine condition. *Repair:* "Theorems~A–D are formally verified in the Lean
proof assistant."

**m4.** `planar.tex` uses `\nf12\abs z^2`, which renders as "1/2|z|^2" (p. 15, Lemma 4.8 and its proof, and the
proof of Theorem B). It can be read as 1/(2|z|²). *Repair:* use `\tfrac12\abs z^2` as in `eq:Cz`.

**m5.** `resonant.tex:195-196`: "the bound $C<B(\Lambda^0)-\delta/4$ of Lemma~4.8 would leave no room for this
erosion". Lemma 4.8's proof gives $-7\delta/16$; δ/4 is the level of $\mathcal Z_0$. *Repair:* "membership in
$\mathcal Z_0(\Lambda^0)$ alone, at level $B(\Lambda^0)-\delta/4$, would leave no room for this erosion."

**m6.** `barrier.tex:98` defines `r_g` and `planar.tex:207` uses `c_U`. Neither has an explained subscript, and
`c_U` is undefined. *Repair:* rename `r_g` to `r_0`; write "$E_i\le-\min_{U}\nu_i^2/(2\Lambda_i^2)<0$".

**m7.** Lemma 3.2 is stated for unit gravitational parameter, but the proof of Lemma 4.9 uses it "with parameter
$k_i$". *Repair:* state Lemma 3.2 with a parameter $k>0$ ($E=\abs v^2/2-k/\abs q$, $a=-k/(2E)$), at the cost of one
word in the proof.

**m8.** Lemma 4.3: "the $\lambda$-average and its complement have norm at most one". The sentence means the
operator norm of the projection. *Repair:* "the projections $V\mapsto\langle V\rangle$ and $V\mapsto V-\langle
V\rangle$ do not increase $\norm\cdot_\rho$".

**m9.** Inline statements that are too long to read: Lemma 4.8's conclusion (p. 15, about eight inline
inequalities) and the last sentence of Lemma 4.9 (p. 16, which breaks inside $a^\osc_{i+1}(\ldots)-a_i^\osc(1+\
e_i^\osc)$). *Repair:* display the separations in Lemma 4.9. In Lemma 4.8, write "conclusions (ii)–(iv) of
Theorem~B hold" if M8 is adopted.

**m10.** Proposition 6.1 is followed by "The threshold precedes $P$, $C$ and the solution." Here "threshold" means
$\mu_0$. *Repair:* "The constant $\mu_0$ is chosen before $P$, the time horizon and the solution."

**m11.** `intro.tex:30` compares two different numbers that a reader will set side by side: "mass ratio below
$10^{-13}$" (Niederman, via BN20) and `outlook.tex:16` "perturbations of size about $10^{-11}$" (BN20 §5.1).
*Repair:* say once, in §7, what each number measures, and drop the intro instance (this also shortens the intro).

**m12.** `intro.tex:5` gives the AMD in physical units, $\Lambda_k=m_k\sqrt{Gm_0a_k}$ with index k. Two lines later
it uses $\Lambda_i=\nu_i\sqrt{a_i}$ with index i. *Repair:* use index i throughout and add "(in physical units)".

**m13.** Bibliography [2] wraps badly (underfull, p. 22) because of the `\texttt` paths. This disappears once B2 is
fixed.

**m14.** The table in §6 (Table 1) floats to the top of p. 20, inside §7. Fixed by M7.

Typography otherwise: no overfull lines. Displays are on one line where they fit. Theorem headers and lettering
(A–E, Proposition 6.1, Lemmas x.y) follow the overlay, and links are dark blue (`paperlink`). Contents depth is 1;
the overlay asks for depth 2 (`\setcounter{tocdepth}{2}`), which is a small layout change. No sentence credits one
author with a part of the work. The AI paragraph credits "the authors" jointly.

## Per-section takeaways and recommendations

| § | Pages now | Takeaway (one sentence) | Recommendation | Cap |
|---|---|---|---|---|
| Abstract | 0.4 | Strong AMD-stability with a fixed margin gives exponentially long collision safety, in the plane and in space, uniformly over the sublevel set. | Keep; fix m3. | 0.4 |
| 1 Intro | 3.6 (pp. 1–4) | Exact conservation of angular momentum plus exponentially slow drift of the Delaunay actions closes a bootstrap that keeps the AMD below the sharp threshold. | Keep. Fix B1 and M4, and cut the duplicated bootstrap and the 10^-13 aside (m11). | 3.2 |
| 2 Setting and results | 2.7 (pp. 5–7) | The model, the exact thresholds $B_{ij}$, $B$, and Theorems A–E with all constants chosen before μ. | Keep. Delete "What is not claimed" and either the B/E paragraph or Table 1 (M7). | 2.4 |
| 3 Sharp barrier | 2.3 (pp. 8–10) | $C\le B(\Lambda)-m$ alone forces uniform perihelion and annulus separation, and the moving-threshold estimate converts action drift into AMD drift. | Keep. Fix m1 and m7. | 2.3 |
| 4 Planar theorem | 5.7 (pp. 10–16) | The whole AMD ball is one analytic domain of fixed width, so averaging about the linear Kepler flow with action radius √μ gives drift √μ for time $\exp(c\mu^{-1/(2(\tau+1))})$. | Keep. Fix B2 (adds up to 1.5 pp if proofs are written out) and M5/M8; move Lemma 4.9 before the proof of Theorem B (M9). | 6.5 |
| 5 Spatial | 1.5 (pp. 16–17) | A fixed-plane regular chart aligned with L once per solution gives $C=\tfrac12\abs z^2$, and the planar argument goes through verbatim. | Keep; Corollary D per m2. | 1.5 |
| 6 Resonant | 2.0 (pp. 18–20) | Nekhoroshev's convex theorem with slow variables, applied on finitely many cells covering the sublevel, replaces the Diophantine normal form. | Keep. Fix the symbol collisions (M3) and M8; drop or move Table 1. | 1.8 |
| 7 Limitations | 1.2 (pp. 19–20) | The constants are non-explicit, real masses are out of reach, and the Solar System is AMD-unstable. | Keep the first three paragraphs and questions 1–4; delete question 5 (B1). | 1.0 |
| App. A | 2.0 (pp. 21–23) | Theorems A–D are Lean-verified at a994efdf with standard axioms; definitional faithfulness was reviewed, not machine-checked. | Keep. Fix M1, M2 and M6. | 2.0 |

Projected total after repairs, with B2 by written proofs: about 24 pp, within the 25-page cap.

## Errata and deviations

No source errata were identified (this audit is about exposition). One factual claim was checked: the appendix's
"contains no sorry" for Proposition 6.1's file is true but uninformative (M2). This audit introduces no deviations.
