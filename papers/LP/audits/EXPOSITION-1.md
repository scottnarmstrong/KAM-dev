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

---

# Round 2 (bound to commit b6d1cca3)

Target: commit `b6d1cca3`, `papers/LP/main.pdf` (23 pp). Diff reviewed: `git diff cda28701 b6d1cca3 -- papers/LP`.
Editor rulings: `NOTES.md` §8. Docs only; no `.tex` file was edited.

```
0b565f28b54772e4c97fdf9eba2211bedc4aadad4aa17bb2223ae48dd920f0b3  sections/abstract.tex
fab6d6dd33aa0b69d791b0e3a72f666db3c9632a385490522bdd34cecb7f7c27  sections/barrier.tex
bebe76929beb2540005cbfda8446a3ca76b964a145e7751ceed78061da09b1c0  sections/formal.tex
9d4cdd88d301afd3f51ad94f146bd8e524bc6a6760982d41a42b539a0f4e5502  sections/intro.tex
bb295fbc845e0807abb888bbf7fec42e515f9f459c10655b48ccd940f4213729  sections/outlook.tex
d50bb6d0e29dc8cbf3c9896d1031f350b5ac9f3f94d30d8e0c7f56ce2540a859  sections/planar.tex
0383ced534cd829d986153f0bdde13527043d9b3f212e102b5547b9844b5ee96  sections/resonant.tex
fc1177df942b90dae4898bc278e8e9ff89c6d9d03e7d5c54e617f491f79a7d36  sections/results.tex
157cc18f687ac912c69154c5b115a64d70366bbb10b55684bef385fa5601c0dc  sections/spatial.tex
```

Checks run: every changed section read linearly; a fresh `latexmk` build in a scratch directory (23 pp, no
overfull boxes, no undefined references, underfull boxes only in §A.3 and in bibliography entry [2]); all 23
pages rendered at 80 dpi and inspected; jargon and banned-word greps on `sections/*.tex` (the only hit is the
`KAM/Frozen/` path in Table 2); the cited proof notes read at `74d77b43`
(`docs/tracks/LP/source/MAIN.md`, `AMENDMENTS.md`). I did not check whether the GitHub repository is public; I
take that from the ruling.

## Verdict: PASS WITH NOTES

Both blockers are closed according to the editor's rulings, and every round-1 Major is resolved or reduced to a
residue. Two Majors should be repaired before submission. R2-1: the paper calls the cited proof notes "complete",
but the notes record that part of Lemma 10 is only sketched. R2-2: one sentence still states that approval is
pending. Neither needs a structural change.

## Implementation of the rulings

**B1 (Niederman): implemented honestly.** `intro.tex:32` opens with "We could not consult Niederman's
paper~\cite{Nie96}; our description of it is taken from~\cite{CFG24,BN20}", and each claim is attributed
("According to …"). `intro.tex:34` restricts the novelty sentence to Theorems B–D and adds "since we could not
consult~\cite{Nie96}, this rests in part on the descriptions above". Open question 5 is deleted. The paragraph
also says plainly that Theorem E is close to Nek77 Theorem 12.3. Not re-raised.

**B2 (Lemmas 4.3–4.5 as sketches): implemented, with one overclaim (R2-1) and a citation-form residue (R2-4).**
`planar.tex:81` says the lemmas are standard, are not claimed as new, and are only sketched, and it points to
[2]. That matches the ruling.

## Round-2 findings

**R2-1 (MAJOR). The paper calls the proof notes complete, and the notes themselves say part of Lemma 10 is sketched.**
- `planar.tex:81`: "Complete proofs, with all constants, are in the supplementary proof notes~\cite{KAMnotes}."
- `intro.tex:36`: "Complete proofs, with the details omitted here, are written out in~\cite{KAMnotes}."

The cited source is `AMENDMENTS.md` at `74d77b43`, which is normative over `MAIN.md`. Its note N5 reads: "L10 |
Flow existence, Lie-series identification and `c_D` are sketched; they matter only for the optional packages
9–11 (not on the shortest route)." L10 is the notes' Lie step, which is the paper's Lemma 4.4. So for Lemma 4.4
the paper points to a source that is not complete either, and Lemma 4.4 is also outside the formal check
(Appendix A.1). The gap is small and the argument is standard. The claim is still false as written, and a reader
in formal verification will check it.

*Repair (smallest):* in `planar.tex:81`, replace "Complete proofs, with all constants, are in" with "More detailed
proofs, with explicit constants, are in"; add "(the flow estimates of the Lie step are standard and only
sketched there)"; and change `intro.tex:36` to "More detailed proofs are written out in~\cite{KAMnotes}."
Alternatively, complete N5 in the notes and keep the wording.

**R2-2 (MAJOR). Residue of M1: an approval-status sentence and a process detail remain in Appendix A.3.**
- `formal.tex:106`: "The exact statement texts await the authors' final approval."
- `formal.tex:104-106`: "the Lean files are unchanged through commit 01d36418. Each integration of new code into
  the repository also replays the proofs in the Lean kernel."

The first sentence tells the reader that the results are not final; a submitted paper either has approved
statements or is not submitted. The second sentence names a commit that appears nowhere else in the paper and
describes the project's internal workflow.

*Repair:* delete both sentences. Keep "`#print axioms` reports exactly … checked at commit 74d77b43."

**R2-3 (MINOR). The A.3 paragraph is badly typeset (p. 21).** The `\sloppy` paragraph of `\texttt` names has
very wide inter-word spaces (two underfull boxes). *Repair:* say "for each declaration in Table~2 (all headline
declarations and their `_normalized`, `_halfInteger` and `_source` versions)", without listing the names again.

**R2-4 (MINOR). Residue of M6 and m13: the citation form of [2] and one path.**
- `refs.bib:43` still prints `docs/tracks/LP/source/MAIN.md and AMENDMENTS.md`. The entry is underfull on p. 22,
  and the reader is asked to apply one file of amendments to another by hand. The notes also number lemmas
  differently (Lemmas 9–11 there are the paper's Lemmas 4.3–4.5) and write `I` for Λ.
  *Repair:* add one sentence at `planar.tex:81`: "(Lemmas 9–11 there, with $I$ in place of $\Lambda$; the
  amendments file overrides the cited lines)". Better, publish the notes as one merged PDF at a release tag.
- Table 2, last row: the path `KAM/Frozen/Nekhoroshev/…` shows campaign vocabulary. It is acceptable in the
  appendix after the sentence "internal identifiers, listed verbatim", but listing the provider file, or
  renaming at public release, reads better.

**R2-5 (MINOR). A false explanatory sentence was introduced.**
- `barrier.tex` (end of the proof of Theorem A, p. 10): "The next lemma, the only place where conservation of $L$
  enters, converts action drift into margin drift."

Conservation of $L$ also enters Lemma 3.3 (which proves it), the proof of Theorem B ("we may assume $L>0$, which
is conserved") and Lemma 5.2 ("Along the solution $L$ is conserved, so $C_{\mathbf N}=C$").
*Repair:* "The next lemma uses the conservation of $L$ to convert action drift into margin drift."

**R2-6 (MINOR). The section opening of §3 drops the star.**
- `barrier.tex:4`: "and $B$ is the least deficit at which two annuli can touch."

$B$ is also bounded by $\Bst$, the deficit at which a planet reaches the star.
*Repair:* "… at which two adjacent annuli can touch or a planet can reach the star."

**R2-7 (MINOR). The Nek77 comparison appears twice, with the same hedge.** `intro.tex:30` and
`resonant.tex:5-9` both say that a box cover "appears to give" the hypothesis of Theorem E up to δ, and both list
what Theorem E adds. *Repair:* in §6, keep only the first sentence ("… replaces it.") and "Table~1 compares …",
and refer back with "(see the comparison with~\cite[Theorem~12.3]{Nek77} in Section~1)".

**R2-8 (MINOR). Small gaps in the new §4.4–§6.3 argument.**
- §6.3 Conclusion (`resonant.tex:125`): "Lemma~4.8 now gives existence and uniqueness". Lemma 4.8 gives
  existence only; uniqueness comes from analyticity, as the proof of Theorem B says. *Repair:* "Lemma~4.8 gives
  existence on $[-T,T]$ (uniqueness as in Theorem~B), …".
- Proof of Theorem C (`spatial.tex`, p. 17): "Lemmas 4.3–4.6 hold verbatim …; Lemmas 4.8, 3.5, 4.7 and 3.1 give
  all conclusions". It never says that (SD) is verified. *Repair:* add "and (SD) is verified as in the proof of
  Theorem~B".
- Lemma 4.8's hypothesis (`planar.tex`, p. 15): "admissible initial state, $\Lambda^0\in\Lset$ and
  $C(0)\le B(\Lambda^0)-\delta$". The last two are part of admissibility. *Repair:* "with admissible initial
  state and $\Lambda^0=\Lambda(0)$".
- The §6.3 restatement of (SD) omits "the solution exists at time $u$", which Lemma 4.8 includes. *Repair:* cite
  (SD) by name instead of restating it.

**R2-9 (MINOR). New symbol reuse introduced by the repairs.**
- Lemma 3.2 now uses $k$ as the gravitational parameter. This is consistent with $k_i=1+\mu\nu_i$, but it adds a
  third meaning of $k$ next to the Fourier index. The (k,l) rename was declined, so this is noted only.
- The proof of Lemma 3.6 uses $\rho$ for a neighbourhood radius, while $\rho$ indexes the domains
  $\mathcal D_\rho$ in §4 and $\rho_*$ is a width in §6. *Repair:* call it $r_0$, as before.
- $\zeta=n(n-1)/2$ (`resonant.tex:39`) is Nekhoroshev's symbol and is not defined in the paper. *Repair:* "give
  the exponents $\aE{},\bE{}$ (with $\zeta=n(n-1)/2$ in Nekhoroshev's notation)", or drop ζ.

**R2-10 (MINOR). A cryptic table cell.** Table 2, "spatial" row: "; negative energy is in the first". *Repair:*
"(the first declaration also assumes negative energies)", or delete it.

**R2-11 (MINOR). Bibliography.** [6] Las97 has `pages = {L75}`; the letter runs L75–L78. NOTES.md says the title
was entered from memory. The title matches the A&A Letter as I know it; check the pages against the PDF.

## Round-1 findings: status

| Item | Status |
|---|---|
| B1 | Resolved per ruling (see above). |
| B2 | Resolved per ruling; overclaim R2-1, citation form R2-4. |
| M1 | Resolved (single status: Theorems A–E proved at 74d77b43) except the approval sentence (R2-2). |
| M2 | Resolved: `#print axioms` stated; "fixed in advance" reworded; the file-level "no sorry" removed. |
| M3 | Resolved for m (masses now μν_i), C (T₁), γ, η (r_c), d (d₀), μ₀ (ε_*), S (W), F (𝓕), P (p̄). H_i, (k,l), 𝖣 declined per ruling. New reuse in R2-9. |
| M4 | Resolved (m, γ, τ introduced in the bullets; "compact set of ordered axes"). |
| M5 | Resolved: Remark 4.7 deleted; Appendix A.1 describes the formal normal form in words. |
| M6 | Mostly resolved ("Locators" notes removed; Lean names declared internal identifiers); residue R2-4. The `FOR OWNER` comment is gone. |
| M7 | Resolved: "What is not claimed" merged into "Constants"; the B/E paragraph replaced by a pointer to Table 1, which now sits at the start of §6.3. New duplication R2-7. |
| M8 | Resolved: Lemma 4.8 has an explicit (SD) hypothesis, verified in the proofs of Theorems B and E. Small gaps in R2-8. |
| M9 | Resolved: Lemma 4.7 (osculating) precedes Lemma 4.8 and the proof of Theorem B; the duplicate definition is removed. |
| m1 | Resolved. |
| m2 | Corollary D kept (owner's call); its proof is merged into §5.3. Accepted. |
| m3 | Resolved ("All results are formally verified"). |
| m4 | Resolved (`\tfrac12`). |
| m5 | Resolved (sentence removed). |
| m6 | Resolved: `r_g` is explained in §4.1 ("a fixed action radius over which $B$ varies by at most δ/16"), and `c_U` is replaced by an explicit bound. |
| m7 | Resolved (Lemma 3.2 has a parameter $k$). |
| m8 | Resolved. |
| m9 | Resolved (displays in Lemmas 4.7 and 4.8). |
| m10 | Resolved ("$\varepsilon_*$ precedes …"). |
| m11 | Resolved: §7 now gives BN20's actual figures and what they measure. |
| m12 | Resolved (index i, units stated). |
| m13 | Open (R2-4). |
| m14 | Resolved. |
| ToC depth | Resolved (depth 2; the contents now run onto p. 2, which is acceptable). |

## Rendered pages

23 pp, within the cap. No overfull lines. The new displays in Lemmas 4.7 and 4.8 and in the (SD) item are set
cleanly (p. 15). Tables 1–3 fit the text width. Problems: §A.3 has wide inter-word spacing (R2-3) and
bibliography entry [2] is underfull (R2-4). Link colours are unchanged (dark blue). No banned words, and no
sentence credits one author.

## Errata and deviations

None in the pinned sources. One discrepancy between the paper and its cited notes is reported as R2-1 (AMENDMENTS
N5 versus "complete proofs").

---

# Round 3 (bound to commit 05ad2cbe; narrow final check)

Target: commit `05ad2cbe`, `papers/LP/main.pdf` (23 pp). Diff reviewed: `git diff b6d1cca3 05ad2cbe -- papers/LP`.
Rulings accepted as given: R2-2 (the approval sentence and the verification-evidence sentences stay), R2-4 (the
repository paths are the citation), R2-11 (Las97 without a title).

```
0b565f28b54772e4c97fdf9eba2211bedc4aadad4aa17bb2223ae48dd920f0b3  sections/abstract.tex
9750a5c33b4e36c45f9bc1685d7891c1c8ab40de60a36665e5a2cbdea66096e0  sections/barrier.tex
88d8549265fcf2e97a4b2072921a9aca54849594f5fee82d312e78111f2d8474  sections/formal.tex
5835916c965ff3a6d1e6e38695ddc64b75d9249ed530821c2b83420b401e8755  sections/intro.tex
bb295fbc845e0807abb888bbf7fec42e515f9f459c10655b48ccd940f4213729  sections/outlook.tex
22c8477a68f497148d9d78bc8a0b1b9ab42fef4540be9aea880e0bc8c844e724  sections/planar.tex
cf3c7f8402a1db88a582585d397fb53cd35fa07e6f1ef6374ae4c98642f2718c  sections/resonant.tex
fc1177df942b90dae4898bc278e8e9ff89c6d9d03e7d5c54e617f491f79a7d36  sections/results.tex
46b48ebd3c541d54d88463b24202e84ff18cf3ebf0c417f553a3a5631e5e520e  sections/spatial.tex
```

Checks run: every changed line read; a fresh build in a scratch directory (23 pp, 0 overfull boxes, no undefined
references); pages 18–23 rendered and inspected.

## Verdict: PASS WITH NOTES

R2-1, R2-6, R2-7 and R2-10 are resolved. R2-8 and R2-9 are resolved in substance. R2-5 is resolved only in part.
The change introduced one cosmetic issue (R3-2). Nothing here blocks submission.

## Status of round-2 findings

| Item | Status |
|---|---|
| R2-1 | **Resolved, honestly.** `planar.tex:81` now reads "More detailed proofs, with constants, are in the supplementary proof notes~\cite{KAMnotes} (Lemmas~9--11 there), where the standard flow estimates of the Lie step are also only sketched." `intro.tex` reads "More detailed proofs are written out in~\cite{KAMnotes}." This matches AMENDMENTS N5. |
| R2-5 | **Partly resolved (R3-1).** |
| R2-6 | Resolved ("… two adjacent annuli can touch or a planet can reach the star"). |
| R2-7 | Resolved: §6 now says "As explained in Section~1, Theorem~E is close to …" and the duplicated hedge is gone. |
| R2-8 | Resolved in substance. Uniqueness is now attributed correctly ("uniqueness as in Theorem~B"). The proof of Theorem C now verifies (SD) explicitly, with the spatial ball. Lemma 4.8 now says "the maximal solution". Still left: the redundant "$\Lambda^0\in\Lset$ and $C(0)\le B(\Lambda^0)-\delta$" after "admissible", and the §6.3 restatement of (SD) without "the solution exists at time $u$". Both are harmless, since admissibility and maximality make them implicit. |
| R2-9 | ζ removed. `ρ` in the proof of Lemma 3.6 (`barrier.tex:105`) is unchanged; it is local to that proof and causes no confusion on the page. `k` noted only, per the earlier ruling. |
| R2-10 | Resolved (the cell is removed). |

Also checked: the shortened novelty sentence in `intro.tex:34` now claims novelty only for the Diophantine drift
and time exponents of Theorems B–D, keeps the Niederman caveat, and stays consistent with the B1 ruling. The
added bibliography notes ("page, section and table numbers cited refer to this version") are standard practice
and contain no jargon.

## Round-3 findings

**R3-1 (MINOR). The replacement sentence in §3 is still not accurate.**
- `barrier.tex` (end of the proof of Theorem A, p. 10): "The next lemma, the only place where the drift of the
  actions is compared with the threshold, converts action drift into margin drift."

The proof of Theorem B also makes this comparison ($B(\Lambda(u))\le B(\Lambda^0)+\Omega_B(r)$ in the stopped
drift display), and so does Lemma 6.2(ii).
*Repair:* drop the qualifier, leaving "The next lemma converts action drift into margin drift."

**R3-2 (MINOR, new). Bibliography [6] prints the year twice:** "Jacques Laskar, Astron. Astrophys. **317** (1997),
L75, 1997." (p. 23). The `@misc` entry has both `howpublished` containing "(1997)" and `year = {1997}`.
*Repair:* write `howpublished = {Astron. Astrophys. \textbf{317}, L75}` and keep `year`, or drop the
`year` field.

## Rendered pages 18–23

Clean. The display in Lemma 6.2, Table 1 at the start of §6.3, Tables 2 and 3, and the references are all set
correctly, with no overfull lines. The wide spacing in the §A.3 paragraph of declaration names on pp. 21–22
remains. It is cosmetic; it was R2-3 and was not in this round's scope.

## Errata and deviations

None.
