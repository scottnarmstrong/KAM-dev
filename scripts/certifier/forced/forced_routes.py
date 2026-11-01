#!/usr/bin/env python3
"""V2-TOOLS #6: the route modules of a forced toy (witnesses from forced_witness.py).  Untrusted tooling.

    python3 -I scripts/certifier/forced/forced_routes.py TAG

Writes, under KAM/CertificateSharp/V2/Tests/Forced/:
  <TAG>Freq.lean    FreqEncloses of the box (root enclosure of √5, checkAlgBox, lunarRotFreqMinusN_eq) and the
                    Diophantine premise (lunarRotFreqMinusN_isDiophantine) at the certificate's γ, τ;
  <TAG>Claim.lean   the refined claim R: the disc pass and the frame majorants (N and T through the memoized
                    stages of <TAG>Base);
  <TAG>RouteA.lean  route A at the refined data and with lever L8': witnesses, the sites, the cores, the whole
                    v2 certifier at `routeV2All` and the certified torus.
"""
import json
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import forced_emit as FE            # noqa: E402
import forced_lean as FL            # noqa: E402

ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
LEAN_DIR = os.path.join(ROOT, "KAM", "CertificateSharp", "V2", "Tests", "Forced")
MOD = "KAM.CertificateSharp.V2.Tests.Forced."


def q(x):
    return FE.FM.lean_q(F(x))


def q2(x):
    """a rational on one line, or split after `/` when it is too long."""
    t = "  " + q(x)
    if len(t) <= 100:
        return t
    x = F(x)
    return "  (%d /\n    %d)" % (x.numerator, x.denominator)


def list_items(name, xs):
    """wrap tokens of `name := [x0, ..., xk]` (the wrap separator supplies the commas)."""
    xs = [q(x) for x in xs]
    if len(xs) == 1:
        return ["%s := [%s]" % (name, xs[0])]
    return ["%s := [%s" % (name, xs[0])] + xs[1:-1] + [xs[-1] + "]"]


def lines_ok(text):
    for ln in text.split("\n"):
        assert len(ln) <= 100, ln
    return text


def freq_module(tag, c):
    lo, hi = c.root
    N = c.toy.N
    kap = c.toy.kappa
    return lines_ok(FE.HEADER + """public import %(mod)s%(T)sData
public import KAM.SpinOrbit.RotFreqN
public import KAM.Certificate.Freq

/-!
# The reference frequency of the forced toy `%(T)s`

`ω* = κ (ν₋(%(N)d) - 1, 1) = lunarRotFreq (lunarNuMinusN %(N)d) κ`, `κ = %(kq)s`: the box of
`%(T)s.cert` encloses it (`freq`: a root enclosure of `√5` and `checkAlgBox` at the exact `ℚ(√5)`
description `lunarRotFreqMinusN_eq`), and it is `(κ / %(N2)d, 1)`-Diophantine
(`lunarRotFreqMinusN_isDiophantine`), which is the certificate's `(γ, τ)` (`dio`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.%(T)s

open KAM KAM.Certificate KAM.SpinOrbit

/-- The scale `κ = c / s` of the reference vector. -/
def κ : ℚ := %(kq)s

/-- The reference vector `κ (ν₋(%(N)d) - 1, 1)`. -/
noncomputable def ωstar : Fin 2 → ℝ := lunarRotFreq (lunarNuMinusN %(N)d) κ

/-- The lower end of the enclosure of `√5`. -/
def rootLo : ℚ :=
%(lo)s

/-- The upper end of the enclosure of `√5`. -/
def rootHi : ℚ :=
%(hi)s

theorem freq : FreqEncloses 2 cert.freqBox ωstar := by
  have hx := sqrt_mem_of_checkRootEnclosure
    (show checkRootEnclosure 2 5 rootLo rootHi = true by decide +kernel)
  rw [Nat.cast_ofNat] at hx
  rw [ωstar, lunarRotFreqMinusN_eq]
  exact algFreq_encloses hx (by decide +kernel)

theorem dio : IsDiophantine ((cert.params.γ : ℚ) : ℝ) ((cert.params.tau : ℕ) : ℝ) ωstar := by
  have h := lunarRotFreqMinusN_isDiophantine %(N)d (by norm_num) (κ := κ) (by norm_num [κ])
  have hγ : ((cert.params.γ : ℚ) : ℝ) = (κ : ℝ) / ((%(N)d : ℕ) + 2) := by
    rw [show cert.params.γ = κ / %(N2)d by decide +kernel]
    push_cast
    norm_num
  have hτ : ((cert.params.tau : ℕ) : ℝ) = 1 := by
    rw [show cert.params.tau = 1 by decide +kernel]
    norm_num
  rw [hγ, hτ]
  exact h

end KAM.CertificateSharp.V2.Forced.%(T)s

end
""" % dict(mod=MOD, T=tag, N=N, N2=N + 2, kq=q(kap), lo=q2(lo), hi=q2(hi)))


def claim_module(tag, W):
    R = W["R"]
    Rs = ", ".join("%s := %s" % (k, q(R[k])) for k in ("dh", "dx", "d2x", "d2h", "bL", "bN", "bNt", "bT"))
    return lines_ok(FE.HEADER + """public import %(mod)s%(T)sBase
public import KAM.CertificateSharp.V2.RouteARefinedEngine

/-!
# The refined claim of the forced toy `%(T)s`

`Rclaim`: the four sums of the disc pass and the frame bounds, from the producer's mirror values
rounded up by `10⁻⁴`. `hamClaim_ok` is the disc pass (`checkHamClaim`); `frame_ok` the frame
majorants of C4, `checkFrameN` and `checkFrameT` through the memoized stages of `%(T)sBase`
(`checkFrameN_eq_of`, `checkFrameT_eq_of`), so the frame and the torsion share one kernel
computation of each stage.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.%(T)s

open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- The refined claim (bounds on `H` and the frame). -/
def Rclaim : RefClaim :=
%(Rs)s

theorem hamClaim_ok : checkHamClaim cert Rclaim = true := by decide +kernel

/-- The assembled torsion matrix of `torsionModels_eq_of_stages`. -/
noncomputable def Tmat : ModelMatrix FB := buildMat (2 + 1) (2 + 1) fun i j =>
  if i < 2 then
    (if j < 2 then modelMatrixEntry Tb i j else freqModel 2 cert.freqBox cert.params.s i)
  else (if j < 2 then modelMatrixEntry Y 0 j else zeroModel)

theorem T_eq : torsionModels 2 cert.ham cert.emb cert.wit cert.gramInv db cert.freqBox cert.params.s
    cert.weight cert.cfgLow cert.piEnc = some Tmat :=
  torsionModels_eq_of_stages 2 cert.ham cert.emb cert.wit cert.gramInv db cert.freqBox cert.params.s
    cert.weight cert.cfgLow cert.piEnc eps_eq ms_eq L_eq Gi_eq DL_eq N0_eq DG1_eq DG2_eq DGi0_eq
    DGi1_eq DN1_eq DN2_eq XN1_eq Tb_eq Y_eq

theorem frameL_ok : checkFrameL cert Rclaim.bL = true := by decide +kernel

theorem frameN_ok : checkFrameN cert Rclaim.bN Rclaim.bNt = true := by
  rw [checkFrameN_eq_of gram_eq eps_eq (frameNModels_eq_of_stage 2 cert.emb cert.gramInv eps
    cert.weight cert.cfgLow cert.piEnc L_eq Gi_eq N0_eq)]
  decide +kernel

theorem frameT_ok : checkFrameT cert Rclaim.bT = true := by
  rw [checkFrameT_eq_of gram_eq T_eq]
  decide +kernel

theorem frameOm_ok : checkFrameOmega cert (freqNormUp cert.freqBox) = true := by decide +kernel

theorem frame_ok : checkFrameMajorants cert (Rclaim.frame cert.freqBox) = true := by
  show (checkFrameL cert Rclaim.bL && checkFrameN cert Rclaim.bN Rclaim.bNt &&
    checkFrameT cert Rclaim.bT && checkFrameOmega cert (freqNormUp cert.freqBox)) = true
  rw [frameL_ok, frameN_ok, frameT_ok, frameOm_ok]
  rfl

end KAM.CertificateSharp.V2.Forced.%(T)s

end
""" % dict(mod=MOD, T=tag, Rs=FE.wrap("  { ", Rs.split(", "), indent="    ", close=" }")))


def bite(s):
    if s is None:
        return "none"
    return "some ⟨%s, %d, %d, %s⟩" % (q(s["E1"]), s["l"], s["J"], q(s["B"]))


def refined_wit_def(name, W, doc):
    w = W["core"]
    items = ["Xs := %s" % q(w["Xs"]), "kp := %d" % w["kp"], "th := %s" % q(w["th"]),
             ] + list_items("c", w["c"]) + list_items("cbar", w["cbar"]) + ["ctail := %s" % q(w["ctail"])] + ["%s := %s" % (k, q(w[k])) for k in
                                                 ("sB", "sT", "sLt", "sN", "sNt", "t")] + ["J := %d" % w["J"]]
    core = FE.wrap("    { ", items, indent="      ", close=" }")
    sites = ["(%s,\n      %s)" % (bite(a), bite(b)) for a, b in W["sites"]]
    return """/-- %s -/
def %s : RefinedWit where
  core :=
%s
  R := Rclaim
  κ := %s
  sites :=
    [%s]
""" % (doc, name, core, q(W["kappa"]), ",\n     ".join(sites))


def routeA_module(tag, W, WR=None):
    T = tag
    body = refined_wit_def("refinedWit", W, "The refined route-A witness of `%s`." % T)
    parts = [FE.HEADER, "public import %s%sClaim\npublic import %s%sFreq\n" % (MOD, T, MOD, T),
             "public import %sLemmas\n" % MOD,
             "public import KAM.CertificateSharp.V2.RouteAll\n\n"]
    parts.append("""/-!
# Route A on the forced toy `%(T)s`, in the kernel

* `refinedWit`: route A at the refined data (`iso_g1_v2A`): the claim `Rclaim`, certified
  small-divisor sites at every bite of the prefix (`siteOk` with the balanced fibered checker),
  the classical tail; `X⋆ = %(Xs)s`, threshold `e* = X⋆ γ⁴ δ₀⁴ ≈ %(estar).2e` against
  `err = %(err)s`;
* `refinedA_passes`: the whole v2 certifier at `routeV2All` with the witness of `routeARefined`
  (the landed sub-checks from `%(T)sBase`, the claim from `%(T)sClaim`);
* `refinedA_torus`: the certified torus at the reference frequency
  (`checkTorusCertificateV2_sound`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.%(T)s

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

""" % dict(T=T, Xs=q(W["Xs"]), estar=float(W["estar"]), err=q(W["err"])))
    parts.append(body)
    parts.append("""
theorem refinedA_sites : sitesOk (refinedWit.num 2 cert.params cert.freqBox) refinedWit.core.J
    cert.freqBox refinedWit.κ cert.params.γ refinedWit.sites = true := by decide +kernel

theorem refinedA_core : refinedCore 2 cert.params cert.freqBox refinedWit = true :=
  refinedCore_of (by decide +kernel) (by decide +kernel) (by decide +kernel) refinedA_sites
    (by decide +kernel) (by decide +kernel)

theorem refinedA_test : refinedTest cert refinedWit = true := by
  have h1 : checkHamClaim cert refinedWit.R = true := hamClaim_ok
  have h2 : checkFrameMajorants cert (refinedWit.R.frame cert.freqBox) = true := frame_ok
  show (checkHamClaim cert refinedWit.R &&
    checkFrameMajorants cert (refinedWit.R.frame cert.freqBox) &&
    refinedCore 2 cert.params cert.freqBox refinedWit) = true
  rw [h1, h2, refinedA_core]
  rfl

/-- **The forced toy through `routeV2All`**, at the witness of `routeARefined`. -/
theorem refinedA_passes : checkTorusCertificateV2 routeV2All cert
    (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr refinedWit))))) = true := by
  rw [checkTorusCertificateV2_routeV2All_aRefined]
  refine (checkV2_eq routeARefined cert refinedWit).trans ?_
  rw [base_ok, Bool.true_and]
  exact (routeARefined_test cert refinedWit).trans refinedA_test

/-- **The certified torus of the forced toy `%(T)s`** at `κ (ν₋(%(N)d) - 1, 1)`. -/
theorem refinedA_torus : CertifiedTorus cert ωstar :=
  checkTorusCertificateV2_sound routeV2All refinedA_passes freq dio
""" % dict(T=T, N=W["N"]))
    if WR is not None:
        parts.append("""
/-- The witness of route A with lever L8′ (`Ref.iso_g1_branch_R`). -/
def refinedWitR : RefinedWitR where
  base := refinedWit
  bF := %(bF)s
  bT := %(bT)s

theorem refinedR_core : refinedCoreR 2 cert.params cert.freqBox refinedWitR = true :=
  refinedCoreR_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    refinedA_sites (by decide +kernel) (by decide +kernel)

/-- The forced toy through `routeV2All` with lever L8′. -/
theorem refinedR_passes : checkTorusCertificateV2 routeV2All cert
    (Sum.inr (Sum.inl (Sum.inl (Sum.inr refinedWitR)))) = true := by
  rw [checkTorusCertificateV2_routeV2All_aRefinedR]
  refine (checkV2_eq routeARefinedR cert refinedWitR).trans ?_
  rw [base_ok, Bool.true_and]
  refine (routeARefinedR_test cert refinedWitR).trans ?_
  have h1 : checkHamClaim cert refinedWitR.base.R = true := hamClaim_ok
  have h2 : checkFrameMajorants cert (refinedWitR.base.R.frame cert.freqBox) = true := frame_ok
  show (checkHamClaim cert refinedWitR.base.R &&
    checkFrameMajorants cert (refinedWitR.base.R.frame cert.freqBox) &&
    refinedCoreR 2 cert.params cert.freqBox refinedWitR) = true
  rw [h1, h2, refinedR_core]
  rfl
""" % dict(bF=q(WR["bF"]), bT=q(WR["bT"])))
    parts.append("\nend KAM.CertificateSharp.V2.Forced.%s\n\nend\n" % T)
    return lines_ok("".join(parts))


def write(tag, name, text):
    with open(os.path.join(LEAN_DIR, "%s%s.lean" % (tag, name)), "w") as fh:
        fh.write(text)


def main(tag):
    import forced_witness as FW
    c = FW.load(tag)
    W = FW.refined_A(c, tag)
    p = c.params
    d0 = min(F(1), (p["rho"] - p["rhoInf"]) / 6)
    W["estar"] = W["Xs"] * p["gamma"] ** 4 * d0 ** 4
    W["err"] = p["err"]
    W["N"] = c.toy.N
    ok = FW.check_in_lean(tag, FW.lean_refined_wit(W))
    assert all(FL.parse_bool(o) for o in ok), ok
    WR = FW.refined_R(tag, W)
    print("L8'", WR and (str(WR["bF"]), str(WR["bT"])))
    write(tag, "Freq", freq_module(tag, c))
    write(tag, "Claim", claim_module(tag, W))
    write(tag, "RouteA", routeA_module(tag, W, WR))
    out = os.path.join(ROOT, "scripts", "certifier", "fixtures", "forced-toy", "%s_witness.json" % tag)
    with open(out, "w") as fh:
        json.dump(FW.jsonable(dict(refinedA={k: v for k, v in W.items() if k != "claim_values"},
                                   claim_values=W["claim_values"], refinedR=WR)), fh, indent=1, sort_keys=True,
                  default=str)
    return W, WR


if __name__ == "__main__":
    main(sys.argv[1])


def bsite(t):
    return "(%s,\n      %s,\n      %s)" % tuple(bite(x) for x in t)


def runB_items(W):
    caps = W["caps"]
    cl, cpl, cbl, ctail, cbtail = W["consts"]
    return (["Xs := %s" % q(W["Xs"]), "kp := %d" % W["kp"], "a := 2", "ybar := 1 / 2", "θ := 1 / 16",
             "θξ := 1 / 8", "θΩ := 1 / 8", "q := 1 / 8", "θN := 1 / 8", "θω := 1 / 8", "ts := 1 / 10",
             "bF := %s" % q(caps["bF"]), "selfcons := false", "lam0 := %s" % q(caps["lam0"]),
             "lamW0 := %s" % q(caps["lamW0"]), "ePer0 := %s" % q(caps["ePer0"]),
] + list_items("c", cl) + list_items("c'", cpl) + list_items("cbar", cbl) +
            ["ctail := %s" % q(ctail), "cbtail := %s" % q(cbtail)]
            + ["%s := %s" % (k, q(caps[k])) for k in ("sB", "sT", "sLt", "sN", "sNt")] + ["J := %d" % W["J"]])


def routeB_module(tag, W):
    T = tag
    core = FE.wrap("    { ", runB_items(W), indent="      ", close=" }")
    sites = ",\n     ".join(bsite(t) for t in W["sites"])
    return lines_ok(FE.HEADER + """public import %(mod)s%(T)sClaim
public import %(mod)s%(T)sFreq
public import %(mod)sLemmas

/-!
# Route B on the forced toy `%(T)s`, in the kernel

`refinedBWit`: route B at the refined data (`iso_g1_branch_B`), with the claim `Rclaim` of
`%(T)sClaim` and certified small-divisor sites at the three bites of each prefix stage (`δ_s`, the
split bite, `min r_s 1`); `X⋆ = %(Xs)s`, threshold `γ⁴ρ⁴ / c₁ ≈ %(estar).2e` against
`err = %(err)s`. `refinedB_passes` is the whole v2 certifier at `routeV2All` with the
witness of `routeBRefined`, and `refinedB_torus` the certified torus.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.%(T)s

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- The refined route-B witness of `%(T)s`. -/
def refinedBWit : RefinedBWit where
  core :=
%(core)s
  R := Rclaim
  κ := %(kap)s
  sites :=
    [%(sites)s]

theorem refinedB_sites : (refinedBWit.num cert.params cert.freqBox).sitesOk 2 refinedBWit.core.J
    cert.freqBox refinedBWit.κ cert.params.γ refinedBWit.sites = true := by decide +kernel

theorem refinedB_core : refinedBCore 2 cert.params cert.freqBox refinedBWit = true :=
  refinedBCore_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) refinedB_sites (by decide +kernel) (by decide +kernel)

/-- **The forced toy through `routeV2All`**, at the witness of `routeBRefined`. -/
theorem refinedB_passes : checkTorusCertificateV2 routeV2All cert
    (Sum.inr (Sum.inr (Sum.inr refinedBWit))) = true := by
  rw [checkTorusCertificateV2_routeV2All_bRefined]
  refine (checkV2_eq routeBRefined cert refinedBWit).trans ?_
  rw [base_ok, Bool.true_and]
  refine (routeBRefined_test cert refinedBWit).trans ?_
  have h1 : checkHamClaim cert refinedBWit.R = true := hamClaim_ok
  have h2 : checkFrameMajorants cert (refinedBWit.R.frame cert.freqBox) = true := frame_ok
  show (checkHamClaim cert refinedBWit.R &&
    checkFrameMajorants cert (refinedBWit.R.frame cert.freqBox) &&
    refinedBCore 2 cert.params cert.freqBox refinedBWit) = true
  rw [h1, h2, refinedB_core]
  rfl

/-- **The certified torus of `%(T)s` through route B.** -/
theorem refinedB_torus : CertifiedTorus cert ωstar :=
  checkTorusCertificateV2_sound routeV2All refinedB_passes freq dio

end KAM.CertificateSharp.V2.Forced.%(T)s

end
""" % dict(mod=MOD, T=T, Xs=q(W["Xs"]), estar=float(W["estar"]), err=q(W["err"]), core=core, kap=q(W["kappa"]),
           sites=sites))


def frozen_module(tag, A, B):
    T = tag
    itemsA = (["Xs := %s" % q(A["Xs"]), "kp := %d" % A["kp"], "th := %s" % q(A["th"]),
] + list_items("c", A["c"]) + list_items("cbar", A["cbar"]) + ["ctail := %s" % q(A["ctail"])] + ["%s := %s" % (k, q(A[k])) for k in
                                                ("sB", "sT", "sLt", "sN", "sNt", "t")] + ["J := %d" % A["J"]])
    coreA = FE.wrap("  { ", itemsA, indent="    ", close=" }")
    coreB = FE.wrap("  { ", runB_items(B), indent="    ", close=" }")
    return lines_ok(FE.HEADER + """public import %(mod)s%(T)sBase
public import %(mod)s%(T)sFreq
public import %(mod)sLemmas

/-!
# The sharp and frozen routes on the near-integrable forced toy `%(T)s`, in the kernel

`%(T)s` has `err = %(err)s`, below the thresholds of the landed sharp
engine and of the frozen forms of routes A and B (sharp `%(es).2e`, frozen A `%(ea).2e`,
frozen B `%(eb).2e`), so every one of them passes on the same certificate:
* `sharp_passes`: `routeV2All` at `Sum.inl ()` (the landed certifier `checkTorusCertificateSharp`);
* `frozenA_passes`: the witness of `routeAFrozen` (classical constants, `M₁ = M₂ = M`);
* `frozenB_passes`: the witness of `routeBFrozen` (`iso_g1_v2B_frozen`);
and `sharp_torus`, `frozenA_torus`, `frozenB_torus` are the certified tori.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.%(T)s

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

theorem sharp_test : sharpTest cert = true := by decide +kernel

/-- **The landed sharp certifier on `%(T)s`**, through `routeV2All`. -/
theorem sharp_passes : checkTorusCertificateV2 routeV2All cert (Sum.inl ()) = true := by
  refine (checkV2_eq routeV2All cert (Sum.inl ())).trans ?_
  rw [base_ok, Bool.true_and]
  exact (sharpV2_test cert ()).trans sharp_test

theorem sharp_torus : CertifiedTorus cert ωstar :=
  checkTorusCertificateV2_sound routeV2All sharp_passes freq dio

/-- The frozen route-A witness of `%(T)s`. -/
def frozenWit : FrozenWit :=
%(coreA)s

theorem frozenA_core : frozenCore 2 cert.params cert.freqBox frozenWit = true := by decide +kernel

theorem frozenA_passes : checkTorusCertificateV2 routeV2All cert
    (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl frozenWit))))) = true := by
  rw [checkTorusCertificateV2_routeV2All_aFrozen]
  refine (checkV2_eq routeAFrozen cert frozenWit).trans ?_
  rw [base_ok, Bool.true_and]
  exact (routeAFrozen_test cert frozenWit).trans frozenA_core

theorem frozenA_torus : CertifiedTorus cert ωstar :=
  checkTorusCertificateV2_sound routeV2All frozenA_passes freq dio

/-- The frozen route-B witness of `%(T)s`. -/
def frozenBWit : RunBWit :=
%(coreB)s

theorem frozenB_core : frozenBCore 2 cert.params cert.freqBox frozenBWit = true := by decide +kernel

theorem frozenB_passes : checkTorusCertificateV2 routeV2All cert
    (Sum.inr (Sum.inr (Sum.inl frozenBWit))) = true := by
  rw [checkTorusCertificateV2_routeV2All_bFrozen]
  refine (checkV2_eq routeBFrozen cert frozenBWit).trans ?_
  rw [base_ok, Bool.true_and]
  exact (routeBFrozen_test cert frozenBWit).trans frozenB_core

theorem frozenB_torus : CertifiedTorus cert ωstar :=
  checkTorusCertificateV2_sound routeV2All frozenB_passes freq dio

end KAM.CertificateSharp.V2.Forced.%(T)s

end
""" % dict(mod=MOD, T=T, err=q(A["err"]), es=float(A["esharp"]), ea=float(A["estar"]), eb=float(B["estar"]),
           coreA=coreA, coreB=coreB))
