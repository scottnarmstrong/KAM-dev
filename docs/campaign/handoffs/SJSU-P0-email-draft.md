# Draft email to Sansottera, Locatelli and Giorgilli (for Scott to send; not sent)

**To:** Marco Sansottera, Ugo Locatelli, Antonio Giorgilli
**Subject:** Degree-18 secular SJSU Hamiltonian of your 2013/2017 papers: is the data available?

Dear Professors Sansottera, Locatelli and Giorgilli,

I am working, with Zohar Komargodski, on computer-assisted (Lean-verified) bounds for long-time
stability in planetary models, and your planar secular model of the Sun–Jupiter–Saturn–Uranus
system (Math. Comput. Simul. 88 (2013) 1–14, and Regul. Chaotic Dyn. 22 (2017) 54–77) is the
natural first target beyond two planets. We have regenerated the model from the recipe in your
section 3 (classical expansion, the two Kolmogorov-like steps with K_F = 8, and the resonant
step for 3λ₁ − 5λ₂ − 7λ₃), and we would be very grateful for help on a few points where the
published description leaves room for choice.

Would you be willing to share any of the following, if they still exist?

1. The coefficients of the secular Hamiltonian H^(sec) up to degree 18 (Appendix A of the 2013
   paper gives degrees 2 and 4).
2. The averaged semi-major axes a*₁, a*₂, a*₃ (hence Λ*), with the length of the numerical
   integration used to compute them, and whether the Table 1 elements were used directly as
   Poincaré elements.
3. The map from the Table 1 initial data to the secular coordinates and to the Table 2 values
   (x(0), y(0)): which transformations were applied to the initial point, and to which order.
4. A few implementation details of the Lie series, if you remember them: whether the frequency
   vector n* in the homological equations (6)–(7) includes the first-order correction
   ⟨∂h/∂L⟩ at zero eccentricities; the degree of χ₁ and χ₂ (the equations show 6, the closing
   remark of §3 says 9); and whether the series exp L_χ were summed to all orders within the
   truncations or stopped at a fixed order in the masses.

In our reconstruction the three-planet quartic coefficients of Appendix A are reproduced only
when terms of third order in the masses are kept, which suggests the latter. We also noticed
that the printed quartic has a small component that is not invariant under the common rotation
of the perihelia (terms of charge ±4 of size about 10⁻⁸, for example in the coefficients of
η₂²η₃², ξ₂²η₃² and ξ₂ξ₃η₂η₃), so that it does not exactly commute with the angular-momentum
deficit; we would be glad to know whether this comes from a numerical truncation in the
manipulator, or whether we are misreading a convention.

We intend to publish our regenerated model, scripts and comparison tables openly (CC BY 4.0
for the data), with full credit to your papers, and of course we would cite any data you are
able to share in whatever way you prefer.

With many thanks and best regards,

Scott Armstrong
CNRS, Sorbonne Université, and Courant Institute (NYU)
