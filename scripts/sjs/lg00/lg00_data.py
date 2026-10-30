#!/usr/bin/env python3
"""SJS-LG00: data of Locatelli & Giorgilli, "Invariant tori in the secular motions of the three-body planetary
systems", Celest. Mech. Dyn. Astron. 78 (2000) 47-74 (LG00), transcribed by hand from the local copy (text layer for
the digits, page image of p. 24 for the monomials; both agree on all 69 entries).  Data only.

H11: eq. (11) as printed in Appendix A, without its additive constant ("we neglected the additive constant because
it has no influence on the equations of motion"):
    H(xi1, xi2, eta1, eta2) = sum c * xi1^i1 xi2^i2 eta1^j1 eta2^j2,   exponents (i1, i2, j1, j2),
69 monomials of degree 2, 4, 6 -- every monomial of these degrees that is even in eta (the symmetry
(xi, eta) -> (xi, -eta) of the paper's eq. (15)).  All coefficients are negative as printed.
The coefficients are exact decimals (Fraction of the printed string): units AU, year, G = 1, solar mass (2 pi)^2
(LG00 Table 1), so frequencies are in rad/year.
(The action-angle form (15) of the same polynomial has 129 cosine terms; that is the "129 monomials" of SJS-FEAS.)
"""
from fractions import Fraction as F

H11 = [
    ("-7.9817980076760655e-5", (2, 0, 0, 0)),
    ("-3.8147366852664142e-5", (1, 1, 0, 0)),
    ("-1.0268297004552840e-4", (0, 2, 0, 0)),
    ("-7.7243404322933866e-5", (0, 0, 2, 0)),
    ("-3.3707608458413656e-5", (0, 0, 1, 1)),
    ("-9.9999984803151030e-5", (0, 0, 0, 2)),
    ("-5.6436223750712493e-4", (4, 0, 0, 0)),
    ("-1.6416392742006527e-3", (3, 1, 0, 0)),
    ("-6.2973632765649690e-3", (2, 2, 0, 0)),
    ("-2.2899781169560516e-3", (2, 0, 2, 0)),
    ("-3.4760626376493233e-3", (2, 0, 1, 1)),
    ("-4.2185659067704027e-3", (2, 0, 0, 2)),
    ("-8.3857323933716650e-3", (1, 3, 0, 0)),
    ("-1.3039354499285056e-3", (1, 1, 2, 0)),
    ("-4.7425253805301244e-3", (1, 1, 1, 1)),
    ("-6.8531825574944021e-3", (1, 1, 0, 2)),
    ("-6.2286577646952779e-3", (0, 4, 0, 0)),
    ("-3.9500271580332256e-3", (0, 2, 2, 0)),
    ("-8.3527962865484184e-3", (0, 2, 1, 1)),
    ("-1.1373126532783053e-2", (0, 2, 0, 2)),
    ("-1.7268965474147260e-3", (0, 0, 4, 0)),
    ("-3.1475592574520577e-3", (0, 0, 3, 1)),
    ("-6.6349860468623900e-3", (0, 0, 2, 2)),
    ("-6.8332272847022573e-3", (0, 0, 1, 3)),
    ("-5.1387074709303473e-3", (0, 0, 0, 4)),
    ("-6.0701804574696823e-3", (6, 0, 0, 0)),
    ("-3.2119532714927534e-2", (5, 1, 0, 0)),
    ("-2.7549740027179186e-1", (4, 2, 0, 0)),
    ("-7.4777792652719661e-2", (4, 0, 2, 0)),
    ("-2.0878989193600397e-1", (4, 0, 1, 1)),
    ("-2.2556116819663772e-1", (4, 0, 0, 2)),
    ("-1.2799874137338532e0", (3, 3, 0, 0)),
    ("-2.1957803068778765e-1", (3, 1, 2, 0)),
    ("-1.0754609127577874e0", (3, 1, 1, 1)),
    ("-1.2525556241525955e0", (3, 1, 0, 2)),
    ("-3.0996153271501390e0", (2, 4, 0, 0)),
    ("-6.4320374599537216e-1", (2, 2, 2, 0)),
    ("-3.9977642968441485e0", (2, 2, 1, 1)),
    ("-4.7878280093164562e0", (2, 2, 0, 2)),
    ("-1.3017334854810814e-1", (2, 0, 4, 0)),
    ("-5.6443027855889856e-1", (2, 0, 3, 1)),
    ("-1.6091206979341728e0", (2, 0, 2, 2)),
    ("-2.4623339524089656e0", (2, 0, 1, 3)),
    ("-1.6707157626697120e0", (2, 0, 0, 4)),
    ("-3.2771819750467199e0", (1, 5, 0, 0)),
    ("-6.5831703615139023e-1", (1, 3, 2, 0)),
    ("-6.1109646323834843e0", (1, 3, 1, 1)),
    ("-7.3380945672001685e0", (1, 3, 0, 2)),
    ("-1.8774424112239909e-1", (1, 1, 4, 0)),
    ("-1.0570482388082987e0", (1, 1, 3, 1)),
    ("-3.6262703950516264e0", (1, 1, 2, 2)),
    ("-6.1600785219363594e0", (1, 1, 1, 3)),
    ("-4.0619119716320187e0", (1, 1, 0, 4)),
    ("-1.2962091387801093e0", (0, 6, 0, 0)),
    ("-6.0253186540222901e-1", (0, 4, 2, 0)),
    ("-4.3130729937971006e0", (0, 4, 1, 1)),
    ("-5.0726955487757852e0", (0, 4, 0, 2)),
    ("-3.7694653469144916e-1", (0, 2, 4, 0)),
    ("-1.8736854171280113e0", (0, 2, 3, 1)),
    ("-5.8658678966225395e0", (0, 2, 2, 2)),
    ("-9.4014451177163672e0", (0, 2, 1, 3)),
    ("-6.2640076184402940e0", (0, 2, 0, 4)),
    ("-6.1464575048410168e-2", (0, 0, 6, 0)),
    ("-3.5591582332419240e-1", (0, 0, 5, 1)),
    ("-1.3743527471116275e0", (0, 0, 4, 2)),
    ("-3.3335872837233516e0", (0, 0, 3, 3)),
    ("-5.2949133058695930e0", (0, 0, 2, 4)),
    ("-5.0893561220459285e0", (0, 0, 1, 5)),
    ("-2.4875190197883796e0", (0, 0, 0, 6)),
]

# Table 2 (Laskar frequency analysis of the full three-body problem): n in rad/year, g in arcsec/year
TABLE2 = dict(n1="0.52989041594", n2="0.213454442910", g1="-30.06829", g2="-54.04533")
# Table 3: initial secular coordinates (xi, eta) of Jupiter (1) and Saturn (2), after the order-1 transformation
TABLE3 = dict(xi1="0.013902710681323937", eta1="-0.033461832907706032",
              xi2="0.021222294541265476", eta2="0.013936304647086138")
# eq. (12): secular frequencies of the model (11) from Table 3 (arcsec/year)
EQ12 = dict(g1="-30.03577993494953", g2="-53.33350277285140")
# Table 4: (I, phi) of the same point after the first three preliminary transformations (diagonalization,
# action-angle, Birkhoff to order 6)
TABLE4 = dict(I1="6.5759961186315956e-4", phi1="1.6385266516501007", I2="3.2097485037333470e-4",
              phi2="3.1140763924923589")
# Sect. 4.3: frequencies (rad/year) of the two orbits with xi1, eta1 scaled by 1 +- 0.02 (energy kept)
OMEGA_P = ("-0.0001456732145781655", "-0.0002592343751518042")      # omega'
OMEGA_PP = ("-0.0001455615260122723", "-0.0002579079711284839")     # omega''
# eq. (51): omega1/omega2 = (a + b g)/(c + d g), g = (sqrt 5 - 1)/2, and the centre of the omega2 range
GAMMA_P = dict(a=5797287, b=2625484, c=10316626, d=4672209, omega2="-0.000259234375151694060")
GAMMA_PP = dict(a=2899483, b=818219, c=5137345, d=1449732, omega2="-0.00025790797112834715")
# sect. 4.3: omega_{-,2}, omega_{+,2} of each curve
OMEGA2_ENDS = dict(p=("-0.00025923437525826712", "-0.00025923437504512100"),
                   pp=("-0.00025790797123354561", "-0.00025790797102314870"))
# eq. (52): energy level (interval) of the Table 4 point for H^(IV) truncated at s = 35
E52 = ("-1.6986715765408438e-7", "-1.6986715763842084e-7")
# Theorem 2 data reported in sect. 4.3
THM2 = dict(gamma="8e-6", tau=1, eps_R="0.840", eps_star="0.868", E="2e-6", Xi="1.2e4", rho_R="6", K=2,
            R1=33, R2=2048)
ARCSEC = 3.141592653589793 / 648000


def coeffs():
    """[(Fraction c, (i1, i2, j1, j2))]"""
    return [(F(s), e) for s, e in H11]
