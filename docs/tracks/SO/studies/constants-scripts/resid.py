import pickle, numpy as np, math
TP = 2*math.pi
def load(which): return pickle.load(open('trunc_%s.pkl'%which,'rb'))
def eta(tr, L, frame, rho):
    """weighted-l1 bound of the scalar residual r = 2 pi R on the strip (log10)."""
    d = tr[L]; k, l, lm = d['k'], d['l'], d['log10mag']
    if frame == 'theta':  wexp = rho*(np.abs(k) + np.abs(l-k))
    elif frame == 'rect': wexp = 2*rho*np.abs(k) + rho*np.abs(l)
    else:                 wexp = rho*(np.abs(k) + np.abs(l))
    lw = lm + TP*wexp/math.log(10)
    mx = lw.max()
    return mx + math.log10(np.sum(10**(lw-mx))) + math.log10(2) + math.log10(TP)
if __name__ == "__main__":
    for which in ['lower','upper']:
        tr = load(which)
        print(which, "check vs analyze.py rect rho=0.005 L=110:", 10**eta(tr,110,'rect',0.005), " L=60:", 10**eta(tr,60,'rect',0.005))
        for L in sorted(tr):
            print(L, tr[L]['nv'], tr[L]['nE'], tr[L]['vbox'], "eta_rect(0.005) %.2f  eta_theta(0.005) %.2f  eta_rot(0.01) %.2f eta_theta(0.01) %.2f eta_theta(0.02) %.2f" % (
                eta(tr,L,'rect',0.005), eta(tr,L,'theta',0.005), eta(tr,L,'rot',0.01), eta(tr,L,'theta',0.01), eta(tr,L,'theta',0.02)))
