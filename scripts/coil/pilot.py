"""Untrusted, source-pinned coil KAM scope pilot; no proof certificate is produced.

Requires NumPy and mpmath. Uses the Apache-2.0 PlasmaLean contributors' oracle
at the revision below, cloned by the reproduction driver. Scratch only output.
The inherited Galerkin basis, stable segment formula and analytic Jacobian are
reused; this driver recovers the missing initial torus from committed Lean data.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

resource.setrlimit(resource.RLIMIT_CPU, (3500, 3500))
ROOT = Path(__file__).resolve().parents[2]
UP = ROOT / '.drafts/coil/PlasmaLean'
PIN = '79b6152e779a62287da76fb4a49918e38575b3d6'
assert subprocess.check_output(['git', '-C', str(UP), 'rev-parse', 'HEAD'], text=True).strip() == PIN
sys.path.insert(0, str(UP / 'scripts/coil_kam_oracle'))
import numpy as np
import mpmath as mp
import coil
import refit


def seed(g):
    src = (UP / 'PlasmaLean/Design/CoilKamData.lean').read_text()
    body = src.split('def ckRecs : List TRec := [')[1].split('\n]')[0]
    recs = [list(map(int, re.findall(r'-?\d+', row)))
            for row in re.findall('⟨([^⟩]+)⟩', body)]
    assert len(recs) == 281 and all(len(r) == 6 for r in recs)
    data = {(k, m): np.array(v, float) / 2**100 for k, m, *v in recs}
    arr = np.array([data.get(km, np.zeros(4)) for km in g.H])
    return g.pack(*arr.T)


def save(g, x, out):
    np.savez(out, H=np.array(g.H), a=g.unpack(x)[0], ap=g.unpack(x)[1],
             b=g.unpack(x)[2], bp=g.unpack(x)[3], N=g.N, M=g.M, iota=refit.IOTA)


def evaluate(d, th, ph):
    H = d['H']; a, ap, b, bp = [d[s] for s in ('a', 'ap', 'b', 'bp')]
    arg = np.asarray(th)[..., None] * H[:, 0] + np.asarray(ph)[..., None] * H[:, 1]
    c, s = np.cos(arg), np.sin(arg)
    return np.stack([c @ a + s @ ap, c @ b + s @ bp], -1)


def fit(args):
    receipts = []
    g = None
    for spec in args.plan:
        n, m = map(int, spec.split('x'))
        t = time.process_time()
        newg = (refit.Galerkin(n, m, Nt=2*n+4, Np=2*m+4) if n >= 20
                else refit.Galerkin(n, m))
        if g is None and args.start:
            d = np.load(args.start)
            g = refit.Galerkin(int(d['N']), int(d['M']), Nt=1, Np=1)
            x = g.pack(*[d[s] for s in ('a','ap','b','bp')])
        x = seed(newg) if g is None else refit.regrid(x, g, newg)
        g = newg
        x = refit.newton(g, x, steps=5, tol=3e-15)
        # Independent, shifted, oversampled grid; no collocation-only success.
        h = refit.Galerkin(n, m, Nt=3*n+9, Np=3*m+11)
        h.phi = h.phi + .137
        arg = np.outer(h.T + .071, h.ks) + np.outer(h.C + .137, h.ms)
        h.Cs, h.Sn = np.cos(arg), np.sin(arg)
        er, ez = h.residual(x)
        R, Z, _, _ = h.torus(x)
        ff = [np.fft.fft2(v.reshape(h.Nt, h.Np))/(h.Nt*h.Np) for v in (er, ez)]
        kk = np.abs(np.fft.fftfreq(h.Nt)*h.Nt)[:, None]
        mm = np.abs(np.fft.fftfreq(h.Np)*h.Np)[None, :]
        r = dict(N=n, M=m, unknowns=len(x), grid=[h.Nt, h.Np],
                 sup=[float(abs(er).max()), float(abs(ez).max())],
                 l1_r0063=[float((abs(f)*np.exp(.063*(kk+mm))).sum()) for f in ff],
                 R_range=[float(R.min()), float(R.max())],
                 Z_range=[float(Z.min()), float(Z.max())],
                 cpu_seconds=time.process_time()-t)
        print(json.dumps(r), flush=True)
        receipts.append(r)
        save(g, x, ROOT/f'.drafts/coil/torus-{n}x{m}.npz')
        del h
    return receipts


def trace(args):
    d = np.load(args.torus)
    th = np.arange(4)*np.pi/2
    y0 = evaluate(d, th, np.zeros(4))
    results = []
    for steps in (64, 128, 256):
        y = y0.copy(); dt=2*np.pi/steps
        def rhs(ph, v):
            c, s = np.cos(ph), np.sin(ph)
            R = v[:, 0]
            B = coil.field(np.stack([R*c, R*s, v[:, 1]], -1))
            return R[:, None]*np.stack([c*B[:, 0]+s*B[:, 1], B[:, 2]], -1)/(-s*B[:, 0]+c*B[:, 1])[:, None]
        for j in range(steps):
            ph = j*dt
            a=rhs(ph,y); b=rhs(ph+dt/2,y+dt*a/2)
            c=rhs(ph+dt/2,y+dt*b/2); e=rhs(ph+dt,y+dt*c)
            y += dt*(a+2*b+2*c+e)/6
        target=evaluate(d, th+2*np.pi*refit.IOTA, np.full(4,2*np.pi))
        r=dict(steps=steps, torus_error=float(abs(y-target).max()), final=y.tolist())
        results.append(r); print(json.dumps(r), flush=True)
    return results


def diagnostics(args):
    d=np.load(args.torus)
    H=d['H']; amps=np.max(np.abs(np.array([d[s] for s in ('a','ap','b','bp')])),axis=0)
    spectra={}
    for axis, label, stop in ((0,'theta',int(d['N'])), (1,'phi',int(d['M']))):
        shell=np.array([amps[np.abs(H[:,axis])==j].max() for j in range(stop+1)])
        sel=np.where((shell>1e-13)&(np.arange(stop+1)>3))[0]
        if label=='phi': sel=sel[sel%2==0]  # main spectrum; odd modes kept in all evaluations
        slope=float(-np.polyfit(sel,np.log(shell[sel]),1)[0])
        spectra[label]=dict(shell=shell.tolist(), fit_modes=sel.tolist(), decay=slope,
                           illustrative_cutoff_1e20=int(np.ceil(np.log(1e20)/slope)))
    th,ph=np.meshgrid(2*np.pi*np.arange(24)/24,2*np.pi*np.arange(48)/48,indexing='ij')
    rz=evaluate(d, th,ph); R,Z=rz[...,0],rz[...,1]
    y=np.stack([R*np.cos(ph),R*np.sin(ph),Z],-1)
    B=coil.field(y); Bphi=-np.sin(ph)*B[...,0]+np.cos(ph)*B[...,1]
    min_dist=np.inf
    for p,q in zip(coil.PP[:192],coil.QQ[:192]):
        v=q-p; tt=np.clip(((y-p)*v).sum(-1)/(v*v).sum(),0,1)
        min_dist=min(min_dist,float(np.linalg.norm(y-p-tt[...,None]*v,axis=-1).min()))
    complex_samples=[]
    for beta in (.03,.07,.12,.18,.24):
        pc=ph+1j*beta; rc=evaluate(d,th,pc)
        yc=np.stack([rc[...,0]*np.cos(pc),rc[...,0]*np.sin(pc),rc[...,1]],-1)
        bc=coil.field_c(yc)
        RB=yc[...,0]*bc[...,1]-yc[...,1]*bc[...,0]
        min_re=np.inf
        for p,q in zip(coil.PP,coil.QQ):
            v=q-p; tt=np.clip(((yc.real-p)*v).sum(-1)/(v*v).sum(),0,1)
            w=yc-p-tt[...,None]*v
            min_re=min(min_re,float(np.real((w*w).sum(-1)).min()))
        complex_samples.append(dict(beta=beta,min_abs_RBphi=float(abs(RB).min()),
                                    max_B=float(abs(bc).max()),min_Re_segQ=min_re))
    return dict(spectra=spectra,RBphi_range=[float((R*Bphi).min()),float((R*Bphi).max())],
                sampled_min_coil_distance=min_dist,complex_samples=complex_samples)


def precision(args):
    d=np.load(args.torus); mp.mp.dps=65
    H=d['H']; coeff=[[mp.mpf(float(v)) for v in d[s]] for s in ('a','ap','b','bp')]
    kap,p,q=coil.seg_arrays()
    # Recover the dyadic geometry exactly, not via decimal float string conversion.
    records=[(mp.mpf(k)/2**32,[mp.mpf(v)/2**32 for v in p],
              [mp.mpf(v)/2**32 for v in q]) for k,p,q in coil.SEGS]
    records += [(mp.mpf('0.5'),list(map(mp.mpf,p)),list(map(mp.mpf,q))) for p,q in coil.TF]
    def cross(a,b): return [a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]]
    def dot(a,b): return sum(u*v for u,v in zip(a,b))
    results=[]
    for th,ph in [('0.271','0.193'),('1.7','2.3'),('4.1','5.2')]:
        th,ph=mp.mpf(th),mp.mpf(ph)
        ang=[int(k)*th+int(m)*ph for k,m in H]
        c=list(map(mp.cos,ang));s=list(map(mp.sin,ang))
        a,ap,b,bp=coeff; iota=(75+mp.sqrt(5))/562
        R=sum(u*v+w*z for u,v,w,z in zip(a,c,ap,s)); Z=sum(u*v+w*z for u,v,w,z in zip(b,c,bp,s))
        lam=[int(m)+iota*int(k) for k,m in H]
        LR=sum(l*(-u*v+w*z) for l,u,v,w,z in zip(lam,a,s,ap,c))
        LZ=sum(l*(-u*v+w*z) for l,u,v,w,z in zip(lam,b,s,bp,c))
        cp,sp=mp.cos(ph),mp.sin(ph); y=[R*cp,R*sp,Z]; B=[mp.mpf(0)]*3
        for k,p,q in records:
            aa=[u-v for u,v in zip(p,y)];bb=[u-v for u,v in zip(q,y)]
            al,be=mp.sqrt(dot(aa,aa)),mp.sqrt(dot(bb,bb)); ab=dot(aa,bb); cr=cross(aa,bb)
            f=k*(al+be)/(al*be*(al*be+ab))
            B=[u+f*v for u,v in zip(B,cr)]
        D=-sp*B[0]+cp*B[1]; ER=D*LR-R*(cp*B[0]+sp*B[1]);EZ=D*LZ-R*B[2]
        results.append(dict(theta=str(th),phi=str(ph),ER=mp.nstr(ER,22),EZ=mp.nstr(EZ,22)))
    return dict(dps=mp.mp.dps,points=results,refit_in_high_precision=False)


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('mode',choices=['fit','trace','diagnostics','precision'])
    parser.add_argument('--plan',nargs='+',default=['8x16','12x24'])
    parser.add_argument('--torus',default=str(ROOT/'.drafts/coil/torus-12x24.npz'))
    parser.add_argument('--start')
    parser.add_argument('--out',required=True)
    args=parser.parse_args(); t=time.process_time(); w=time.monotonic()
    result=globals()[args.mode](args)
    payload=dict(mode=args.mode,upstream=PIN,result=result,cpu_seconds=time.process_time()-t,
                 wall_seconds=time.monotonic()-w,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                 numpy=np.__version__,mpmath=mp.__version__,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    Path(args.out).write_text(json.dumps(payload,indent=2)+'\n')
    print(json.dumps({k:v for k,v in payload.items() if k!='result'}),flush=True)
