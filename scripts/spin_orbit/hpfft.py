"""Fixed-point complex 2-D FFT on numpy object arrays of Python ints (scale 2^P).  Untrusted tooling."""
import numpy as np
import mpmath

P = 520

def _twiddles(n, sign, prec=P):
    mpmath.mp.prec = prec + 80
    wr, wi = [], []
    for j in range(n // 2):
        a = 2 * mpmath.pi * j / n
        wr.append(int(mpmath.nint(mpmath.cos(a) * 2**prec)))
        wi.append(int(mpmath.nint(sign * mpmath.sin(a) * 2**prec)))
    return np.array(wr, dtype=object), np.array(wi, dtype=object)

_cache = {}
def _tw(n, sign):
    if (n, sign) not in _cache:
        _cache[(n, sign)] = _twiddles(n, sign)
    return _cache[(n, sign)]

def _bitrev(n):
    bits = n.bit_length() - 1
    return np.array([int(format(i, f"0{bits}b")[::-1], 2) if bits else 0 for i in range(n)])

def fft_axis0(re, im, sign):
    """Unnormalised DFT along axis 0 (sign=-1 forward, +1 inverse); arrays (n, m) of ints."""
    n = re.shape[0]
    idx = _bitrev(n)
    re = re[idx]; im = im[idx]
    wr_all, wi_all = _tw(n, sign)
    h = 1
    while h < n:
        shp = (n // (2 * h), 2, h, re.shape[1])
        r = re.reshape(shp); i = im.reshape(shp)
        step = n // (2 * h)
        wr = wr_all[::step][:h].reshape(1, h, 1); wi = wi_all[::step][:h].reshape(1, h, 1)
        ur, ui = r[:, 0], i[:, 0]
        br, bi = r[:, 1], i[:, 1]
        tr = (br * wr - bi * wi) >> P
        ti = (br * wi + bi * wr) >> P
        nr = np.empty(shp, dtype=object); ni = np.empty(shp, dtype=object)
        nr[:, 0] = ur + tr; nr[:, 1] = ur - tr
        ni[:, 0] = ui + ti; ni[:, 1] = ui - ti
        re = nr.reshape(n, -1); im = ni.reshape(n, -1)
        h *= 2
    return re, im

def fft2(re, im, sign):
    re, im = fft_axis0(re, im, sign)
    re, im = fft_axis0(re.T.copy(), im.T.copy(), sign)
    return re.T.copy(), im.T.copy()

def zeros(shape):
    z = np.empty(shape, dtype=object); z.fill(0); return z
