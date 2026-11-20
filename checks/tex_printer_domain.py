"""Finite-domain audit of §10.4's printed loop; run with Python 3."""
from collections import Counter

W = 131072


def audit(n):
    # Prefix z with k digits denotes z / scale. Its residual interval
    # has endpoints (p/W, q/W); keep the signed lower endpoint here.
    lo, hi = 2*n - 1, 2*n + 1
    p, q, z, scale, k = lo, hi, 0, 1, 0
    while p > 0:
        assert k < 5, (n, k)
        d, rem = divmod(10*q, W)
        assert rem != 0 and 0 <= d <= 9, (n, k, q)
        # No integer prefix at this width lies in [lo/W, hi/W).
        assert -(-lo*scale // W) > (hi*scale - 1) // W
        p, q = 10*p - W*d, rem
        z, scale, k = 10*z + d, 10*scale, k+1
        assert (p, q) == (lo*scale-W*z, hi*scale-W*z)
    assert lo*scale <= W*z < hi*scale
    assert z == (hi*scale - 1) // W
    return k, z


def intern(z, k):
    state = 0
    for _ in range(k):  # including any leading zeroes
        z, d = divmod(z, 10)
        state = (W*d + state) // 10
    return (state + 1) // 2


def shortest_groups():
    groups = {}
    for k in range(6):
        for z in range(10**k):
            n = intern(z, k)
            width, candidates = groups.setdefault(n, (k, []))
            if k == width:
                candidates.append(z)
    return groups


if __name__ == '__main__':
    counts = Counter()
    groups = shortest_groups()
    misses = 0
    for n in range(W // 2):
        k, z = audit(n)
        width, candidates = groups[n]
        assert k == width and z == max(candidates)
        def error(p):
            return abs((W // 2)*p - n*10**k)
        # Round the exact target at this width, then clamp to the grid
        # of available fractional strings (including the empty string).
        nearest = min(10**k - 1, (2*n*10**k + W//2) // W)
        optimum = min(map(error, candidates))
        assert nearest in candidates and error(nearest) == optimum
        misses += error(z) > optimum
        counts[k] += 1
    print('Greatest shortest candidate strictly farther than closest:', misses)
    print('Shortest printed width: number of targets')
    for width in sorted(counts):
        print(width, counts[width])
