"""r3-monotone: beta -> infinity twist ratio |Hom_tw|/|Hom| for finite groups (PREREG.md). Exact integer counts."""
import json, math, itertools, sys

def qmul(a, b):
    a0, a1, a2, a3 = a; b0, b1, b2, b3 = b
    return (a0*b0 - a1*b1 - a2*b2 - a3*b3, a0*b1 + a1*b0 + a2*b3 - a3*b2,
            a0*b2 - a1*b3 + a2*b0 + a3*b1, a0*b3 + a1*b2 - a2*b1 + a3*b0)

def key(q):
    return tuple(round(x, 9) + 0.0 for x in q)

def closure(gens):
    one = (1.0, 0.0, 0.0, 0.0)
    elems = {key(one): one}
    frontier = [one]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = qmul(x, g); k = key(y)
                if k not in elems:
                    elems[k] = y; new.append(y)
        frontier = new
    return list(elems.values())

def quat_group(gens):
    el = closure(gens)
    idx = {key(q): i for i, q in enumerate(el)}
    n = len(el)
    mul = [[idx[key(qmul(el[i], el[j]))] for j in range(n)] for i in range(n)]
    one = idx[key((1.0, 0, 0, 0))]
    c = idx[key((-1.0, 0, 0, 0))]
    return n, mul, one, c

def cyclic(n):
    mul = [[(i + j) % n for j in range(n)] for i in range(n)]
    return n, mul, 0, n // 2   # c = element of order 2 ("-1")

def analyse(name, grp):
    n, mul, one, c = grp
    inv = [next(j for j in range(n) if mul[i][j] == one) for i in range(n)]
    # closure check
    assert all(0 <= mul[i][j] < n for i in range(n) for j in range(n))
    comm = [[mul[i][j] == mul[j][i] for j in range(n)] for i in range(n)]
    def commutator(a, b):
        return mul[mul[mul[a][b]][inv[a]]][inv[b]]
    # conjugacy classes
    seen, k = set(), 0
    for a in range(n):
        if a in seen: continue
        k += 1
        for g in range(n):
            seen.add(mul[mul[g][a]][inv[g]])
    # |Hom(Z^m, H)| recursively over centralisers
    def hom(m, H):
        if m == 0: return 1
        return sum(hom(m - 1, [h for h in H if comm[g][h]]) for g in H)
    G = list(range(n))
    hom2, hom4 = hom(2, G), hom(4, G)
    tw = 0
    tw_pairs = 0
    for a in G:
        for b in G:
            if commutator(a, b) == c:
                tw_pairs += 1
                C = [h for h in G if comm[a][h] and comm[b][h]]
                tw += hom(2, C)
    F = math.log(hom4 / tw) if tw > 0 else float('inf')
    return dict(group=name, order=n, classes=k, hom2=hom2, hom2_check=(hom2 == n * k), hom4=hom4,
                twisted_pairs=tw_pairs, hom_tw=tw, F_inf=F)

s = 0.5
h = 0.5 * (1 + math.sqrt(5)) / 2  # cos(pi/5)
g2 = 0.5 / ((1 + math.sqrt(5)) / 2)  # 1/(2 phi) = sin(pi/10)
r2 = math.sqrt(0.5)
groups = {
    'Z2': cyclic(2), 'Z4': cyclic(4),
    'Q8': quat_group([(0, 1, 0, 0), (0, 0, 1, 0)]),
    '2T': quat_group([(0, 1, 0, 0), (0, 0, 1, 0), (s, s, s, s)]),
    '2O': quat_group([(0, 1, 0, 0), (0, 0, 1, 0), (s, s, s, s), (r2, r2, 0, 0)]),
    '2I': quat_group([(0, 1, 0, 0), (0, 0, 1, 0), (s, s, s, s), (h, s, g2, 0)]),
}
out = [analyse(k, v) for k, v in groups.items()]
for r in out:
    print(r)
checks = {
    'orders': [r['order'] for r in out] == [2, 4, 8, 24, 48, 120],
    'abelian_no_twist': out[0]['hom_tw'] == 0 and out[1]['hom_tw'] == 0,
    'hom2_eq_G_k': all(r['hom2_check'] for r in out),
    'Q8_hom2_40': out[2]['hom2'] == 40, '2I_hom2_1080': out[5]['hom2'] == 1080,
    'Q8_hom_tw_96': out[2]['hom_tw'] == 96,
}
print(checks)
json.dump({'results': out, 'checks': checks}, open(sys.argv[1], 'w'), indent=1)
