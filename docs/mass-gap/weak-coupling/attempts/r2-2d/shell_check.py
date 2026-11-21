"""Check of the shell classification used by the certificate and by the Lean kappa (Attempts/R2/TwoD.lean).

On the 2D torus (Z/N)^2, for the thin square of side l at x = 0 (links with both ends in {0..l}^2, the Lean `thinCube l 0`), enumerate
the shell exactly as Lean defines it (`InShell`: a link outside the block lying in a plaquette that has a link in the block), and
check that every shell link has one of the offsets listed in `kappa` (relative to x, along / across its own direction):
  P   (i, -1), (i, l+1),            i = 0..l-1      class P_i
  D   (-1, s), (l, s),              s = 1..l-1      class D
  C   (-1, 0), (-1, l), (l, 0), (l, l)              class P_0 (corner links)
and conversely that each listed offset is a shell link; also that the P links touch exactly one plaquette with a block link
(outer plaquette of one face link), D links two, corner links one (the P_0 equivalence).
Usage: py shell_check.py   (l = 10, 11, 12 on tori N >= l + 3)
"""


def run(l, N):
    def link_ok(s, mu):  # block membership: both ends in {0..l}^2 (mod N, values 0..N-1)
        t = list(s)
        t[mu] = (t[mu] + 1) % N
        return all(v <= l for v in s) and all(v <= l for v in t)

    def plaq_links(s):
        x, y = s
        return [((x, y), 0), (((x + 1) % N, y), 1), ((x, (y + 1) % N), 0), ((x, y), 1)]

    block = {((x, y), mu) for x in range(N) for y in range(N) for mu in (0, 1) if link_ok((x, y), mu)}
    touch = {}
    for x in range(N):
        for y in range(N):
            ls = plaq_links((x, y))
            nb = sum(1 for e in ls if e in block)
            if nb:
                for e in ls:
                    if e not in block:
                        touch.setdefault(e, []).append(nb)
    shell = set(touch)
    listed = {}
    for mu in (0, 1):
        def site(a, b):  # a along mu, b across
            v = [0, 0]
            v[mu], v[1 - mu] = a % N, b % N
            return tuple(v)
        for i in range(l):
            listed[(site(i, -1), mu)] = "P%d" % i
            listed[(site(i, l + 1), mu)] = "P%d" % i
        for s in range(1, l):
            listed[(site(-1, s), mu)] = "D"
            listed[(site(l, s), mu)] = "D"
        for a, b in ((-1, 0), (-1, l), (l, 0), (l, l)):
            listed[(site(a, b), mu)] = "C"
    ok = shell == set(listed)
    ntouch = {"P": 1, "D": 2, "C": 1}
    ok2 = all(len(touch[e]) == ntouch[c[0]] for e, c in listed.items())
    print("l=%d N=%d: shell links %d, listed %d, equal: %s; plaquette counts as expected: %s" % (
        l, N, len(shell), len(listed), ok, ok2))
    return ok and ok2


if __name__ == "__main__":
    assert all(run(11, N) for N in (14, 15, 20))
    assert all(run(12, N) for N in (15, 20))
    assert all(run(10, N) for N in (13, 20))
