#!/usr/bin/env python3
"""A digest of all zeros and a one: possible in small, provably costly in full (draft 5, Appendix T.6, R.6a).

  python docs/unified/sha256_scaled.py > docs/unified/sha256_scaled.log

1. The sha256 of the 32-byte value 0...01 (all zeros, a one at the end): computing a hash of any input is immediate.
2. The opposite direction, a digest of a fixed shape, is a preimage search. Scaled down: for k = 1 to 5, the first input
   "vxunderground-n" (n = 0, 1, 2, ...) whose digest starts with k zero hex digits and ends in the hex digit 1. Each fixed hex
   digit multiplies the expected work by 16; a fully fixed digest (63 zeros and a 1) needs about 16^64 = 2^256 tries.
3. The test vectors of the Secure Hash Standard reproduce (the encoding agrees with the standard).
4. Inputs built by rotating a 1 into place are hashed once each and compared with 000...0001 (all refuted).
5. The avalanche on vxunderground: each of its 104 input bits flipped once, the digest bits that change counted.
6. The digest of vxunderground plus its complement is the line of 256 ones; a cyclic bit rotation keeps its count of ones.
Everything is deterministic, so the RESULT lines reproduce exactly. Python standard library only.
"""
import hashlib

m = bytes(31) + b'\x01'
print('input %s' % m.hex())
print('RESULT sha256(0...01) = %s' % hashlib.sha256(m).hexdigest())
for k in range(1, 6):
    n = 0
    while True:
        s = 'vxunderground-%d' % n
        d = hashlib.sha256(s.encode()).hexdigest()
        if d.startswith('0' * k) and d.endswith('1'):
            break
        n += 1
    print('RESULT k=%d zeros, ends in 1: input %s, tries %d (expected about 16^%d = %d), digest %s' % (k, s, n + 1, k + 1, 16 ** (k + 1), d))
print('full shape 000...0001: 64 fixed hex digits, about 16^64 = 2^256 = %.3e tries' % float(2 ** 256))

# 3. The encoding agrees with the standard: the test vectors published with the Secure Hash Standard (as recalled).
VECTORS = [(b'abc', 'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad'),
           (b'', 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855'),
           (b'abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq',
            '248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1')]
for msg, want in VECTORS:
    got = hashlib.sha256(msg).hexdigest()
    print('RESULT test vector %r: %s' % (msg.decode() if len(msg) < 10 else msg.decode()[:10] + '...', 'agrees' if got == want else 'DIFFERS ' + got))
# 4. Inputs built by rotating a 1 into place, each hashed once (path cost 1) and compared with 000...0001.
target = '0' * 63 + '1'
for name, c in [('one byte 0x01', b'\x01'), ('the character "1"', b'1'), ('32 bytes 0...01', bytes(31) + b'\x01'),
                ('256 characters 0...01', ('0' * 255 + '1').encode())]:
    d = hashlib.sha256(c).hexdigest()
    print('RESULT candidate %s: digest %s, equals 000...0001: %s' % (name, d, d == target))
# 5. Avalanche on vxunderground: flip each of its 104 input bits once and count the digest bits that change.
v = bytearray(b'vxunderground'); d0 = int(hashlib.sha256(v).hexdigest(), 16)
flips = []
for i in range(len(v) * 8):
    w = bytearray(v); w[i // 8] ^= 1 << (7 - i % 8)
    flips.append(bin(d0 ^ int(hashlib.sha256(w).hexdigest(), 16)).count('1'))
print('RESULT avalanche on vxunderground: %d input-bit flips, digest bits changed min %d, max %d, mean %.1f of 256'
      % (len(flips), min(flips), max(flips), sum(flips) / len(flips)))
# 6. Every digest completes to the line of 256 ones by adding its complement: y + ~y = 2^256 - 1; a cyclic rotation of the bits keeps
#    the number of ones, so it never does.
y = d0; k = (2 ** 256 - 1) ^ y
rot_ones = set(bin(((y << r) | (y >> (256 - r))) & (2 ** 256 - 1)).count('1') for r in range(256))
print('RESULT line of ones: sha256(vxunderground) + its complement = 2^256 - 1: %s; ones %d + %d = 256; every cyclic bit rotation keeps %s ones'
      % (y + k == 2 ** 256 - 1, bin(y).count('1'), bin(k).count('1'), sorted(rot_ones)))
