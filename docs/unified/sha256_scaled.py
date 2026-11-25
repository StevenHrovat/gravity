#!/usr/bin/env python3
"""A digest of all zeros and a one: possible in small, provably costly in full (draft 5, Appendix T.6, R.6a).

  python docs/unified/sha256_scaled.py > docs/unified/sha256_scaled.log

1. The sha256 of the 32-byte value 0...01 (all zeros, a one at the end): computing a hash of any input is immediate.
2. The opposite direction, a digest of a fixed shape, is a preimage search. Scaled down: for k = 1 to 5, the first input
   "vxunderground-n" (n = 0, 1, 2, ...) whose digest starts with k zero hex digits and ends in the hex digit 1. Each fixed hex
   digit multiplies the expected work by 16; a fully fixed digest (63 zeros and a 1) needs about 16^64 = 2^256 tries.
The search is deterministic, so the RESULT lines reproduce exactly. Python standard library only.
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
