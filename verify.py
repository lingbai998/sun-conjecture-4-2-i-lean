#!/usr/bin/env python3
"""
Numerical verification for Zhi-Wei Sun's Conjecture 4.2(i) (arXiv:2108.07723v7,
Eqs. 4.3 & 4.4; OEIS A085807) and its extensions.

Uses Ryser's Gray-code algorithm for exact integer permanents.
"""

from itertools import permutations
import random


def permanent_ryser(matrix):
    """Exact permanent of an n x n integer matrix via Ryser's algorithm with Gray code."""
    n = len(matrix)
    row_sums = [0] * n
    total = 0
    old_gray = 0
    sign = -1 if (n % 2 == 1) else 1

    for k in range(1, 1 << n):
        gray = k ^ (k >> 1)
        diff = gray ^ old_gray
        col = diff.bit_length() - 1
        if gray & diff:
            for i in range(n):
                row_sums[i] += matrix[i][col]
        else:
            for i in range(n):
                row_sums[i] -= matrix[i][col]
        old_gray = gray

        prod = 1
        for s in row_sums:
            prod *= s
        sign = -sign
        total += sign * prod

    return total


def det_mod(matrix, p):
    """Exact determinant of an n x n matrix modulo a prime p via Gaussian elimination."""
    n = len(matrix)
    A = [[x % p for x in row] for row in matrix]
    det = 1
    for col in range(n):
        pivot = None
        for r in range(col, n):
            if A[r][col] != 0:
                pivot = r
                break
        if pivot is None:
            return 0
        if pivot != col:
            A[col], A[pivot] = A[pivot], A[col]
            det = (-det) % p
        pv = A[col][col]
        det = (det * pv) % p
        inv_pv = pow(pv, p - 2, p)
        for r in range(col + 1, n):
            factor = (A[r][col] * inv_pv) % p
            if factor:
                for c in range(col, n):
                    A[r][c] = (A[r][c] - factor * A[col][c]) % p
    return det


def verify_eq_4_3_and_4_4():
    primes = [3, 5, 7, 11, 13, 17]
    print("=== 1. Sun Conjecture 4.2(i): Eqs. (4.3) and (4.4) ===")
    for p in primes:
        M0 = [[abs(j - k) for k in range(1, p + 1)] for j in range(1, p + 1)]
        M1 = [[abs(j - k + 1) for k in range(1, p + 1)] for j in range(1, p + 1)]
        per0 = permanent_ryser(M0)
        per1 = permanent_ryser(M1)
        det0 = det_mod(M0, p)
        det1 = det_mod(M1, p)
        assert (2 * per0) % p == p - 1, f"Eq. 4.3 failed at p={p}"
        assert (2 * per1) % p == 1, f"Eq. 4.4 failed at p={p}"
        assert per0 % p == det0, f"per != det for M0 at p={p}"
        assert per1 % p == det1, f"per != det for M1 at p={p}"
        print(
            f"p={p:2d}: 2*per(|j-k|) ≡ {(2*per0)%p - p:2d} (mod {p}), "
            f"2*per(|j-k+1|) ≡ {(2*per1)%p:2d} (mod {p}), per≡det OK"
        )


def verify_shift_boundary():
    print("\n=== 2. Exact Shift Boundary (s = 2 breaks at p = 5) ===")
    p = 5
    M2 = [[abs(j - k + 2) for k in range(1, p + 1)] for j in range(1, p + 1)]
    per2 = permanent_ryser(M2) % p
    det2 = det_mod(M2, p)
    assert det2 == 0 and per2 == 2
    print(f"p=5, s=2: det(|j-k+2|) ≡ {det2} (mod 5), per(|j-k+2|) ≡ {per2} (mod 5) (boundary confirmed)")


def verify_general_powers():
    print("\n=== 3. General Powers: per[|j-k|^m] ≡ sum_{c=1}^{p-1} (-1)^{mc} c^m (mod p) ===")
    for p in [3, 5, 7, 11]:
        for m in range(1, 6):
            M = [[abs(j - k) ** m for k in range(1, p + 1)] for j in range(1, p + 1)]
            lhs = permanent_ryser(M) % p
            rhs = sum(((-1) ** (m * c)) * pow(c, m, p) for c in range(1, p)) % p
            assert lhs == rhs, f"Power formula failed at p={p}, m={m}"
        print(f"p={p:2d}: m=1..5 all match sum (-1)^(mc) c^m (mod {p})")


def verify_prime_powers():
    print("\n=== 4. Prime Power Extension: a(p^k) ≡ -1/2 (mod p) ===")
    for n, p in [(9, 3), (4, 2), (8, 2)]:
        M = [[abs(j - k) for k in range(1, n + 1)] for j in range(1, n + 1)]
        val = permanent_ryser(M)
        if p == 2:
            assert val % 2 == 0
            print(f"n={n:2d} (2^k): a({n}) = {val} ≡ 0 (mod 2)")
        else:
            assert (2 * val) % p == p - 1
            print(f"n={n:2d} ({p}^k): a({n}) = {val}, 2*a({n}) ≡ -1 (mod {p})")


def verify_master_theorem_random():
    print("\n=== 5. Master Theorem on Random Signed-Shift-Invariant Matrices ===")
    rng = random.Random(2026)
    for p in [3, 5, 7]:
        # A signed-shift-invariant matrix is determined by its first row a_0, ..., a_{p-1}:
        # M_{i, j} = eps_prod * a_{(j - i) mod p}, specifically M_{i,j} = (-1)^[j < i] * a_{(j - i) mod p}
        for _ in range(5):
            row0 = [rng.randrange(p) for _ in range(p)]
            M = [[(row0[(j - i) % p] * (-1 if j < i else 1)) % p for j in range(p)] for i in range(p)]
            per_val = permanent_ryser(M) % p
            det_val = det_mod(M, p)
            assert per_val == det_val, f"Master theorem failed at p={p}"
        print(f"p={p:2d}: 5 random signed-shift-invariant matrices satisfy per(M) ≡ det(M) (mod {p})")


if __name__ == "__main__":
    verify_eq_4_3_and_4_4()
    verify_shift_boundary()
    verify_general_powers()
    verify_prime_powers()
    verify_master_theorem_random()
    print("\nALL CHECKS PASSED.")
