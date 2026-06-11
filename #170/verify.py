#!/usr/bin/env python3
"""Exact-arithmetic verification for Erdős Problem 170 write-up."""
from fractions import Fraction as F


def f(k: int) -> F:
    return F(k, 2**k)


def main() -> None:
    # Theorem 1: n_s = 2^s - s - 1
    for s in range(3, 12):
        n = 2**s - s - 1
        blk = list(range(n + 1, 2**s - 1))
        assert f(n) == sum(f(k) for k in blk), (s, n)

    # Remark 2: odd E >= 5
    for E in (5, 7, 9, 11, 13):
        b = (2**E - 5) // 3 + 1
        a = b + 1 - E
        assert f(a) + f(b) == sum(f(k) for k in range(a + 1, b)), (E, a, b)

    # Table certificates (t >= 2)
    certs = {
        1: [4, 5, 6],
        2: [4, 5, 6],
        3: [4, 6, 8],
        4: [5, 6],
        5: [6, 7, 11, 13, 14],
        6: [7, 8, 11, 13, 14],
        7: [8, 9, 12, 13, 14, 15, 20, 21, 24],
        9: [10, 11, 13, 14],
        11: [12, 13, 14],
        12: [13, 14, 15, 20, 21, 24],
        15: [16, 17, 18, 21, 22],
    }
    for n, S in certs.items():
        assert len(S) == len(set(S)) >= 2, n
        assert f(n) == sum(f(k) for k in S), n

    # Theorem compute: reachability for n <= 2000
    def reachable(n: int, H: int = 250_000) -> tuple[bool, int]:
        cur = {n}
        j = n
        while j < H:
            nxt: set[int] = set()
            for rho in cur:
                r1 = 2 * rho
                if 0 <= r1 <= j + 3:
                    nxt.add(r1)
                r2 = 2 * rho - (j + 1)
                if 0 <= r2 <= j + 3:
                    nxt.add(r2)
            j += 1
            cur = nxt
            if 0 in cur:
                return True, j
            if not cur:
                return False, j
        return False, H

    for n in range(1, 2001):
        ok, _ = reachable(n)
        assert ok, n

    print("all checks passed")


if __name__ == "__main__":
    main()
