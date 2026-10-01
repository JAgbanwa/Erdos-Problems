"""Integer target and one-chain budget regression, not a Lean proof."""

from __future__ import annotations

import json
from pathlib import Path


HERE = Path(__file__).resolve().parents[1]


def target(n: int) -> int:
    return n * (n + 1) // 6


def main():
    checks = 0
    credits = [0]
    for n in range(1, 10001):
        if target(n) - target(n - 1) != (n + 1) // 3:
            raise AssertionError((n, "deletion credit"))
        if 6 * target(n) > n * (n + 1):
            raise AssertionError((n, "floor bound"))
        credits.append(credits[-1] + (n + 1) // 3)
        for m in (0, n // 3, n // 2, n - 1):
            budget = credits[n] - credits[m]
            if budget != target(n) - target(m):
                raise AssertionError((n, m, "one-chain telescoping"))
            checks += 1
    result = {"domain": "1<=n<=10000, four endpoint choices m per n",
              "telescoping_checks": checks,
              "target_difference_checks": 10000,
              "limit": "Finite arithmetic regression, not proof of existence of a partition or b=0."}
    path = HERE / "results" / "target_arithmetic.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
