#!/usr/bin/env python3
"""Finite audit of Gate PIII-EFF-01 constants."""

from math import floor, ceil, sqrt


def chi_complete(t: int) -> int:
    if t <= 1:
        return 0
    return t - 1 if t % 2 == 0 else t


def check_short() -> int:
    instances = 0
    for p in range(36, 5001):
        for s in range(0, floor(6 * sqrt(p)) + 1):
            q = 2 * p - s
            assert q >= chi_complete(p)
            excess = p / 2 + (s * s - 6 * s + 3) / 12
            assert excess <= 2 * (3 * p - s) + 1e-12
            instances += 1
    return instances


def check_mesoscopic() -> int:
    instances = 0
    for p in range(2304, 8001):
        lower = ceil(6 * sqrt(p))
        upper = floor(p / 8)

        for s in range(lower, upper + 1):
            q = 2 * p - s
            m_max = (s - 3) // 3

            r_p = chi_complete(p)
            h = min(r_p, q - r_p)
            delta = h / r_p

            assert delta >= 7 / 8 - 1e-12
            assert p / 2 - 5 * s * s / 288 - 2 * s / 3 <= 1e-12
            assert p / 2 - s * s / 64 <= 1e-12

            for rho in {0, m_max // 2, m_max}:
                b = p - rho
                r_b = chi_complete(b)
                u = q - r_b

                assert q >= r_b
                assert b >= chi_complete(rho)

                for t in {0, m_max}:
                    assert b - t >= rho
                    assert b - t >= u

                if rho > 0:
                    theta = (rho - 1) / b
                    kappa = 1 - 2 * (1 - theta) * u / q
                    assert kappa <= 5 * s / (4 * p) + 1e-12

                coefficient_a = max(s - 2 * rho - 1, 0) / q
                assert coefficient_a <= 5 * s / (4 * p) + 1e-12

            instances += 1

    return instances


def main() -> None:
    short = check_short()
    mesoscopic = check_mesoscopic()

    print(f"PASS short corridor: {short} integer (p,s) instances")
    print(
        "PASS mesoscopic constants: "
        f"{mesoscopic} integer (p,s) instances"
    )
    print("PASS delta >= 7/8")
    print("PASS high-dispersion excess <= 0")
    print("PASS shifted-center hypotheses on audited boundary cases")
    print("PASS kappa_R and A_R coefficients <= 5s/(4p)")
    print("PASS low-dispersion excess <= 0")


if __name__ == "__main__":
    main()
