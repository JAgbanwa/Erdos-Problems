# Gate plan and resource limits (recorded at intake, before substantive work)

Order (request §4.1): Intake(E0) → E1/E3-static → E7 → E2 → E5 → E6 → E8-preliminary → PREBUILD_CHECKPOINT → E4 → finish E3/E8 → E0 recheck → report → seal.

| Phase | Planned limit | Notes |
|---|---|---|
| Intake | ≤ 1 h wall clock | E0 + pins only |
| E1/E3 static | ≤ 1 session phase; checkpoint sealed at end | literal statements vs Lean types |
| E7 | web retrieval; ≤ 2 h | record URL/date/hash of every source |
| E2 | proof-critical rederivation of the headline chain; each serious concern ≤ 30 min diagnostic (§4.2) | components known only through Lean/imported papers flagged |
| E5 | each exhaustive search ≤ 20 min CPU; timeouts preserved | exact arithmetic (fractions/sympy) |
| E6 | render all 101 pages; text-level diff EN/ES | PDFs never regenerated |
| E4 | single heavy build, ≤ 8 h wall clock, no concurrent heavy jobs; one retry only for environment faults | isolated project build against shared verified dependency artefacts |

Limits are not silently extended; on cutoff a PARTIAL_REPORT is sealed (§4.2).
The auditor is an AI agent working in one conversation; if the conversation context or operator session ends,
the last sealed checkpoint is the recoverable result.
