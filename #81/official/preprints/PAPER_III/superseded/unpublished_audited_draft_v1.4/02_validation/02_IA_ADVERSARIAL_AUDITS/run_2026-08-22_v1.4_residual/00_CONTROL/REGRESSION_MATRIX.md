# Regression matrix -- v1.3 findings against v1.4

Every finding of the v1.3 baseline report, with the disposition established in this run.

| ID | v1.3 severity | Disposition | Evidence in this run |
|---|---|---|---|
| `EXT-V13-001` | MAJOR | **CLOSED** | `lake build PaperIII` produced `Theorem_1_1_Final.olean`; 8,455 jobs matching the author's declared count and 252 more than v1.3; aggregate closure 429 modules against 177, exceeding both canonical roots; 429 closure modules = 429 objects built |
| `EXT-V13-002` | MAJOR | **CLOSED** | Spanish Proposition 7.4 now carries `h_i >= max{rho, q_J - r_b}` and the full inequality; `A_{2J}` 4/4 in MD and TeX; zero `A_{2,J}` |
| `EXT-V13-003` | MAJOR | **CLOSED** | the metadata now declares `audit_lifecycle: AUDIT_RESULTS_ARE_EXTERNAL_TO_THIS_IMMUTABLE_FORMAL_SNAPSHOT`, fixing the category error rather than the field. Residual recorded as `EXT-V14-N01` (NOTE) |
| `EXT-V13-004` | MINOR | **CLOSED** | `"uninterrupted": false` and `PASS_CLEAN_ORIGIN_RESUMED` declared; Section 13 discloses the restart in prose. This audit's 70-minute uninterrupted build supplies the missing evidence |
| `EXT-V13-005` | MINOR | **WITHDRAWN**, unchanged | the Cavers survey was retrieved in full in the v1.3 addendum and has no chordal or split-graph clique-partition content |
| `EXT-V13-006` | MINOR | **CLOSED** | the scaffold docstring is replaced by a release-gate explanation |
| `EXT-V13-007` | MINOR | **CLOSED** | the mandated sequence now works as written: public root builds, then all eight queries exit 0 |
| `EXT-V13-008` | MINOR | **CLOSED**, unchanged | the `3/16` baseline confirmed from the Erdős Problems record for #81 |

**5 closed in this run, 2 remaining closed from the addendum, 1 withdrawn, 0 open.**

## New in v1.4

| ID | Severity | Substance |
|---|---|---|
| `EXT-V14-M01` | MINOR | Section 2.4 EN/ES: the Spanish rephrasing drops the Proposition 10.5 mention; both languages carry the fact in Section 11.3 |
| `EXT-V14-M02` | MINOR | Appendix D's self-containedness was not audited; the statement is classical and its hypothesis matches Lemma 7.1's need |
| `EXT-V14-N01` | NOTE | `BUILD_INPUT_METADATA.json` reads `internal_audit: PENDING_FOR_VERSION_1.4` while a passing v1.4 internal audit exists; defensible as a freeze-time statement under the declared lifecycle policy |

## The four statuses, kept separate

| Status | Result |
|---|---|
| semantic correspondence | **PROVED** for AX1 (an `iff`), AX2, the decomposition predicate and the four canonical bridges |
| successful compilation | **YES**: 8,455 jobs then 8,444, exit 0, uninterrupted, from 0 project objects |
| axiom footprint | **CLEAN**: 42 surfaces, 0 `sorryAx`, 0 project axioms, archived axioms unreachable |
| independent mathematical rederivation | **DONE**: Sections 4-9, 22/23 and 14/15 items PASS, zero failures; the one open residual is Appendix D |
