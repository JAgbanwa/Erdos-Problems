# E6 -- citations, prior art, novelty and overclaim

**Verdict: `INCONCLUSIVE`**, on auditor capability rather than on a defect.

## What is verifiable, and passes

Citation integrity is clean: **17 references listed, every bracketed citation resolves to a
listed reference, and every listed reference is cited in the body.** An apparent citation `[0]`
was the auditor's regex reading the interval `[0,2]` as a citation; recorded as a tool artifact.

Every source the request names by name is present and cited: Chen-Erdős-Ordman,
Erdős-Ordman-Zalcstein, Haxell-Rödl, Yuster, Barber-Kühn-Lo-Osthus, Dross, Galvin, Tuza, and
the Erdős #81 record. The `3/16 -> 1/6` improvement is stated explicitly, and the full chordal
problem is kept distinct from the split asymptotic result in both languages.

**The Cavers survey is absent**, zero mentions in either language, though the request names it
among the sources to check. See `EXT-V13-005`.

## What could not be done, stated plainly

**Not one of the 17 references was independently retrieved in this run.** No institutional
bibliographic database was reachable, and `erdosproblems.com` has returned HTTP 403 to this
auditor on every attempt. No specialist search through the audit date was run, so there are no
search strings and no databases to report.

Therefore this audit **cannot** say whether a published result already gives the same
split-graph `1/6` quadratic coefficient, a stronger statement, or an equivalent method. The
request states that novelty cannot pass on the author's bibliography alone, and it does not
pass here.

Evidence: `scripts/v13_E6_E7.py`, `results/prior_art.json`.
