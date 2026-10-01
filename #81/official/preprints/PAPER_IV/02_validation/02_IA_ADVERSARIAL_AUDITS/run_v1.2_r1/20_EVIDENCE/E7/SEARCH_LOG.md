# E7 search log (run_v1.2_r1)

Date of all queries: 2026-09-30 (UTC 12:28–12:37). Auditor: E7 sub-auditor. No manuscript text was sent to any external service; queries are short topical keywords.

| # | Engine / endpoint | Query | Top relevant hits | Saved as |
|---|---|---|---|---|
| 1 | arXiv abs (direct) | 2609.20871 | Submission history: only [v1] Tue 15 Sep 2026 16:25:32 UTC (21 KB); 24 pages; no journal ref | sources/okechukwu_abs.html |
| 2 | arXiv abs (direct) | 1902.06135 | Submission history: only [v1] Sat 16 Feb 2019 18:50:24 UTC; no journal ref, no related DOI | sources/verclos_abs.html |
| 3 | GitHub REST API | repos/N0zoM1z0/erdos-81/commits, /branches, /tags, /releases | main HEAD = cbde8a0a (2026-09-08T10:47:29Z); repo pushed_at 2026-09-08T12:53:39Z; tag v0.1.0-proof-claim -> cbde8a0a; release asset main.pdf sha256 53e15161... = file at cited commit = file at main | sources/gh5_*.json |
| 4 | erdosproblems.com | /81, /forum/thread/81, /forum/thread/81/proof-claims | #81 status OPEN (page last edited 28 Dec 2025); 4 proof claims: 201 Cipollini (partial, 2026-08-10), 235 Traverso (partial, split, 2026-08-29), 285 Morluto, Yang Luo, Yinzhen Huang, Grace Lee (full, 2026-09-08, links N0zoM1z0/erdos-81), 337 Traverso (full, 2026-09-22); comments by jpt (23 Aug 2026), JamalAgbanwa (20 Jun 2026, conditional wCDH note, Zenodo 20778270), Woett (19 Jun 2026, explicit EOZ constant c >= 1/133) | sources/ep81*.html/.txt |
| 5 | Crossref API | works/10.1137/06064888X | Alon, Shapira, "A Characterization of the (Natural) Graph Properties Testable with One-Sided Error", SIAM J. Comput. 37(6), 1703–1727, 2008-01; doi.org -> epubs.siam.org (302) | sources/crossref_alon_shapira.json |
| 6 | Crossref API | query.bibliographic="Chordal graphs are easily testable" | No matching journal record in top 5 (McKee, Uehara et al., unrelated) | sources/crossref_verclos_search.json |
| 7 | dblp API | "Chordal graphs are easily testable" | FAILED (non-JSON response); not retried | sources/dblp_verclos.json |
| 8 | arXiv API | all:"clique partition" AND all:chordal | only 2609.20871v1 | sources/arxiv_q1.xml |
| 9 | arXiv API | all:"simplicial defect" | only 2609.20871v1 | sources/arxiv_q2.xml |
| 10 | arXiv API | all:"clique partition" AND all:stability | 2609.20871v1; 1408.2116 (self-stabilizing algorithms, irrelevant) | sources/arxiv_q3.xml |
| 11 | arXiv API | all:Erdos AND all:Ordman AND all:Zalcstein | no hits | sources/arxiv_q4.xml |
| 12 | arXiv API | all:"clique partitions" AND all:"split graphs" | 2306.13306 (claw deletion, irrelevant) | sources/arxiv_q5.xml |
| 13 | arXiv API | ti:"clique partition" (25 newest) | 2609.20871v1 (Okechukwu); 2608.11536 and 2609.20305 (Bo Ning, cp − cc difference, Erdős–Faudree–Ordman; not chordal); rest algorithmic/unrelated | sources/arxiv_q6.xml, arxiv_ning.xml |
| 14 | arXiv API | all:chordal AND abs:"clique partition" | only 2609.20871v1 | sources/arxiv_q7.xml |
| 15 | WebSearch (standard) | "Chordal graphs are easily testable" de Joannis de Verclos journal | arXiv 1902.06135 / ar5iv only; no journal version surfaced | not saved |
| 16 | WebSearch (standard) | clique partition rooted simplicial defect Okechukwu 2026 | arXiv 2609.20871; Bo Ning 2609.20305; nothing else relevant | not saved |
| 17 | WebSearch (standard) | Erdős problem 81 chordal graph clique partition n^2/6 proof 2026 | arXiv 2609.20871; erdosproblems.com pages; JamalAgbanwa forum note; CUP/zbMATH record of EOZ 1993 | not saved |

Not searched / not accessible: MathSciNet, zbMATH Open (beyond the incidental EOZ hit), Google Scholar, Semantic Scholar, the Overleaf manuscript of [21] (link recorded, not opened), Zenodo record 20778270 (not opened). No completeness claim is made.
