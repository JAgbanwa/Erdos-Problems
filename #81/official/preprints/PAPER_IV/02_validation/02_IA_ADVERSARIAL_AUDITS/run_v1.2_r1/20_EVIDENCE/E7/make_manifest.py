import hashlib, os, subprocess, sys
BASE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(BASE, 'sources')
ACC = os.path.join(BASE, '..', 'tools', 'acclog.py')
C = 'cbde8a0a0563372b23b1b39a44180d2c0fb02f44'
RAW = 'https://raw.githubusercontent.com/N0zoM1z0/erdos-81/' + C + '/'
API = 'https://api.github.com/repos/N0zoM1z0/erdos-81'
AQ = 'http://export.arxiv.org/api/query?'
rows = [
 ('okechukwu_abs.html', 'https://arxiv.org/abs/2609.20871', '2026-09-30T12:28:52Z', '[15] abs page, submission history (only v1)'),
 ('okechukwu_abs_v1.html', 'https://arxiv.org/abs/2609.20871v1', '2026-09-30T12:28:53Z', '[15] abs page v1'),
 ('okechukwu_v1.pdf', 'https://arxiv.org/pdf/2609.20871v1', '2026-09-30T12:28:55Z', '[15] PDF v1 (cited version)'),
 ('okechukwu_v1.txt', 'derived: pymupdf text of okechukwu_v1.pdf', '2026-09-30T12:29Z', 'derived text'),
 ('okechukwu_v1_p2_render.png', 'derived: pymupdf render of okechukwu_v1.pdf p.2', '2026-09-30T12:35Z', 'visual check of (1.3) complement bars'),
 ('verclos_abs.html', 'https://arxiv.org/abs/1902.06135', '2026-09-30T12:28:56Z', '[22] abs page (only v1)'),
 ('verclos_v1.pdf', 'https://arxiv.org/pdf/1902.06135v1', '2026-09-30T12:28:57Z', '[22] PDF v1 (cited version)'),
 ('verclos_v1.txt', 'derived: pymupdf text of verclos_v1.pdf', '2026-09-30T12:29Z', 'derived text'),
 ('gh5_commits.json', API + '/commits?per_page=30', '2026-09-30T12:31:33Z', '[5] commit list (HEAD=cbde8a0a)'),
 ('gh5_repo.json', API, '2026-09-30T12:31:33Z', '[5] repo metadata (pushed_at 2026-09-08T12:53:39Z)'),
 ('gh5_commit_cited.json', API + '/commits/' + C, '2026-09-30T12:31:33Z', '[5] cited commit'),
 ('gh5_branches.json', API + '/branches', '2026-09-30T12:31:45Z', '[5] branches'),
 ('gh5_tags.json', API + '/tags', '2026-09-30T12:31:45Z', '[5] tags'),
 ('gh5_releases.json', API + '/releases', '2026-09-30T12:31:45Z', '[5] releases (v0.1.0-proof-claim)'),
 ('gh5_cbde8a0a_manuscript_main.pdf', RAW + 'manuscript/main.pdf', '2026-09-30T12:31:49Z', '[5] manuscript at cited commit'),
 ('gh5_cbde8a0a_manuscript_main.txt', 'derived: pymupdf text of gh5_cbde8a0a_manuscript_main.pdf', '2026-09-30T12:32Z', 'derived text'),
 ('gh5_cbde8a0a_README.md', RAW + 'README.md', '2026-09-30T12:31:51Z', '[5] README at cited commit'),
 ('gh5_cbde8a0a_lean_FORMALIZATION_STATUS.md', RAW + 'lean/FORMALIZATION_STATUS.md', '2026-09-30T12:31:52Z', '[5] formalization status at cited commit'),
 ('gh5_main_main.pdf', 'https://raw.githubusercontent.com/N0zoM1z0/erdos-81/main/manuscript/main.pdf', '2026-09-30T12:31:53Z', '[5] manuscript at main (identical hash)'),
 ('ep81.html', 'https://www.erdosproblems.com/81', '2026-09-30T12:32:47Z', '[8] problem page (status OPEN)'),
 ('ep81.txt', 'derived: text of ep81.html', '2026-09-30T12:33Z', 'derived text'),
 ('ep81_proofclaims.html', 'https://www.erdosproblems.com/forum/thread/81/proof-claims', '2026-09-30T12:32:48Z', '[21] proof claims (anchors 201,235,285,337)'),
 ('ep81_proofclaims.txt', 'derived: text of ep81_proofclaims.html', '2026-09-30T12:33Z', 'derived text'),
 ('ep81_thread.html', 'https://www.erdosproblems.com/forum/thread/81', '2026-09-30T12:32:50Z', 'forum comments #81'),
 ('ep81_thread.txt', 'derived: text of ep81_thread.html', '2026-09-30T12:35Z', 'derived text'),
 ('crossref_alon_shapira.json', 'https://api.crossref.org/works/10.1137/06064888X', '2026-09-30T12:33:27Z', '[23] bibliographic check'),
 ('crossref_verclos_search.json', 'https://api.crossref.org/works?query.bibliographic=Chordal+graphs+are+easily+testable&rows=5', '2026-09-30T12:33:40Z', '[22] journal-version search (no hit)'),
 ('dblp_verclos.json', 'https://dblp.org/search/publ/api?q=Chordal%20graphs%20are%20easily%20testable&format=json', '2026-09-30T12:33:40Z', '[22] dblp search (FAILED: non-JSON response)'),
 ('arxiv_q1.xml', AQ + 'search_query=all:"clique partition" AND all:chordal', '2026-09-30T12:34:07Z', 'prior-art query q1'),
 ('arxiv_q2.xml', AQ + 'search_query=all:"simplicial defect"', '2026-09-30T12:34:11Z', 'prior-art query q2'),
 ('arxiv_q3.xml', AQ + 'search_query=all:"clique partition" AND all:stability', '2026-09-30T12:34:16Z', 'prior-art query q3'),
 ('arxiv_q4.xml', AQ + 'search_query=all:Erdos AND all:Ordman AND all:Zalcstein', '2026-09-30T12:34:21Z', 'prior-art query q4'),
 ('arxiv_q5.xml', AQ + 'search_query=all:"clique partitions" AND all:"split graphs"', '2026-09-30T12:34:25Z', 'prior-art query q5'),
 ('arxiv_q6.xml', AQ + 'search_query=ti:"clique partition"', '2026-09-30T12:34:30Z', 'prior-art query q6'),
 ('arxiv_q7.xml', AQ + 'search_query=all:chordal AND abs:"clique partition"', '2026-09-30T12:34:47Z', 'prior-art query q7'),
 ('arxiv_ning.xml', AQ + 'id_list=2608.11536,2609.20305', '2026-09-30T12:34:44Z', 'Bo Ning abstracts (not chordal; not relevant)'),
]
out = ['# sha256  file  url  retrieval_utc  note']
for f, u, t, note in rows:
    p = os.path.join(SRC, f)
    h = hashlib.sha256(open(p, 'rb').read()).hexdigest()
    out.append('\t'.join([h, 'sources/' + f, u, t, note]))
    if '--log' in sys.argv and not u.startswith('derived'):
        subprocess.run([sys.executable, ACC, u, 'sha256:' + h, 'E7 literature: ' + note, 'E7', 'public literature'], check=True)
open(os.path.join(BASE, 'SOURCES_SHA256.txt'), 'w', encoding='utf-8').write('\n'.join(out) + '\n')
print(len(rows), 'rows')
