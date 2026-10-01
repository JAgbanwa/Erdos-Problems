"""E6: paragraph-aligned qualifier survival check EN->ES (MD)."""
import re, json, difflib
D = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/01_manuscript/v1.2_full_rebuild_candidate/"
OUT = "C:/Users/jtraverso/e81p4-publish/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.2_r1/20_EVIDENCE/E6/results/"

def paras(l):
    t = open(D + f"PAPER_IV_preprint_v1.2_{l}.md", encoding="utf-8").read()
    out, cur, start = [], [], 1
    for i, line in enumerate(t.split("\n"), 1):
        if line.strip() == "":
            if cur:
                out.append((start, "\n".join(cur))); cur = []
        else:
            if not cur: start = i
            cur.append(line)
    if cur: out.append((start, "\n".join(cur)))
    return out

def strip_math(s):
    s = re.sub(r"\\\[.+?\\\]", " M ", s, flags=re.S)
    return re.sub(r"\\\(.+?\\\)", " M ", s, flags=re.S)

Q = [  # (name, EN regex, ES regex)
    ("at_most", r"\bat most\b|\bno more than\b|\bup to\b", r"\ba lo sumo\b|\bcomo máximo\b|\bno más de\b|\bhasta\b"),
    ("at_least", r"\bat least\b", r"\bal menos\b|\bcomo mínimo\b|\bpor lo menos\b"),
    ("eventual", r"\beventual", r"\beventual|órdenes grandes|suficientemente grande"),
    ("suff_large", r"sufficiently large|large enough", r"suficientemente grande"),
    ("fixed", r"\bfixed\b", r"\bfij[oa]s?\b"),
    ("uniform", r"\buniform", r"\buniform"),
    ("explicit", r"\bexplicit", r"\bexplícit"),
    ("impractical", r"impractical", r"no prácticos?|impráctic"),
    ("rational", r"\brational", r"\bracional"),
    ("real", r"\breal\b", r"\breal(es)?\b"),
    ("priority", r"\bpriority\b", r"\bprioridad\b"),
    ("not_claimed", r"not (?:be )?claimed|is not asserted|not asserted|no .* is claimed|is claimed|not claim|does not assert|nor .* asserted|are not asserted", r"no se (?:reclama|afirma)|no afirma|no reclama|no se asevera|ni .* se afirma"),
    ("strict", r"\bstrict", r"\bestrict"),
    ("every", r"\bevery\b|\beach\b|\ball\b", r"\btod[oa]s?\b|\bcada\b"),
    ("exists", r"\bthere (?:is|are|exist)", r"\bexiste|\bhay\b"),
    ("negation", r"\bnot\b|\bno\b|\bneither\b|\bnor\b|\bnever\b|\bnone\b|n't\b|\bwithout\b", r"\bno\b|\bni\b|\bnunca\b|\bninguna?\b|\bsin\b|\btampoco\b"),
    ("four", r"\bfour\b", r"\bcuatro\b"),
    ("three", r"\bthree\b", r"\btres\b"),
    ("only", r"\bonly\b|\balone\b|\bmerely\b", r"\bsólo\b|\bsolo\b|\búnicamente\b|\bpor sí sol[oa]\b|\bmeramente\b|\bexclusivamente\b"),
    ("pending", r"\bpending\b", r"\bpendiente"),
]
A, B = paras("en"), paras("es")
print("paragraphs", len(A), len(B))
# align by math skeleton
def skel(p):
    return re.sub(r"\s+", "", "".join(re.findall(r"\\\((.+?)\\\)|\\\[(.+?)\\\]", p[1], flags=re.S).__str__()))[:400] + str(len(re.findall(r"\d+", p[1])))
sm = difflib.SequenceMatcher(None, [skel(p) for p in A], [skel(p) for p in B], autojunk=False)
pairs = []
for op, i1, i2, j1, j2 in sm.get_opcodes():
    if op == "equal" or (i2 - i1 == j2 - j1):
        pairs += [(A[i1 + k], B[j1 + k]) for k in range(i2 - i1)]
    else:
        print("unaligned", op, [a[0] for a in A[i1:i2]], [b[0] for b in B[j1:j2]])
flags = []
for a, b in pairs:
    ta, tb = strip_math(a[1]), strip_math(b[1])
    diff = {}
    for name, pe, ps in Q:
        ce, cs = len(re.findall(pe, ta, re.I)), len(re.findall(ps, tb, re.I))
        if ce != cs:
            diff[name] = (ce, cs)
    if diff:
        flags.append(dict(en_line=a[0], es_line=b[0], diff=diff))
json.dump(dict(n_pairs=len(pairs), flags=flags), open(OUT + "qualifiers.json", "w", encoding="utf-8"), ensure_ascii=False, indent=1)
print("pairs", len(pairs), "flagged", len(flags))
imp = [f for f in flags if set(f["diff"]) & {"at_most", "at_least", "eventual", "fixed", "uniform", "explicit", "impractical", "rational", "real", "priority", "not_claimed", "strict", "four", "three", "pending", "suff_large"}]
print("flagged on key qualifiers", len(imp))
for f in imp:
    print(f["en_line"], f["es_line"], {k: v for k, v in f["diff"].items() if k not in ("every", "negation", "exists", "only")})
