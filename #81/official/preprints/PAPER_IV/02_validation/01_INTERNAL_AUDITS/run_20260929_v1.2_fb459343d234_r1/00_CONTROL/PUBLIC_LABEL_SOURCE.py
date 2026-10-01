"""Inventory the literal formal claims and their recorded evidence.

Rows with a formal trace are not thereby certified as faithful translations of
the English and Spanish prose; that is a separate G1 review.
"""

from __future__ import annotations

import csv
import hashlib
import json
import re
from pathlib import Path


RUN = Path(__file__).resolve().parents[1]
PAPER = RUN.parents[2]
TARGET = json.loads((RUN / "00_CONTROL" / "TARGET.json").read_text(encoding="utf-8"))
MAIN = Path(TARGET["freezeSourceRoot"])
LOGS = Path(TARGET["buildEvidenceRoot"])
ANNEX = Path(TARGET["boundedGapAnnexRoot"])
ANNEX_LOGS = Path(TARGET["boundedGapBuildEvidenceRoot"])
OUT = RUN / "00_CONTROL" / "CLAIM_MAP.csv"

PUBLIC = {
    "PaperIV.Erdos81AllOrders.erdos81_all_orders": ("Theorem A", "Teorema A", "B06", "all n, chordal, O(n)"),
    "PaperIV.Erdos81AllOrders.erdos81_all_orders_additive": ("Theorem A", "Teorema A", "B06", "all n, chordal, additive b"),
    "PaperIV.Erdos81Unconditional.erdos81_cliquePartition": ("Theorem B", "Teorema B", "B06", "eventual, chordal, pieces at most 4"),
    "PaperIV.PaperTheorems.erdos81_max_eq": ("Theorem B", "Teorema B", "B07", "eventual maximum over chordal graphs"),
    "PaperIV.DefectSharpPublication.rooted_defect_eventual": ("Theorem C", "Teorema C", "B06", "fixed rooted simplicial defect, eventual"),
    "PaperIV.DefectSharpPublication.rooted_defect_maximum": ("Theorem C", "Teorema C", "B07", "eventual maximum in fixed rooted-defect class"),
    "PaperIV.DefectSharpPublication.exists_defect_lower_witness": ("Appendix E.3", "Apéndice E.3", "B07", "unrestricted lower witness"),
    "PaperIV.FarRounding.exists_cliquePartition_of_packing": ("Lemma 2.1", "Lema 2.1", "B01", "physical mixed packing completed by K2 with exact count"),
    "PaperIV.LossBudget.size_add_gain_eq": ("Lemma 2.1 / budget (1.3)", "Lema 2.1 / presupuesto (1.3)", "B01", "any complete clique partition, unrestricted gain identity"),
    "PaperIV.LossBudget.budget_iff": ("Budget (1.3)", "Presupuesto (1.3)", "B01", "any physical partition, exact budget equivalence"),
    "PaperIV.RC01Final.rc01_uniformRoundingTarget": ("Theorem 3.1", "Teorema 3.1", "B03", "positive precision fixed before arbitrary graph"),
    "PaperIV.FarRegimeAllGraphs.farRegime_cliquePartition_allGraphs": ("Corollary 3.5", "Corolario 3.5", "B03", "all graphs, far regime"),
    "PaperIV.PaperIIISlackNibbleAdapter.boundedRankNibbleAt": ("Lemma 3.2", "Lema 3.2", "B03", "Paper III bounded-rank slack nibble adapter"),
    "PaperIV.MarkedQuotaSlackGate.slackMarkedQuotaNibbleAt_proved": ("Lemma 3.3", "Lema 3.3", "B03", "one matching, total and marked quotas"),
    "PaperIV.JointTwoQuotaPhysical.mixed_physical_packing_of_slackMarkedQuota": ("Lemma 3.4", "Lema 3.4", "B03", "physical gain lower bound with two typed quotas"),
    "PaperIV.RC01MarkedRounding.exists_packing_loss_le_of_slackMarkedQuotaBudget": ("Appendix C / selector budget", "Apéndice C / presupuesto del selector", "B03", "uniform target after an explicit numeric budget"),
    "PaperIV.GatedTerminalSplit.exists_split_terminal_symmetrizationPath": ("Lemma 4.1", "Lema 4.1", "B05", "chordal finite graph, monotone mixed path"),
    "PaperIV.NearH1WindowAccounts.exists_window_accounts": ("Lemma 4.2", "Lema 4.2", "B05", "window-local accounts, original optimum retained"),
    "PaperIV.NearH1Localization.exists_localized_split_core": ("Proposition 4.3", "Proposición 4.3", "B05", "near fractional regime, explicit near threshold"),
    "PaperIV.NearH1LocalConstructor.exists_near_partition_paid_by_root_sharp": ("Theorem 5.0", "Teorema 5.0", "B05", "local proximity and fractional value hypotheses"),
    "PaperIV.NearH1LocalConstructor.exists_near_partition_paid_by_root": ("Theorem 5.0 / earlier interface", "Teorema 5.0 / interfaz anterior", "B05", "local proximity and fractional value hypotheses"),
    "PaperIV.ChordalCoreMissing.exists_core_clique_with_calibration": ("Lemma 5.1", "Lema 5.1", "B05", "actual clique extracted from comparator"),
    "PaperIV.NearH1CalibratedRoot.exists_regularizedRoot_of_split_comparator": ("Proposition 5.2", "Proposición 5.2", "B05", "calibrated root assembled from extracted clique"),
    "PaperIV.RootRegularizationBridge.exists_regularizedRoot_engineFree": ("Proposition 5.2", "Proposición 5.2", "B05", "regularization on the original graph"),
    "PaperIV.NearH1StructureWitness.exists_nearStructureWitness_of_split_comparator": ("Lemma 5.3", "Lema 5.3", "B05", "same root and physical accounts"),
    "PaperIV.NearCriticalDichotomy.chordal_far_or_criticalRoot": ("Corollary 5.4", "Corolario 5.4", "B05", "far or critical root"),
    "PaperIV.NearCriticalDichotomy.chordal_far_or_edge_density": ("Corollary 5.4", "Corolario 5.4", "B05", "far or near edge density"),
    "PaperIV.SplitCompleteSharpLower.cliquePartition_size_ge_baseline_unrestricted": ("Section 6.1", "Sección 6.1", "B07", "unrestricted clique partitions"),
    "PaperIV.SplitCompleteRigidity.optimal_cores": ("Section 6.2", "Sección 6.2", "B07", "all maximizing core sizes, including double case"),
    "PaperIV.LinearCoefficient.linear_coefficient_optimal": ("Section 6.3", "Sección 6.3", "B07", "linear coefficient lower bound"),
    "PaperIV.SplitCompleteDefect.size_add_choose_eq_mul_add_sum_defect": ("Section 6.4", "Sección 6.4", "B07", "unrestricted partition defect identity"),
    "PaperIV.SharpConstantOptimality.erdos81_quadratic_constant_optimal": ("Section 6.3", "Sección 6.3", "B07", "rational quadratic coefficient lower bound"),
    "PaperIV.SharpConstantOptimality.erdos81_quadratic_constant_isLeast": ("Section 6.3", "Sección 6.3", "B07", "rational quadratic coefficient leastness"),
    "PaperIV.IntegralStability.chordal_linear_stability_sixteen": ("Theorem 6.1", "Teorema 6.1", "B08", "eventual, small nonnegative delta"),
    "PaperIV.RootPartitionStability.chordal_partition_stability": ("Corollary 6.1a", "Corolario 6.1a", "B08", "same root, every unrestricted partition"),
    "PaperIV.RootPartitionStability.sum_rootPieceDefect_eq": ("Identity (6.7b)", "Identidad (6.7b)", "B08", "unrestricted partition defect sum"),
    "PaperIV.ExtremalClassification.chordal_extremal_classification": ("Corollary 6.2", "Corolario 6.2", "B08", "eventual extremizers"),
    "PaperIV.SplitMixedGap.mixed_gap_zero": ("Proposition 6.3", "Proposición 6.3", "B07", "complete-split, 2<=core<=hosts"),
    "PaperIV.ReserveIdentity.targetSize_eq_baseline_add_reserve": ("Section 6.7", "Sección 6.7", "B07", "core displacement reserve"),
    "PaperIV.HybridDichotomy.chordal_far_or_nearStructure": ("Dichotomy 1.5", "Dicotomía 1.5", "B06", "far or literal near-structure witness"),
    "PaperIV.SpreadAbsorptionCompatibility.exists_budgeted_compatible_spread_absorber": ("Appendix B.1", "Apéndice B.1", "B08", "free resources and one packing"),
    "PaperIV.BalancedReserve.exists_balanced_reserve": ("Appendix B.2", "Apéndice B.2", "B09", "Beck-Fiala reserve hypothesis"),
    "PaperIV.FourHostClosure.exists_fourHost_packing": ("Appendix B.3", "Apéndice B.3", "B09", "four universal hosts, max degree at most 3"),
    "PaperIV.DefectSharpPublication.order_three_insufficient": ("Proposition D.2", "Proposición D.2", "B07", "n congruent 4 mod 6"),
    "PaperIV.ExplicitThreshold.erdos81_all_orders_explicit": ("Section 6.3", "Sección 6.3", "B04", "all orders, symbolic tower bound"),
    "PaperIV.ExplicitThreshold.erdos81_sharp_explicit": ("Section 6.3", "Sección 6.3", "B04", "eventual, symbolic tower threshold"),
    "E17Bridge.improved_far_loss_explicit": ("Equation (3.11)", "Ecuación (3.11)", "B04", "complete far-loss account; all graphs"),
    "E17Bridge.ExplicitAssembly.farRegime_allGraphs_explicit": ("Appendix C.3", "Apéndice C.3", "B04", "explicit far branch; all graphs"),
    "BoundedCliqueGap.chordal_gap_linear_cliqueFree": ("Section 8.2", "Sección 8.2", "B08", "triangular gap only; clique-free bound d+2"),
    "FarExploration.CleanupRigidVerdict.threshold_gt_exp": ("Proposition 8.1", "Proposición 8.1", "B03", "conditional cleanup contract; all graphs"),
    "FarExploration.CleanupRigidVerdict.threshold_gt_exp_seventy_two": ("Proposition 8.1", "Proposición 8.1", "B03", "conditional cleanup contract; selected epsilon"),
    "ThreeRegime.CompleteStateAllOrders.complete_state_closes": ("Appendix D", "Apéndice D", "B07", "complete graphs, all orders"),
}

SOURCE_MODULE_OVERRIDE = {
    "PaperI.FiniteLP.exists_optimal_pair": "PaperI.FiniteLPDuality",
    "BoundedCliqueGap.chordal_gap_linear_cliqueFree": "BoundedCliqueGap.Gap",
    "E17Bridge.improved_far_loss_explicit": "E17.ExplicitFarAssembly",
    "E17Bridge.ExplicitAssembly.farRegime_allGraphs_explicit": "E17.ExplicitFarAssembly",
}


def sha(data: str) -> str:
    return hashlib.sha256(data.encode("utf-8")).hexdigest()


def relative(path: Path) -> str:
    return path.relative_to(PAPER).as_posix()


def source_header(path: Path, short: str) -> str | None:
    if not path.is_file():
        return None
    data = path.read_text(encoding="utf-8")
    hit = re.search(r"^(?:theorem|lemma|def|abbrev|structure)\s+" + re.escape(short)
                    + r"\b", data, re.M)
    if hit is None:
        return None
    depth = 0
    end = None
    for i in range(hit.end(), len(data) - 1):
        char = data[i]
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth -= 1
        if depth == 0 and data.startswith(":=", i):
            end = i
            break
    return data[hit.start():end].strip() if end is not None else None


def main() -> int:
    sources = json.loads((LOGS / "SOURCES.json").read_text(encoding="utf-8"))
    annex_sources = json.loads((ANNEX_LOGS / "SOURCES.json").read_text(encoding="utf-8"))
    src_by_module = {x["module"]: x for x in sources}
    annex_by_module = {x["module"]: x for x in annex_sources}
    cone_log = (LOGS / "modules" / "PaperIV.ConeAudit.log").read_text(encoding="utf-8")
    cone_names = re.findall(r"^OK\s+([\w.]+)$", cone_log, re.M)
    export_source = (MAIN / "ReleaseExportCheck.lean").read_text(encoding="utf-8")
    export_names = set(re.findall(r"^#check\s+([\w.]+)", export_source, re.M))
    query_names: dict[str, str] = {}
    for query_path in (RUN / "20_EVIDENCE" / "G3_FORMAL").glob("*.lean"):
        query_source = query_path.read_text(encoding="utf-8")
        if query_source.splitlines()[0].strip() != "import PaperIV":
            continue
        for found in re.findall(r"^#(?:check|print axioms)\s+([\w.]+)", query_source, re.M):
            query_names[found] = query_path.name
    axiom_file_by_name: dict[str, Path] = {}
    for log in sorted((LOGS / "modules").glob("*.log")):
        contents = log.read_text(encoding="utf-8", errors="replace")
        for found in re.findall(r"'([^']+)' depends on axioms:", contents):
            axiom_file_by_name.setdefault(found, log)
    for log in sorted((ANNEX_LOGS / "modules").glob("*.log")):
        if not log.name.startswith("BoundedCliqueGap."):
            continue
        contents = log.read_text(encoding="utf-8", errors="replace")
        for found in re.findall(r"'([^']+)' depends on axioms:", contents):
            axiom_file_by_name.setdefault(found, log)
    b7_log = LOGS / "modules" / "E17.ExplicitFarAudit.log"
    for found in re.findall(r"PASS B7 numerical link ([\w.]+): \d+ constants; axioms \[", b7_log.read_text(encoding="utf-8")):
        axiom_file_by_name.setdefault(found, b7_log)
    for query_log in (RUN / "20_EVIDENCE" / "G3_FORMAL").glob("*.stdout.txt"):
        for found in re.findall(r"'([^']+)' depends on axioms:", query_log.read_text(encoding="utf-8")):
            axiom_file_by_name[found] = query_log
    names = list(dict.fromkeys(cone_names + list(PUBLIC)))
    print(f"Cone declarations: {len(cone_names)}; mapped names: {len(names)}")
    fieldnames = [
        "claim_id", "section_es", "section_en", "statement_hash", "protected_hypotheses",
        "lean_declaration", "module", "public_entry", "export_evidence", "build_evidence",
        "axiom_evidence", "constant_cone_evidence", "math_block", "scope", "verdict",
    ]
    rows = []
    for number, name in enumerate(names, 1):
        section_en, section_es, block, scope = PUBLIC.get(
            name, ("Appendix A / supporting declaration", "Apéndice A / declaración auxiliar",
                   "B09", "formal supporting declaration; no separate prose theorem"))
        module = SOURCE_MODULE_OVERRIDE.get(name, name.rsplit(".", 1)[0])
        record = src_by_module.get(module)
        root = MAIN
        evidence = LOGS
        if record is None and module.startswith("BoundedCliqueGap"):
            record = annex_by_module.get(module)
            root = ANNEX
            evidence = ANNEX_LOGS
        if record is None:
            # Some namespaces differ from the file name. Locate the declaration
            # by its exact theorem header, without guessing a module from a name.
            candidates = [x for x in sources if source_header(MAIN / x["path"], name.split(".")[-1])]
            if len(candidates) == 1:
                record = candidates[0]
                module = record["module"]
        header = source_header(root / record["path"], name.split(".")[-1]) if record else None
        built = bool(record and (evidence / "modules" / f"{module}.exit").is_file()
                     and (evidence / "modules" / f"{module}.exit").read_text().strip() == "EXIT_CODE=0")
        audit_log = axiom_file_by_name.get(name)
        is_cone = name in cone_names
        is_export = name in export_names
        is_query_export = name in query_names
        rows.append({
            "claim_id": f"C{number:03d}", "section_es": section_es,
            "section_en": section_en, "statement_hash": sha(header) if header else "",
            "protected_hypotheses": scope, "lean_declaration": name,
            "module": module if record else "UNRESOLVED", "public_entry":
            "PaperIV" if is_export or is_query_export else "separate audit target" if name.startswith(("FarExploration.", "ThreeRegime."))
            else "separate source annex" if name.startswith("BoundedCliqueGap.") else "source module",
            "export_evidence": "ReleaseExportCheck.log" if is_export else
            f"{query_names[name]} imported PaperIV" if is_query_export else "not root-exported",
            "build_evidence": relative(evidence / "modules" / f"{module}.log") if built else "MISSING",
            "axiom_evidence": relative(audit_log) if audit_log else "NOT_PRINTED_HERE",
            "constant_cone_evidence": relative(LOGS / "modules" / "PaperIV.ConeAudit.log")
            if is_cone else "not in 81-declaration cone audit",
            "math_block": block, "scope": scope,
            "verdict": ("PASS_INTERNAL_SCOPE_REVIEW" if name in PUBLIC else "PASS_TRANSITIVE_TRACE")
            if built and header and audit_log else "TRACE_INCOMPLETE",
        })
    OUT.parent.mkdir(parents=True, exist_ok=True)
    with OUT.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)
    print(json.dumps({"rows": len(rows), "cone": len(cone_names),
                      "traceIncomplete": [r["lean_declaration"] for r in rows
                                          if r["verdict"] == "TRACE_INCOMPLETE"],
                      "publicNotRootExported": [r["lean_declaration"] for r in rows
                                                if r["lean_declaration"] in PUBLIC
                                                and r["export_evidence"] == "not root-exported"]}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
