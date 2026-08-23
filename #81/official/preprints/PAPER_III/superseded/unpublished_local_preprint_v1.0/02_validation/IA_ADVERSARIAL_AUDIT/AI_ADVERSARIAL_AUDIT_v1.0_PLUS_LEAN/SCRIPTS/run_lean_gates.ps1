$ErrorActionPreference = "Stop"

$Freeze = "C:\ERDOS\erdos81\github-sync\#81\official\preprints\PAPER_III\05_formalization\lean_v1.0_freeze"
$ResultRoot = "C:\ERDOS\erdos81\github-sync\#81\official\preprints\PAPER_III\02_validation\IA_ADVERSARIAL_AUDIT\AI_ADVERSARIAL_AUDIT_v1.0_PLUS_LEAN\RESULTS\blockG_lean_verification"
$Out = Join-Path $ResultRoot "results"
New-Item -ItemType Directory -Force -Path $Out | Out-Null

Set-Location $Freeze
lake build PaperIII *> (Join-Path $Out "lake_build.log")

@"
import PaperIII
#check PaperIII.AX1
#check PaperIII.AX2
#check PaperIII.Theorem_1_1
#check PaperIII.Corollary_1_2
#print axioms PaperIII.AX1
#print axioms PaperIII.AX2
#print axioms PaperIII.Theorem_1_1
#print axioms PaperIII.Corollary_1_2
"@ | Set-Content -Encoding UTF8 -Path (Join-Path $Out "AuditGates.lean")

lake env lean (Join-Path $Out "AuditGates.lean") *> (Join-Path $Out "lean_axiom_gates.log")
rg -n "sorry|admit|axiom|unsafe" . *> (Join-Path $Out "source_escape_hatch_scan.log"); if ($LASTEXITCODE -eq 1) { $global:LASTEXITCODE = 0 }
