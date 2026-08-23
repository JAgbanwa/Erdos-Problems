# Command ledger

Exact commands, in execution order. Full stdout/stderr, exit codes and timestamps are retained
under `20_EVIDENCE/G5_LEAN/results/`.

```
# gate 1
python v14_E0_intake.py                     -> E0_intake.json, TARGET_SHA256.txt

# the two v1.3 MAJOR checks
grep Theorem_1_1_Final PaperIII.lean         -> lines 46-47 present
read Proposition 7.4 in both manuscripts     -> hypothesis and inequality present in ES

# gate 5, per the request's procedure
git config --global core.longpaths true
sha256 PAPER_III_lean_v1.4_freeze.zip        -> 79ee24c3...7104, matches the request
unzip into C:\p3a                            (hash verified BEFORE extraction)
diff lake-manifest.json lakefile.toml lean-toolchain vs the freeze -> byte-identical
lean --version ; lake --version              -> 4.28.0 / 5.0.0-src+7e01a1b
mklink /J .lake\packages <auditor cache>
git -C .lake\packages\<pkg> rev-parse HEAD    -> 9/9 exact
git -C .lake\packages\<pkg> status --porcelain -> 9/9 empty
lake exe cache get                           -> hung on network; terminated and documented
proof .lake/build absent, 0 project objects  -> 02_pre_build_clean.txt
lake build PaperIII                          -> 8455 jobs, exit 0, 70m10s, UNINTERRUPTED
verify Theorem_1_1_Final.olean present       -> yes; 429 project objects created
lake build BKLO.MainDenseUnconditional Nibble.AX1Closed PaperIII.CanonicalTrianglePacking \
           PaperIII.Obstructions PaperIII.PaperImprovementsGate PaperIII.PublicAPI \
           PaperIII.Theorem_1_1_Final       -> 8444 jobs, exit 0, 8m38s
lake env lean FreezeAxioms.lean              -> exit 0, 12 surfaces
lake env lean FreezeAxiomsAuditClosure.lean  -> exit 0, 13 surfaces
lake env lean FreezeAxiomsAX1.lean           -> exit 0, 1 surface
lake env lean FreezeAxiomsAX1Closure.lean    -> exit 0, 4 surfaces
lake env lean FreezeAxiomsAX2.lean           -> exit 0, 1 surface
lake env lean FreezeAxiomsByproducts.lean    -> exit 0, 2 surfaces
lake env lean FreezeAxiomsCanonical.lean     -> exit 0, 7 surfaces
lake env lean FreezeAxiomsObstructions.lean  -> exit 0, 2 surfaces

# gates 6, 7
python v14_import_closure.py                 -> import_closure.json
lake env lean AuditorE3.lean                 -> exit 0, 8 auditor theorems, clean footprints

# gates 2, 3, 4
python v14_regression_text.py                -> regression_text.json
python v14_bilingual_deep.py                 -> bilingual_deep.json
python v14_inspect_diffs.py                  -> the four flagged blocks, all benign
python v14_table_row_check.py                -> the allowbreak artifact
python v14_tex_pdf_sync.py                   -> 84/84 tokens, 66/66 tags in TeX and PDF
python v14_E5_pdf_qa.py                      -> per-page renders, E5_pdf_qa.json

# E2
python v14_math_delta.py                     -> Sections 1-10 and 12 byte-identical to v1.3
python v14_E2_full.py                        -> 23 items, 22 PASS
python v14_E2_section9.py                    -> 15 items, 14 PASS

# gate 8
web searches, recorded in novelty_refresh_v14.json with queries, corpora and negative results
```
