# Command ledger

Every command that produced retained evidence, in execution order. Logs are under
`10_LOGS/lean/` and gate results under `20_EVIDENCE/`.

```
# E0 intake
python v13_E0_intake.py                        -> E0_intake.json, TARGET_SHA256.txt

# E4 clean room, following MATHLIB_REPRODUCTION_PROTOCOL.md
sha256 of PAPER_III_lean_v1.3_freeze.zip       -> 2eb0ff20...d300, matches the request
unzip into C:\ea\P3                           (hash verified BEFORE extraction)
diff lake-manifest.json lakefile.toml lean-toolchain against the freeze  -> byte-identical
lean --version ; lake --version                -> 4.28.0 / 5.0.0-src+7e01a1b
mklink /J .lake\packages <auditor cache>
git -C .lake\packages\<pkg> rev-parse HEAD     -> 9/9 exact
git -C .lake\packages\<pkg> status --porcelain  -> 9/9 empty
lake exe cache get                             -> 01_cache_get.log, exit 0, nothing to download
proof that .lake/build is absent               -> 02_pre_build_clean_proof.txt
lake build PaperIII                            -> 03_lake_build_PaperIII.log, 8203 jobs, exit 0
lake env lean FreezeAxioms*.lean  (x8)         -> 04_*.log, 7 of 8 FAIL: see EXT-V13-001
lake build <the 7 roots the queries import>    -> 06_lake_build_query_roots.log, 8444 jobs, exit 0
lake env lean FreezeAxioms*.lean  (x8, again)  -> 07_*.log, all exit 0, 42 surfaces
python v13_import_closure.py                   -> import_closure.json

# E3 formal conformance
lake env lean AuditorE3.lean                   -> 08_AuditorE3.log, exit 0

# E1 / E5 manuscript
python v13_regression_text.py                  -> regression_text.json
python v13_E5_pdf_qa.py                        -> E5_pdf_qa.json, per-page renders

# E2 mathematics
python v13_E2_section9.py                      -> section9.json

# E6 / E7
python v13_E6_E7.py                            -> prior_art.json, release_package.json
                                                  (includes the final hash re-verification)
```
