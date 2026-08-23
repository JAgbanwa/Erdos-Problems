# Paper III preprint draft v1.4

This is the self-contained v1.4 candidate for Paper III's first formal public release.
It supersedes the unpublished v1.3 review target; the v1.3 package remains preserved in
its own version directory with its external-audit record.

## Current status

- manuscript chain: synchronized EN/ES Markdown, LaTeX and PDF;
- formal snapshot: immutable source-only `lean_v1.4_freeze`;
- recorded author build: `PASS_CLEAN_ORIGIN_RESUMED` (8,455-job public root,
  8,444-job query roots, eight axiom files, 42 queries/35 distinct surfaces);
- internal audit: `PASS`, 144/144 executable checks and G0--G8 complete;
- external residual adversarial audit: pending;
- public release/tag: pending.

The recorded author build began from a clean source-only project but was resumed after
an application restart. This is disclosed rather than represented as an uninterrupted
reproduction. The external audit must perform the independent uninterrupted clean-room
build.

The manuscript is the semantic source. Any later semantic correction requires the full
Markdown → LaTeX → PDF → rendered QA → hashes chain and a rerun of affected audit gates.
