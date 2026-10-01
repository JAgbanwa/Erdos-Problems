# Publication cleanup scope

The official repository base contained Papers I–III and no Paper IV package.
The Paper IV draft was assembled in a clean Git worktree using an explicit
allowlist, rather than adding the research workspace wholesale.

Included:

- one active bilingual manuscript revision, v0.8, labelled draft;
- its required figures, final TeX/PDF sources and recorded visual QA;
- the single source freeze used by that revision;
- baseline evidence, new internal checks and reproduction instructions.

Excluded:

- earlier local `draft_v0.*` directories and feedback collections;
- Aristotle returns, jobs, prompts and alternative working trees;
- external repository checkouts and exploratory downloads;
- API keys, `.env` files, build caches, executables and compiled Lean objects.

No older research source was deleted. Those files remain in the author's
separate working directory and are not staged for this publication. The
published historical packages and audit histories of Papers I–III are
unchanged. This is a publication cleanup, not an erasure of research history.
