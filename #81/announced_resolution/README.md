# Erdos Problem #81 - Three-Paper Public Release

This repository records the public release package for Juan Pablo Traverso Gianini's announced resolution of Erdos Problem #81 on clique partitions of chordal graphs.

## Main Result

The announced asymptotic theorem is

```text
max{cp(G): G chordal, |V(G)| = n} = (1/6 + o(1)) n^2.
```

The constant `1/6` is sharp.

## Current Public Release

The current release is organized in:

```text
public_release/
```

Direct links:

- [Final announcement PDF](public_release/THREE_PAPER_SERIES_ANNOUNCEMENT_FINAL.pdf)
- [Final announcement Markdown](public_release/THREE_PAPER_SERIES_ANNOUNCEMENT_FINAL.md)
- [Paper I PDF](public_release/PAPER_I/01_MANUSCRIPT/PAPER_I_v1.1.pdf)
- [Paper II PDF](public_release/PAPER_II/01_MANUSCRIPT/PAPER_II_v0.8.pdf)
- [Paper III PDF](public_release/PAPER_III/01_MANUSCRIPT/PAPER_III_v1.0.4.pdf)

It contains the final three-paper public package:

```text
public_release/
  00_SERIES_DOCUMENTS/
  PAPER_I/
  PAPER_II/
  PAPER_III/
  THREE_PAPER_SERIES_ANNOUNCEMENT_FINAL.md
  THREE_PAPER_SERIES_ANNOUNCEMENT_FINAL.tex
  THREE_PAPER_SERIES_ANNOUNCEMENT_FINAL.pdf
```

Each paper folder contains:

- manuscript sources and PDF;
- public audit records;
- reproducibility scripts and outputs;
- integrity artifacts.

The public-only integrity manifest is:

```text
public_release/00_PUBLIC_INTEGRITY/
```

This integrity folder was generated only from the public release files. It intentionally does not include the private internal working record.

The current announcement is mirrored separately for convenience in:

```text
announcement/THREE_PAPER_SERIES_ANNOUNCEMENT_FINAL.md
announcement/THREE_PAPER_SERIES_ANNOUNCEMENT_FINAL.tex
announcement/THREE_PAPER_SERIES_ANNOUNCEMENT_FINAL.pdf
```

## Sealed Complete Package

The complete author package, including internal working records, is archived only in encrypted form:

```text
sealed/THREE_PAPER_SERIES_COMPLETE_PACKAGE.zip.enc
sealed/THREE_PAPER_SERIES_COMPLETE_PACKAGE.zip.enc.sha256
```

The plaintext complete package and encryption key are not stored in this repository.

## Historical Materials

Earlier sealed archives may remain in this repository for timestamp/history purposes. The current public release should be read from `public_release/`. Obsolete root-level draft paper and note folders have been removed to avoid confusion with the final public package.

## Lean Formalisation

A Lean formalisation contribution is being tracked separately through pull request review.

## Author

Juan Pablo Traverso Gianini  
Independent researcher  
Santiago, Chile  
Email: jtraverso@gmail.com  
ORCID: https://orcid.org/0009-0003-6068-4096

## License

Documents, manuscripts, PDFs, LaTeX, Markdown files, and research announcements in this repository are licensed under:

Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International (CC BY-NC-ND 4.0)

Any verification scripts or source code may be licensed separately where explicitly stated.
