# Static series website

`index.html` is the bilingual series landing page. Each paper has a linked
`Paper*_explained_4_levels.html`. No server-side code, build system, CDN font
or mathematics renderer is required for the new landing page and Paper IV
page; figures and document links use relative paths. Existing Papers I–III
pages are preserved in their published form.

For local review, open `index.html` in a browser. For GitHub Pages, the static
tree supports publishing `main` at `/` with `.nojekyll`. Enabling Pages is a
separate remote action; preparation does not enable it or assert a live URL.

Before this release the repository homepage pointed to the Paper I explainer,
and its description described only Paper I and said that #81 remained open.
At publication of this update, replace those fields using the prepared values
in [GITHUB_METADATA_v1.23.json](GITHUB_METADATA_v1.23.json). The replacement
homepage uses the same HTML Preview service, but points to `index.html` for
the entire series. Do not switch it before that file exists on public `main`.

The series landing page explicitly explains that the older pages preserve
their historical context; their original scientific/audit packages are not
rewritten to retrospectively change their claims.
