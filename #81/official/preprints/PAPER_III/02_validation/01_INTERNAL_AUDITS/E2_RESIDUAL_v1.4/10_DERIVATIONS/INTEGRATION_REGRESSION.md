# Integration regression

The external v1.3 audit already closed `K-COVER`, the Section 4 fractional
margin, the Section 9 assembly algebra, the AX1/AX2 statement correspondence,
and the graph/hypergraph model bridge.  The English manuscript hash in this
residual is identical to that audited target, so those results are reused only
as unchanged regression evidence.

The residual kernels connect to that evidence as follows:

- `K-EPS-M` supplies the previously unchecked implication in §9.1 from the
  fixed bulk margin to `nu_3>=T`.
- `K-CORRIDOR` supplies Lemmas 5.1, 5.2, 6.1, and 7.1 used as inputs by the
  already checked high/low-dispersion assembly in §9.3.
- `K-SPARSE` supplies the whole conclusion invoked by the one-line §9.2
  endpoint.
- `K-GLOBAL` supplies the deletion and finite-order closure surrounding the
  eventual three-regime contradiction.

No inequality is used in the reverse direction at an interface.  The packing
observable at every connection is the integral `nu_3`; the only fractional
observable occurs in the bulk input, where the already validated
`nu_3Star` model bridge and the newly rederived nonnegative gap are used.

This integration check introduces no new premise and does not rely on the
forthcoming v1.4 clean build.

