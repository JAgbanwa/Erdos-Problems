# Announcement — Three-Paper Series on Clique Partitions, Fractional Covers, and Split/Chordal Graphs

I am making available a three-paper research series on clique partitions and fractional clique parameters in split and chordal graphs.

The manuscripts are final author versions, pending independent human peer review and journal refereeing. Together, they develop a progression from a general affine reduction method, to exact fractional extremal structure, and finally to a linear-error integral theorem.

---

## Paper I  
### *Affine Profile Reduction for Fractional Triangle Covers in Split Graphs*

Paper I develops the methodological foundation of the series.

Its central mechanism is

\[
\text{fixed-polytope concavity}
\Longrightarrow
\text{pure-profile reduction}
\Longrightarrow
\text{three-orbit optimization}.
\]

The paper shows that heterogeneous neighborhood data can be encoded as an affine objective over a fixed fractional triangle-cover polytope. Concavity then reduces arbitrary mixtures of neighborhood types to pure profiles.

The framework also includes:

- nonnegative real masses on neighborhood profiles;
- heterogeneous edge baselines;
- Dirac extremization on the finite profile simplex;
- Lipschitz stability under perturbations;
- an exact weighted three-orbit formula.

As a graph-theoretic application, the method proves the sharp leading constant \(1/6\) for clique partitions of split graphs.

**Final author manuscript:** v1.1.

---

## Paper II  
### *Complete-Split Extremizers for Fractional Clique Parameters on Chordal Graphs*

Paper II builds on the fractional clone-symmetrization framework of Balogh, He, Krueger, Nguyen, and Wigal.

The paper proves that their symmetrization principle admits a constrained chordal specialization: symmetrization is restricted to suitable maximal clone classes containing simplicial vertices, chordality is preserved, and the terminal chordal graphs are precisely the complete split graphs

\[
K_p\vee\overline K_{n-p}.
\]

Thus the extremal optimization over all \(n\)-vertex chordal graphs collapses to a one-parameter family of \(n+1\) complete split graphs, which are also threshold graphs.

For triangles, this gives the exact finite **fractional** maximum

\[
\max_{\substack{|V(G)|=n\\G\text{ chordal}}}
\left(|E(G)|-2\nu_3^*(G)\right)
=
\left\lfloor\frac{(2n+1)^2}{24}\right\rfloor.
\]

The paper also gives:

- an exact finite fractional theorem for general \(K_r\);
- a threshold-graph sandwich;
- a polynomial-time reduction to \(n+1\) complete-split candidates for fixed \(r\).

**Final author manuscript:** v0.8.

---

## Paper III  
### *Linear-Error Clique Partitions of Split Graphs via Structured Triangle Packing*

Paper III addresses the integral problem.

It proves that there is an absolute constant \(C\) such that every split graph \(G\) on \(n\) vertices satisfies

\[
\operatorname{cp}(G)
\le
\frac{n^2}{6}+Cn.
\]

The proof combines three regimes:

1. a bulk regime, handled through an exact common-profile LP and fractional-to-integral rounding;
2. a sparse-independent regime, handled through anchored matchings and divisibility correction;
3. a near-extremal corridor, handled through factorization, polarization, and shifted-center completion.

The near-extremal corridor is treated quantitatively with explicit constants. The global constant \(C\), however, is not made explicit in the present proof because the bulk and sparse-independent regimes use external asymptotic theorems with unquantified thresholds.

This strengthens the asymptotic \(1/6\) result to the correct linear-error scale.

**Final author manuscript:** v1.0.4.

---

# How the three papers fit together

The papers are complementary.

- **Paper I** develops the affine profile-reduction method.
- **Paper II** identifies the exact fractional extremizers on chordal graphs.
- **Paper III** proves the integral linear-error theorem on split graphs.

In compact form,

\[
\boxed{
\text{method}
\longrightarrow
\text{exact fractional structure}
\longrightarrow
\text{integral linear error}.
}
\]

The complete-split family

\[
K_p\vee\overline K_{2p}
\]

appears throughout the series as the canonical extremal geometry at the \(1/6\) scale.

---

# Attribution and novelty status

The general fractional clone-symmetrization principle used in Paper II is due to Balogh, He, Krueger, Nguyen, and Wigal. Paper II specializes that framework to chordal graphs, proves chordality preservation under the constrained operation, identifies the complete-split terminal family, and performs the resulting exact finite optimization.

The novelty of the chordal-to-complete-split specialization and of the affine-profile coordinate system developed in Paper I remains subject to specialist literature review and forward-citation tracking.

---

# A fourth paper in progress: the Universal Gap program

A fourth manuscript is now in development.

Its main target is the universal linear integrality-gap question for split graphs:

\[
\boxed{
\nu_3^*(G)-\nu_3(G)
\le
C|V(G)|
}
\]

for some absolute constant \(C\).

Paper III does **not** prove this statement. Its linear-error clique-partition theorem instead uses quadratic fractional slack away from the extremal corridor to absorb a potentially superlinear integrality gap.

The fourth-paper program asks whether that indirect compensation can be replaced by a direct universal rounding theorem.

Current research directions include:

- exact common-profile formulas;
- zero-gap complete-split regimes;
- replication and local rounding modules;
- Ferrers-type structure, shells, and interface control;
- identification of the correct stability mechanism behind near-extremal profiles.

Possible auxiliary stability languages include classical edit distance and, if compatible with the discrete obstruction structure, graphon or cut-distance formulations. These are exploratory possibilities, not claims of the current program.

The objective is to determine whether the fractional and integral triangle-packing optima in every split graph are always separated by only a linear term.

This fourth paper remains a research program, not a completed theorem.

---

# Research status and transparency

The three completed manuscripts have undergone extensive algebraic, computational, adversarial, and editorial checking.

Their accompanying packages include:

- proof-dependency ledgers;
- claims matrices;
- exact regression tests;
- static and PDF audits;
- SHA-256 manifests.

The computational material is supplementary and is not used as a logical premise of the theorems.

The manuscripts have not yet completed independent human peer review or journal refereeing.

AI-assisted systems were used during exploratory, computational, organizational, adversarial, and editorial stages. All mathematical claims, citations, code, and final decisions remain the responsibility of the author.

---

## Series status

\[
\boxed{\text{Paper I — Final Author Manuscript v1.1}}
\]

\[
\boxed{\text{Paper II — Final Author Manuscript v0.8}}
\]

\[
\boxed{\text{Paper III — Final Author Manuscript v1.0.4}}
\]

\[
\boxed{\text{Paper IV — Universal Gap program in progress}}
\]

---

**Juan Pablo Traverso Gianini**  
Independent researcher  
Santiago, Chile
