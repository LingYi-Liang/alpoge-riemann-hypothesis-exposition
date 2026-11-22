# Notes on Alpöge’s proposed proof of the Riemann hypothesis

This personal research project aims to give an English exposition of Levent Alpöge’s proposed proof of the Riemann hypothesis and its generalization to Dirichlet L-functions in at most 500 pages. The source is the Lean 4 formalization that Alpöge developed with Claude. [Alpöge’s announcement](https://alpo.ge/remark.pdf) · [Lean source at the revision used here](https://github.com/Deicyde/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005/src)

## Integral theta periods and Dirichlet GRH

This 14-page English abridgment follows the nine sections of the 47-page exposition through the common torsion window and the functional equation. The appendix retains all 28 rows of the original Lean concordance. The source supplies the matching, local estimates and simultaneous arithmetic realization used in the deduction. The coverage review documents corrections to the earlier 12-page draft and identifies the arguments that still require the source. [Manuscript (PDF)](pdfs/theta-periods-abridged.pdf) · [LaTeX source](standalone/theta-periods-abridged.tex) · [Coverage review](audit/theta-periods-coverage.md) · [Original exposition](https://doi.org/10.5281/zenodo.24413008)

Lemma 8.A extends the Gaussian count to all high-conductor terms, proves a uniform bound for their sum, and gives both symplectic cases a common dyadic level. The local arithmetic constructions retain their original hypotheses. [Section 8 comparison and verification](audit/section8-counts.md)

## Local elliptic estimates for the archimedean argument

This three-page note proves real analyticity for smooth solutions of a homogeneous elliptic equation with analytic coefficients. In the Lie group application, fix a monic polynomial $B$ of positive degree and a neighbourhood of the identity. The note constructs one smooth convolution kernel supported in that neighbourhood that reproduces every smooth solution of $B(\Delta)f=0$. [Read the note (PDF)](pdfs/G443-elliptic-regularity.pdf) · [LaTeX source](sections/elliptic-regularity.tex)

The note is indexed here as G443. In the kernel export of the five final theorems, three outside modules make 80 direct references to 25 G443 declarations. The comparison traces those declarations into the English argument and checks the hypotheses used in the shortening. [Mathematical checks](audit/G443.md) · [The 80 references](audit/G443-final-theorem-references.md)
