# Notes on Alpöge’s proposed proof of the Riemann hypothesis

This personal research project aims to give an English exposition of Levent Alpöge’s proposed proof of the Riemann hypothesis and its generalization to Dirichlet L-functions in at most 500 pages. The source is the Lean 4 formalization that Alpöge developed with Claude. [Alpöge’s announcement](https://alpo.ge/remark.pdf) · [Lean source at the revision used here](https://github.com/Deicyde/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005/src)

## Local elliptic estimates for the archimedean argument

This three-page note proves real analyticity for smooth solutions of a homogeneous elliptic equation with analytic coefficients. In the Lie group application, fix a monic polynomial $B$ of positive degree and a neighbourhood of the identity. The note constructs one smooth convolution kernel supported in that neighbourhood that reproduces every smooth solution of $B(\Delta)f=0$. [Read the note (PDF)](pdfs/G443-elliptic-regularity.pdf) · [LaTeX source](sections/elliptic-regularity.tex)

The source comparison covers 25 declarations used by three identified files that depend on the elliptic estimates. The note is indexed here as G443. Whether the final Riemann hypothesis and Dirichlet GRH proofs require any further property from these modules remains open. [Comparison with the original proof terms](audit/G443.md)
