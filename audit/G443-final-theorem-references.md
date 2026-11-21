# G443 in the kernel export of the five final theorems

21 November 2026. This audit compares the earlier three-client examination with the direct references in the five-theorem kernel export. All 25 G443 names in the earlier comparison occur in the final dependencies. The public dependency tables attribute 80 distinct outside references to these names across three client modules. The client constant in every row has theorem mask 31, meaning that all five final theorems depend on it.

| Client module | Type | Value | Total |
|---|---:|---:|---:|
| `GroundTheory.AutomorphicForms.HarishChandraRegularity.TupleOp` | 19 | 47 | 66 |
| `GroundTheory.AutomorphicForms.HarishChandraRegularity` | 3 | 7 | 10 |
| `GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableConv` | 0 | 4 | 4 |

In particular both `analyticOn_of_elliptic` and `exists_parametrix` occur in the dependency closure of each final theorem. The earlier 94 references came from all declarations in 21 original outside modules in the chosen local build. The kernel-export selection retains 80 of those references and the same 25 mathematical names. The companion note records an internal mathematical check of the elliptic results, compact supports and the uniform group kernels. [Mathematical checks](G443.md)

## Evidence and ownership

The original source archive is pinned by SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The local Lean 4.33.1 objects supply constant-name lists for all 23 original G443 modules and 21 adjoining project modules. The comparison uses the constants and direct edges of James Shore’s dataset v0.1.2 (release tag v0.1), derived from Andrew Sutherland’s kernel export. [Independent verification](https://math.mit.edu/~drew/grh/) · [Dataset and release assets](https://github.com/james-shore/rh-proof-dependencies/releases/tag/v0.1) · [Table definitions](https://github.com/james-shore/rh-proof-dependencies/blob/59dac69d6029575eec1f5e47c34e5e1d0da27410/docs/dataset.md) · [Previous local-to-client comparison](https://github.com/LingYi-Liang/alpoge-riemann-hypothesis-exposition/blob/3543f723ea34781a1d4d79cf2ca0fa362dbc38e1/audit/G443.md)

The public tables locate project modules using a source index. Every one of the 744 exported theorem and definition names attributed to G443 was also found in its compiled module records. Starting from the union of the public attribution and those compiled names gave 745 candidates. Parquet destination-ID minima, maxima and complete data-page dictionaries screened all 161 row groups of the 160,315,873-edge table. The three ID/site columns were decoded for each of the nine groups whose dictionaries contained a candidate. Outside clients were checked against their local compiled name lists.

One generated name, `ContDiffBump.mk.congr_simp`, also occurs in a G443 object. The public table classifies it as `dep-aux` for an external dependency. Its 23 own outgoing references contain no G443 result, and the seven other project modules that reference it have no import path to G443. Its eight occurrences are excluded from the mathematical count. [Underlying Mathlib constructor](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean#L70)

One equation lemma, `prinSymbol.eq_1`, occurs in original objects both inside and outside G443. No external reference to it occurs under the release attribution. Treating it as an outside-generated equation would introduce references only to names already covered in the 25.

Parquet asset digests recorded by the publisher: `constants.parquet` `0846858c260597663f6e3cbaff4eee9fcebf1a996a1ad7cc066b30a1af9ada7f`, `edges.parquet` `423a8dfe2150b5a5937679a5822f1477b7d10f241702afc6abd254813203aaae`. This audit fetched selected byte ranges. The full asset digests are provenance labels.

## The 80 references

Each row identifies one client constant, site and G443 provider. The provider prefix is `GroundTheory.Automorphic.Sobolev.`.

| Client constant | Site | G443 provider |
|---|---|---|
| `GroundTheory.Automorphic.IsExpLieAlgebra.exists_kernel_eq_conv_of_aeval_laplacian` | value | `diffOp` |
| `GroundTheory.Automorphic.IsExpLieAlgebra.exists_kernel_eq_conv_of_aeval_laplacian` | value | `exists_parametrix` |
| `GroundTheory.Automorphic.IsExpLieAlgebra.exists_kernel_eq_conv_of_aeval_laplacian` | value | `mabs` |
| `GroundTheory.Automorphic.IsExpLieAlgebra.exists_kernel_eq_conv_of_aeval_laplacian` | value | `prinSymbol` |
| `GroundTheory.Automorphic.IsExpLieAlgebra.analyticAt_of_aeval_laplacian_eq_zero` | value | `analyticOn_of_elliptic` |
| `GroundTheory.Automorphic.IsExpLieAlgebra.analyticAt_of_aeval_laplacian_eq_zero` | value | `diffOp` |
| `GroundTheory.Automorphic.IsExpLieAlgebra.analyticAt_of_aeval_laplacian_eq_zero` | value | `mabs` |
| `GroundTheory.Automorphic.IsExpLieAlgebra.analyticAt_of_aeval_laplacian_eq_zero` | value | `prinSymbol` |
| `GroundTheory.Automorphic.IsExpLieAlgebra.exists_elliptic_aeval_laplacian` | type | `diffOp` |
| `GroundTheory.Automorphic.IsExpLieAlgebra.exists_elliptic_aeval_laplacian` | type | `mabs` |
| `GroundTheory.Automorphic.IsExpLieAlgebra.exists_elliptic_aeval_laplacian` | type | `prinSymbol` |
| `GroundTheory.Automorphic.IsExpLieAlgebra.exists_elliptic_aeval_laplacian` | value | `diffOp` |
| `GroundTheory.Automorphic.IsExpLieAlgebra.exists_elliptic_aeval_laplacian` | value | `mabs` |
| `GroundTheory.Automorphic.IsExpLieAlgebra.exists_elliptic_aeval_laplacian` | value | `prinSymbol` |
| `GroundTheory.Automorphic.Sobolev.analyticOnNhd_fderiv_apply` | value | `ev` |
| `GroundTheory.Automorphic.Sobolev.contDiff_dList._f` | value | `contDiff_fderiv_apply` |
| `GroundTheory.Automorphic.Sobolev.dList_perm` | value | `fderiv_fderiv_apply_comm` |
| `GroundTheory.Automorphic.Sobolev.dT_eq_dList` | type | `dT` |
| `GroundTheory.Automorphic.Sobolev.dT_eq_dList` | value | `dT` |
| `GroundTheory.Automorphic.Sobolev.dT_eq_dList._f` | type | `dT` |
| `GroundTheory.Automorphic.Sobolev.dT_eq_dList._f` | value | `dT` |
| `GroundTheory.Automorphic.Sobolev.dT_eq_dList._f` | value | `dT_cons` |
| `GroundTheory.Automorphic.Sobolev.dT_eq_dList._f` | value | `dT_zero` |
| `GroundTheory.Automorphic.Sobolev.eq_sum_ev` | type | `ev` |
| `GroundTheory.Automorphic.Sobolev.eq_sum_ev` | value | `ev` |
| `GroundTheory.Automorphic.Sobolev.exists_diffOp_eq_tupleOp` | type | `diffOp` |
| `GroundTheory.Automorphic.Sobolev.exists_diffOp_eq_tupleOp` | type | `mabs` |
| `GroundTheory.Automorphic.Sobolev.exists_diffOp_eq_tupleOp` | type | `prinSymbol` |
| `GroundTheory.Automorphic.Sobolev.exists_diffOp_eq_tupleOp` | value | `diffOp` |
| `GroundTheory.Automorphic.Sobolev.exists_diffOp_eq_tupleOp` | value | `mabs` |
| `GroundTheory.Automorphic.Sobolev.exists_diffOp_eq_tupleOp` | value | `mpow` |
| `GroundTheory.Automorphic.Sobolev.exists_diffOp_eq_tupleOp` | value | `pdT` |
| `GroundTheory.Automorphic.Sobolev.exists_diffOp_eq_tupleOp` | value | `pderiv` |
| `GroundTheory.Automorphic.Sobolev.exists_diffOp_eq_tupleOp` | value | `prinSymbol` |
| `GroundTheory.Automorphic.Sobolev.exists_vfOp_tupleOp` | value | `pdT` |
| `GroundTheory.Automorphic.Sobolev.fderiv_apply_eq_sum` | type | `ev` |
| `GroundTheory.Automorphic.Sobolev.fderiv_apply_eq_sum` | value | `ev` |
| `GroundTheory.Automorphic.Sobolev.mabs_tupleCount` | type | `mabs` |
| `GroundTheory.Automorphic.Sobolev.mabs_tupleCount` | value | `mabs` |
| `GroundTheory.Automorphic.Sobolev.mdirList_eq_map` | type | `ev` |
| `GroundTheory.Automorphic.Sobolev.mdirList_eq_map` | type | `mdirList` |
| `GroundTheory.Automorphic.Sobolev.mdirList_eq_map` | value | `ev` |
| `GroundTheory.Automorphic.Sobolev.ofFn_mdir` | type | `mabs` |
| `GroundTheory.Automorphic.Sobolev.ofFn_mdir` | type | `mdir` |
| `GroundTheory.Automorphic.Sobolev.ofFn_mdir` | type | `mdirList` |
| `GroundTheory.Automorphic.Sobolev.ofFn_mdir` | value | `length_mdirList` |
| `GroundTheory.Automorphic.Sobolev.ofFn_mdir` | value | `mabs` |
| `GroundTheory.Automorphic.Sobolev.ofFn_mdir` | value | `mdir` |
| `GroundTheory.Automorphic.Sobolev.ofFn_mdir` | value | `mdir._proof_1` |
| `GroundTheory.Automorphic.Sobolev.ofFn_mdir` | value | `mdirList` |
| `GroundTheory.Automorphic.Sobolev.pdT_eq_pderiv` | type | `pdT` |
| `GroundTheory.Automorphic.Sobolev.pdT_eq_pderiv` | type | `pderiv` |
| `GroundTheory.Automorphic.Sobolev.pdT_eq_pderiv` | value | `dT` |
| `GroundTheory.Automorphic.Sobolev.pdT_eq_pderiv` | value | `ev` |
| `GroundTheory.Automorphic.Sobolev.pdT_eq_pderiv` | value | `mabs` |
| `GroundTheory.Automorphic.Sobolev.pdT_eq_pderiv` | value | `mdir` |
| `GroundTheory.Automorphic.Sobolev.pdT_eq_pderiv` | value | `mdirList` |
| `GroundTheory.Automorphic.Sobolev.pdT_eq_pderiv` | value | `pdT` |
| `GroundTheory.Automorphic.Sobolev.pdT_eq_pderiv` | value | `pdT.eq_1` |
| `GroundTheory.Automorphic.Sobolev.pdT_eq_pderiv` | value | `pderiv` |
| `GroundTheory.Automorphic.Sobolev.pdT_eq_pderiv` | value | `pderiv_eq_dT'` |
| `GroundTheory.Automorphic.Sobolev.prod_eq_mpow` | type | `mpow` |
| `GroundTheory.Automorphic.Sobolev.prod_eq_mpow` | value | `mpow` |
| `GroundTheory.Automorphic.Sobolev.prod_eq_mpow` | value | `mpow.eq_1` |
| `GroundTheory.Automorphic.Sobolev.tupleOp` | value | `pdT` |
| `GroundTheory.Automorphic.Sobolev.tupleOp.eq_1` | type | `pdT` |
| `GroundTheory.Automorphic.Sobolev.tupleOp_add` | value | `pdT` |
| `GroundTheory.Automorphic.Sobolev.tupleOp_idCoeff` | value | `pdT` |
| `GroundTheory.Automorphic.Sobolev.tupleOp_idCoeff` | value | `pdT_zero` |
| `GroundTheory.Automorphic.Sobolev.tupleOp_raiseCoeff` | value | `pdT` |
| `GroundTheory.Automorphic.Sobolev.tupleOp_shiftCoeff` | type | `pdT` |
| `GroundTheory.Automorphic.Sobolev.tupleOp_shiftCoeff` | value | `pdT` |
| `GroundTheory.Automorphic.Sobolev.tupleOp_smul` | value | `pdT` |
| `GroundTheory.Automorphic.Sobolev.tupleOp_sum` | value | `pdT` |
| `GroundTheory.Automorphic.Sobolev.vfOp_tupleOp_eq` | type | `pdT` |
| `GroundTheory.Automorphic.Sobolev.vfOp_tupleOp_eq` | value | `contDiff_pdT` |
| `GroundTheory.Automorphic.Sobolev.vfOp_tupleOp_eq` | value | `ev` |
| `GroundTheory.Automorphic.Sobolev.vfOp_tupleOp_eq` | value | `pd` |
| `GroundTheory.Automorphic.Sobolev.vfOp_tupleOp_eq` | value | `pdT` |
| `GroundTheory.Automorphic.Sobolev.vfOp_tupleOp_eq` | value | `pdT_cons` |
