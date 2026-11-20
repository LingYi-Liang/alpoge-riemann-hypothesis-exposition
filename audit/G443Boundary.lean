import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableConv
import Lean.Util.FoldConsts
import Lean.Elab.Command

/-! Print direct references into the PDE block from the types and proof terms
of all other release modules loaded by the three identified clients. -/

open Lean Elab Command

namespace G443Boundary

private def block := `GroundTheory.AutomorphicForms.PartialDifferential

private def owner? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  return env.header.moduleNames[idx.toNat]!

private def extraNames (ci : ConstantInfo) : NameSet := Id.run do
  let mut names : NameSet := {}
  match ci with
  | .inductInfo v =>
    for n in v.ctors do names := names.insert n
    for n in v.all do names := names.insert n
  | .ctorInfo v => names := names.insert v.induct
  | .recInfo v =>
    for n in v.all do names := names.insert n
    for r in v.rules do names := (names.insert r.ctor) ++ r.rhs.getUsedConstantsAsSet
  | _ => pure ()
  return names

run_cmd do
  let env ← getEnv
  let mut modules := #[]
  let mut refs := #[]
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if !(`GroundTheory).isPrefixOf m || block.isPrefixOf m then continue
    let names := env.header.moduleData[i]!.constNames
    modules := modules.push <| Json.mkObj [("module", toJson m.toString), ("declarations", toJson names.size)]
    for n in names do
      let some ci := env.checked.get.find? n | throwError "Missing imported declaration {n}"
      let body := (ci.value? (allowOpaque := true)).map Expr.getUsedConstantsAsSet |>.getD {}
      for (site, ds) in [("type",ci.type.getUsedConstantsAsSet), ("value",body), ("rule",extraNames ci)] do
        for dep in ds do
          let some owner := owner? env dep | continue
          if block.isPrefixOf owner then
            refs := refs.push <| Json.mkObj [("client_module", toJson m.toString),
              ("client",toJson n.toString), ("site",toJson site),
              ("provider_module", toJson owner.toString), ("provider",toJson dep.toString)]
  liftIO <| IO.println <| "G443_USES " ++ (Json.mkObj [("examined",toJson modules),("references",toJson refs)]).compress

end G443Boundary

#print axioms GroundTheory.Automorphic.Sobolev.analyticOn_of_elliptic
#print axioms GroundTheory.Automorphic.Sobolev.exists_parametrix
#print axioms GroundTheory.Automorphic.Sobolev.exists_diffOp_eq_tupleOp
#print axioms GroundTheory.Automorphic.IsExpLieAlgebra.analyticAt_of_aeval_laplacian_eq_zero
#print axioms GroundTheory.Automorphic.IsExpLieAlgebra.exists_eq_conv_of_aeval_laplacian_eq_zero
#print axioms GroundTheory.Automorphic.IsExpLieAlgebra.exists_kernel_eq_conv_of_aeval_laplacian
