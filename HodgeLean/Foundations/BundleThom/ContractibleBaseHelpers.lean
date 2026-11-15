import HodgeLean.Foundations.BundleThom.ProductContractionHelpers

/-! # Contractions of a contractible base to a specified point

Every chosen fibre can be used in the actual product-pair reduction.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- A contractible topological base contracts to any specified point, with the homotopy directed from the constant map to the identity.
Source: Hatcher, Algebraic Topology, §0, contractible spaces and homotopies. -/
def i1_contractibleBaseContraction {B : Type} [TopologicalSpace B] [ContractibleSpace B]
    (b : B) : ContinuousMap.Homotopy (ContinuousMap.const B b) (ContinuousMap.id B) := by
  let p := Classical.choose (id_nullhomotopic B)
  let H : ContinuousMap.Homotopy (ContinuousMap.id B) (ContinuousMap.const B p) :=
    Classical.choice (Classical.choose_spec (id_nullhomotopic B))
  let K : ContinuousMap.Homotopy (ContinuousMap.const B b) (ContinuousMap.const B p) := {
    toFun := fun t => H (t.1, b)
    continuous_toFun := H.continuous.comp (continuous_fst.prodMk continuous_const)
    map_zero_left := fun _ => H.map_zero_left b
    map_one_left := fun _ => H.map_one_left b }
  exact K.trans H.symm

end HodgeLean.Foundations.BundleThom
