import HodgeLean.Foundations.BundleThom.ContractibleFactorProjectionHelpers

/-! # Actual second-factor product subsets

HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicTopology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.BundleThom

/-- A subset condition on the second coordinate gives the actual product with that subspace.
Source: Hatcher, Algebraic Topology, §0, product and subspace topology. -/
def i1_productSecondSubsetHomeomorph (B Y : Type) [TopologicalSpace B]
    [TopologicalSpace Y] (S : Set Y) :
    {p : B × Y | p.2 ∈ S} ≃ₜ (B × S) where
  toFun := fun p => (p.1.1, ⟨p.1.2, p.2⟩)
  invFun := fun p => ⟨(p.1, p.2.1), p.2.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- First projection from an actual second-coordinate subset is a rational chain quasi-isomorphism when that subspace is contractible.
Source: Hatcher, Algebraic Topology, §2.1, homotopy invariance for product subspaces. -/
theorem i1_productSecondSubsetProjection_quasiIso (B Y : Type) [TopologicalSpace B]
    [TopologicalSpace Y] (S : Set Y) [ContractibleSpace S] :
    QuasiIso
      ((((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ))).map
        (TopCat.ofHom (⟨fun p : {p : B × Y | p.2 ∈ S} => p.1.1,
          continuous_fst.comp continuous_subtype_val⟩))) := by
  let F := (singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
  let e := TopCat.isoOfHomeo (X := TopCat.of {p : B × Y | p.2 ∈ S})
    (Y := TopCat.of (B × S)) (i1_productSecondSubsetHomeomorph B Y S)
  let p : TopCat.of (B × S) ⟶ TopCat.of B := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
  haveI : QuasiIso (F.map p) := i1_productContractibleProjection_quasiIso B S
  change QuasiIso (F.map (e.hom ≫ p))
  rw [F.map_comp]
  infer_instance

end HodgeLean.Foundations.BundleThom
