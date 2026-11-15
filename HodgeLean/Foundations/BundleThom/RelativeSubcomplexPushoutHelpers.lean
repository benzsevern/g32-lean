import HodgeLean.Foundations.BundleThom.RelativeSubcomplexChainHelpers
import Mathlib.CategoryTheory.Limits.Comma

/-! # Pushouts of actual relative subcomplex chain diagrams

The fixed subspace is retained in the left side of each chain arrow before taking its cokernel.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- Actual relative chain arrows carry subcomplex intersections and unions to a pushout of arrows.
Source: Hatcher, Algebraic Topology, §2.2, relative Mayer–Vietoris chain construction. -/
theorem i1_relativeSubcomplexArrows_isPushout (X : SSet) (Z U V : X.Subcomplex) :
    IsPushout
      ((i1_relativeSubcomplexArrowFunctor X Z).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
      ((i1_relativeSubcomplexArrowFunctor X Z).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
      ((i1_relativeSubcomplexArrowFunctor X Z).map (homOfLE (le_sup_left : U ≤ U ⊔ V)))
      ((i1_relativeSubcomplexArrowFunctor X Z).map (homOfLE (le_sup_right : V ≤ U ⊔ V))) := by
  have hs : SSet.Subcomplex.BicartSq ((U ⊓ V) ⊓ Z) (U ⊓ Z) (V ⊓ Z) ((U ⊔ V) ⊓ Z) := {
    sup_eq := by
      ext n x
      change ((x ∈ U.obj n ∧ x ∈ Z.obj n) ∨ (x ∈ V.obj n ∧ x ∈ Z.obj n)) ↔
        ((x ∈ U.obj n ∨ x ∈ V.obj n) ∧ x ∈ Z.obj n)
      tauto
    inf_eq := by
      ext n x
      change ((x ∈ U.obj n ∧ x ∈ Z.obj n) ∧ (x ∈ V.obj n ∧ x ∈ Z.obj n)) ↔
        ((x ∈ U.obj n ∧ x ∈ V.obj n) ∧ x ∈ Z.obj n)
      tauto }
  have hw :
      (i1_relativeSubcomplexArrowFunctor X Z).map (homOfLE (inf_le_left : U ⊓ V ≤ U)) ≫
        (i1_relativeSubcomplexArrowFunctor X Z).map (homOfLE (le_sup_left : U ≤ U ⊔ V)) =
      (i1_relativeSubcomplexArrowFunctor X Z).map (homOfLE (inf_le_right : U ⊓ V ≤ V)) ≫
        (i1_relativeSubcomplexArrowFunctor X Z).map (homOfLE (le_sup_right : V ≤ U ⊔ V)) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  refine { w := hw, isColimit' := ⟨?_⟩ }
  apply Comma.fstSndJointlyReflectColimit
  · exact (PushoutCocone.isColimitMapCoconeEquiv _ _).2
      (i1_subcomplexChains_bicart_isPushout X _ _ _ _ hs).isColimit
  · exact (PushoutCocone.isColimitMapCoconeEquiv _ _).2
      (i1_subcomplexChains_isPushout X U V).isColimit

/-- Actual relative rational chains carry intersection–union squares to pushouts.
Source: Hatcher, Algebraic Topology, §2.2, relative Mayer–Vietoris chain construction. -/
theorem i1_relativeSubcomplexChains_isPushout (X : SSet) (Z U V : X.Subcomplex) :
    IsPushout
      ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
      ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
      ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE (le_sup_left : U ≤ U ⊔ V)))
      ((i1_relativeSubcomplexChainFunctor X Z).map (homOfLE (le_sup_right : V ≤ U ⊔ V))) := by
  letI := (i1_cokernelZeroSourceAdjunction (ChainComplex (ModuleCat ℚ) ℕ)).isLeftAdjoint
  exact (coker (C := ChainComplex (ModuleCat ℚ) ℕ)).map_isPushout
    (i1_relativeSubcomplexArrows_isPushout X Z U V)

end HodgeLean.Foundations.BundleThom
