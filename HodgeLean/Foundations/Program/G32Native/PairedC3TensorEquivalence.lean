import HodgeLean.Foundations.Program.G32Native.PairedC3DualTensorIso

/-! # Tensoring with an invertible native line as an equivalence -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules

/-- Tensoring by the native invertible line has tensoring by its actual
dual as inverse; both comparisons use the original evaluation. -/
def pairedC3TensorRightEquivalence {X : Scheme.{0}} {L : X.Modules}
    (hL : IsInvertible L) : X.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (tensorRight L) (tensorRight L.dual)
    ((tensorRightTensor L L.dual).symm ≪≫
      (tensoringRight X.Modules).mapIso (pairedC3DualTensorIso hL) ≪≫
      rightUnitorNatIso X.Modules).symm
    ((tensorRightTensor L.dual L).symm ≪≫
      (tensoringRight X.Modules).mapIso
        ((β_ L.dual L) ≪≫ pairedC3DualTensorIso hL) ≪≫
      rightUnitorNatIso X.Modules)

/-- A section of the original tensored projection descends to a section
of the original projection, without quasicoherence assumptions. -/
theorem paired_c3_section_of_invertible_twist {X : Scheme.{0}} {L M N : X.Modules}
    (hL : IsInvertible L) (g : M ⟶ N)
    (s : N ⊗ L ⟶ M ⊗ L) (hs : s ≫ (g ▷ L) = 𝟙 _) :
    ∃ v : N ⟶ M, v ≫ g = 𝟙 _ := by
  let e := pairedC3TensorRightEquivalence hL
  obtain ⟨v, hv⟩ := e.functor.map_surjective s
  refine ⟨v, ?_⟩
  apply e.functor.map_injective
  rw [e.functor.map_comp, hv, e.functor.map_id]
  exact hs

#print axioms pairedC3TensorRightEquivalence
#print axioms paired_c3_section_of_invertible_twist
end HodgeLean.Foundations.Program.G32Native
