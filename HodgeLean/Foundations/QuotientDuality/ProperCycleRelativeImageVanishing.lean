import HodgeLean.Foundations.QuotientDuality.ProperCycleFiniteLocalClasses

/-! # Actual relative homology maps whose image lies in the target subspace -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- If the whole actual image lies in the relative target subspace, the induced relative homology map vanishes.
Source: Hatcher, Algebraic Topology, section 2.1, relative homology and functoriality.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_homology_zero_of_image_in_subspace
    {X Y : TopCat.{0}} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (hf : ∀ x ∈ A, f x ∈ B) (hfull : ∀ x : X, f x ∈ B)
    (n : ℕ) (c : RelativeHomology ℚ (TopPair.ofSubset (X := X) A) n) :
    relativeHomologyMap ℚ n (TopPair.ofSubsetHom f hf) c = 0 := by
  let a : TopPair.ofSubset (X := X) A ⟶ TopPair.ofSubset (X := X) (∅ : Set X)ᶜ :=
    TopPair.ofSubsetHom (𝟙 X) (fun _ _ => fun h => h)
  let b : TopPair.ofSubset (X := X) (∅ : Set X)ᶜ ⟶ TopPair.ofSubset (X := Y) B :=
    TopPair.ofSubsetHom f (fun x _ => hfull x)
  have hab : a ≫ b = TopPair.ofSubsetHom f hf := by
    ext x : 2 <;> rfl
  have hzero : relativeHomologyMap ℚ n a c = 0 := by
    let := ModuleCat.subsingleton_of_isZero (b6m_relativeHomology_empty_support_isZero ℚ X n)
    exact Subsingleton.elim _ _
  rw [← hab, relativeHomologyMap_comp, LinearMap.comp_apply, hzero, map_zero]

end HodgeLean.Foundations.QuotientDuality
