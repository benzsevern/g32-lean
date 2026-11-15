import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Target neighbourhoods from source charts of a finite morphism -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A finite map carries the complement of an etale source open to a
closed subset; avoiding that image supplies an etale target restriction. -/
theorem s2e_c1_etale_neighbourhood_of_source_open
    {X Y P : Scheme} (f : X ⟶ Y) [IsFinite f] (g : P ⟶ Y)
    (O : X.Opens) [Etale (O.ι ≫ f)]
    (hO : ∀ x, f x ∈ Set.range g → x ∈ O) :
    ∃ U : Y.Opens, Set.range g ⊆ U ∧ Etale (f ∣_ U) := by
  let U : Y.Opens := ⟨(f '' (O : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ O.isOpen.isClosed_compl).isOpen_compl⟩
  have hsub : f ⁻¹ᵁ U ≤ O := by
    intro x hx
    by_contra hn
    exact hx ⟨x, hn, rfl⟩
  haveI : Etale ((f ⁻¹ᵁ U).ι ≫ f) := by
    rw [← Scheme.homOfLE_ι X hsub, Category.assoc]
    infer_instance
  haveI : Etale ((f ∣_ U) ≫ U.ι) := by
    rw [morphismRestrict_ι]
    infer_instance
  refine ⟨U, ?_, Etale.of_comp (f ∣_ U) U.ι⟩
  intro y hy
  rintro ⟨x, hx, rfl⟩
  exact hx (hO x hy)

end HodgeLean.Foundations.Program
