import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Invariant affine neighborhoods for finite maps

Implication from a finite scheme map and endomorphisms over its target to
an invariant affine neighborhood with the actual restricted finite map.
The invariant ring and parameter constructions remain separate.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A finite map has an affine inverse-image neighborhood invariant under
all specified endomorphisms over its target.
Source: Hartshorne, Algebraic Geometry, II.3, finite morphisms and affine restriction. -/
theorem s2v_l1a_invariant_affine_neighborhood
    {X Y : Scheme} {T : Type*} (f : X ⟶ Y) [IsFinite f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f) (x : X) :
    ∃ U : Y.affineOpens, f x ∈ U.1 ∧ IsAffine (f ⁻¹ᵁ U.1).toScheme ∧
      IsFinite (f ∣_ U.1) ∧
      ∃ ρ : T → ((f ⁻¹ᵁ U.1).toScheme ⟶ (f ⁻¹ᵁ U.1).toScheme),
        (∀ t, ρ t ≫ (f ⁻¹ᵁ U.1).ι = (f ⁻¹ᵁ U.1).ι ≫ a t) ∧
        (∀ t, ρ t ≫ (f ∣_ U.1) = f ∣_ U.1) := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top (f x))
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have hstable (t : T) : f ⁻¹ᵁ U ≤ (a t) ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ha t]
  let ρ (t : T) := (a t).resLE (f ⁻¹ᵁ U) (f ⁻¹ᵁ U) (hstable t)
  refine ⟨⟨U, hU⟩, hx, hV, inferInstance, ρ, ?_, ?_⟩
  · intro t
    exact Scheme.Hom.resLE_comp_ι (a t) (hstable t)
  · intro t
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, ha t]

end HodgeLean.Foundations.Program
