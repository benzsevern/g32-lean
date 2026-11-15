import Mathlib.AlgebraicGeometry.Properties

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every point above a specified open coefficient spectrum has an integral
spectrum neighborhood whose actual coefficient map gives the commuting square.
Source: Mathlib, `Scheme.exists_affine_mem_range_and_range_subset`,
`IsOpenImmersion.lift` and `Spec.map_surjective`. -/
theorem s2v_i2a_compatible_spectrum_neighborhood
    {X Y : Scheme.{0}} [IsIntegral X] (g : X ⟶ Y)
    (S : Type) [CommRing S] (v : Spec (CommRingCat.of S) ⟶ Y) [IsOpenImmersion v]
    (q : X) (hq : g q ∈ Set.range v) :
    ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T)
      (w : Spec (CommRingCat.of T) ⟶ X) (φ : S →+* T),
      IsOpenImmersion w ∧ q ∈ Set.range w ∧
        Spec.map (CommRingCat.ofHom φ) ≫ v = w ≫ g := by
  obtain ⟨T, w, hw, hq, hrange⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (U := g ⁻¹ᵁ v.opensRange) hq
  letI : IsOpenImmersion w := hw
  letI : Nonempty (Spec T) := by obtain ⟨t, _⟩ := hq; exact ⟨t⟩
  haveI : IsIntegral (Spec T) := isIntegral_of_isOpenImmersion w
  haveI : IsDomain T := (affine_isIntegral_iff T).mp inferInstance
  have hr : Set.range (w ≫ g) ⊆ Set.range v := by
    rintro _ ⟨t, rfl⟩
    exact hrange ⟨t, rfl⟩
  let a := IsOpenImmersion.lift v (w ≫ g) hr
  obtain ⟨φ, hφ⟩ := Spec.map_surjective a
  refine ⟨T, inferInstance, inferInstance, w, φ.hom, hw, hq, ?_⟩
  change Spec.map φ ≫ v = w ≫ g
  rw [hφ]
  exact IsOpenImmersion.lift_fac _ _ _

end HodgeLean.Foundations.Program
