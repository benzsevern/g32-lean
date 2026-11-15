import HodgeLean.Foundations.Program.SchoenTowerI2aSelectedCartierNeighborhood
import HodgeLean.Foundations.Program.SchoenTowerI2aPairReesUniqueness
import HodgeLean.Foundations.Program.SchoenTowerI2aReesCartierImage

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A Cartier coefficient chart receiving the actual Rees spectrum has a
principal neighborhood whose selected Rees comparison is a retraction over the
original coefficient ring.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13, standard charts. -/
theorem s2v_i2a_selected_rees_coefficient_retraction
    (R S : Type) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    (u : R →+* S) (x y : R) (hx : x ≠ 0)
    (e : (Ideal.span {u x, u y} : Ideal S) ≃ₗ[S] S)
    (φ : S →+* s2t_reesChart (Ideal.span {x, y}) x)
    (hφ : φ.comp u = algebraMap R _) :
    let C := s2t_reesChart (Ideal.span {x, y}) x
    ∃ s : S, s ≠ 0 ∧ IsUnit (φ s) ∧
      ∃ η : Localization.Away s →+* C, ∃ ψ : C →+* Localization.Away s,
        η.comp (algebraMap S _) = φ ∧
        ψ.comp (algebraMap R C) = (algebraMap S _).comp u ∧
        η.comp ψ = RingHom.id C := by
  intro C
  letI : IsDomain (Localization.Away x) := Localization.Away.isDomain hx
  have hinj : Function.Injective (algebraMap R (Localization.Away x)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hx)
  have hxc : algebraMap R C x ≠ 0 := by
    intro H
    exact hx (hinj ((congrArg Subtype.val H).trans (map_zero _).symm))
  have hφx : φ (u x) ≠ 0 := by
    simpa only [← RingHom.comp_apply, hφ] using hxc
  have himage : (Ideal.span {u x, u y}).map φ = Ideal.span {φ (u x)} := by
    have hp : (Ideal.span {x, y}).map u = Ideal.span {u x, u y} := by
      rw [Ideal.map_span, Set.image_pair]
    rw [← hp, Ideal.map_map, hφ]
    rw [s2t_reesChart_image R (Ideal.span {x, y}) x (Ideal.subset_span (by simp))]
    rw [show φ (u x) = algebraMap R C x from RingHom.congr_fun hφ x]
  obtain ⟨s, hs, hsu, hsx, ⟨t, ht⟩, η, hη⟩ :=
    s2v_i2a_selected_cartier_pair_neighborhood S C φ (u x) (u y) e hφx himage
  letI : IsDomain (Localization.Away s) := Localization.Away.isDomain hs
  obtain ⟨ψ, hψ, _⟩ := s2v_i2a_pair_rees_lift_to_domain R (Localization.Away s)
    ((algebraMap S _).comp u) x y t hsx ht
  refine ⟨s, hs, hsu, η, ψ, hη, hψ.1, ?_⟩
  apply s2v_i2a_pair_rees_map_unique R C (algebraMap R C) x y hxc
  · rw [RingHom.comp_assoc, hψ.1, ← RingHom.comp_assoc, hη, hφ]
  · rfl

end HodgeLean.Foundations.Program
