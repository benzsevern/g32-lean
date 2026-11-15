import HodgeLean.Foundations.Program.SchoenTowerI2aSelectedReesRetraction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The selected Cartier denominator persists when only a restricted actual
Rees chart maps into the coefficient neighborhood. Both comparison maps retain
the specified restriction of the Rees algebra.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13, standard charts. -/
theorem s2v_i2a_selected_rees_coefficient_restriction
    (R S T : Type) [CommRing R] [CommRing S] [IsDomain S] [CommRing T] [IsDomain T]
    (u : R →+* S) (x y : R)
    (e : (Ideal.span {u x, u y} : Ideal S) ≃ₗ[S] S)
    (v : s2t_reesChart (Ideal.span {x, y}) x →+* T) (φ : S →+* T)
    (hφ : φ.comp u = v.comp (algebraMap R _))
    (hx : v (algebraMap R _ x) ≠ 0) :
    let C := s2t_reesChart (Ideal.span {x, y}) x
    ∃ s : S, s ≠ 0 ∧ IsUnit (φ s) ∧
      ∃ η : Localization.Away s →+* T, ∃ ψ : C →+* Localization.Away s,
        η.comp (algebraMap S _) = φ ∧
        ψ.comp (algebraMap R C) = (algebraMap S _).comp u ∧
        η.comp ψ = v := by
  intro C
  have hφx : φ (u x) ≠ 0 := by
    simpa only [← RingHom.comp_apply, hφ] using hx
  have himage : (Ideal.span {u x, u y}).map φ = Ideal.span {φ (u x)} := by
    have hp : (Ideal.span {x, y}).map u = Ideal.span {u x, u y} := by
      rw [Ideal.map_span, Set.image_pair]
    rw [← hp, Ideal.map_map, hφ, ← Ideal.map_map,
      s2t_reesChart_image R (Ideal.span {x, y}) x (Ideal.subset_span (by simp)),
      Ideal.map_span, Set.image_singleton]
    rw [show φ (u x) = v (algebraMap R C x) from RingHom.congr_fun hφ x]
  obtain ⟨s, hs, hsu, hsx, ⟨t, ht⟩, η, hη⟩ :=
    s2v_i2a_selected_cartier_pair_neighborhood S T φ (u x) (u y) e hφx himage
  letI : IsDomain (Localization.Away s) := Localization.Away.isDomain hs
  obtain ⟨ψ, hψ, _⟩ := s2v_i2a_pair_rees_lift_to_domain R (Localization.Away s)
    ((algebraMap S _).comp u) x y t hsx ht
  refine ⟨s, hs, hsu, η, ψ, hη, hψ.1, ?_⟩
  apply s2v_i2a_pair_rees_map_unique R T (v.comp (algebraMap R C)) x y hx
  · rw [RingHom.comp_assoc, hψ.1, ← RingHom.comp_assoc, hη, hφ]
  · rfl

end HodgeLean.Foundations.Program
