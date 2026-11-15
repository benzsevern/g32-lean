import HodgeLean.Foundations.Program.SchoenTowerI2aPairReesLift

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Over an integral target with nonzero denominator, the actual paired Rees
chart map is determined by its coefficient map alone.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13, affine blowup charts. -/
theorem s2v_i2a_pair_rees_map_unique
    (R S : Type) [CommRing R] [CommRing S] [IsDomain S]
    (φ : R →+* S) (x y : R) (hx : φ x ≠ 0)
    (ψ₁ ψ₂ : s2t_reesChart (Ideal.span {x, y}) x →+* S)
    (h₁ : ψ₁.comp (algebraMap R _) = φ)
    (h₂ : ψ₂.comp (algebraMap R _) = φ) : ψ₁ = ψ₂ := by
  obtain ⟨t, ht, hyt, hsur⟩ := s2t_pairChart_coordinate R x y
  have hratio (ψ : s2t_reesChart (Ideal.span {x, y}) x →+* S)
      (hψ : ψ.comp (algebraMap R _) = φ) : φ y = φ x * ψ t := by
    have H := congrArg ψ hyt
    rw [map_mul] at H
    have hb (r : R) : ψ (algebraMap R _ r) = φ r := RingHom.congr_fun hψ r
    rwa [hb, hb] at H
  have hteq : ψ₁ t = ψ₂ t := mul_left_cancel₀ hx
    ((hratio ψ₁ h₁).symm.trans (hratio ψ₂ h₂))
  have H : ψ₁.comp (Polynomial.aeval (R := R) t).toRingHom =
      ψ₂.comp (Polynomial.aeval (R := R) t).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro r
      simpa using (RingHom.congr_fun h₁ r).trans (RingHom.congr_fun h₂ r).symm
    · simpa using hteq
  apply RingHom.ext
  intro z
  obtain ⟨p, rfl⟩ := hsur z
  exact RingHom.congr_fun H p

end HodgeLean.Foundations.Program
