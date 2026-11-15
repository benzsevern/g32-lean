import HodgeLean.Foundations.Program.SchoenTowerI2aCartierPairCoefficients

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Every prime of an integral affine Cartier pair has a principal neighborhood
where one actual branch section divides the other with nonzero denominator.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13, the two standard charts. -/
theorem s2v_i2a_cartier_pair_ratio_neighborhood
    (R : Type) [CommRing R] [IsDomain R] (x y : R)
    (e : (Ideal.span {x, y} : Ideal R) ≃ₗ[R] R) (p : PrimeSpectrum R) :
    ∃ s : R, s ∉ p.asIdeal ∧ s ≠ 0 ∧
      ((algebraMap R (Localization.Away s) x ≠ 0 ∧
        ∃ t : Localization.Away s, algebraMap R _ y = algebraMap R _ x * t) ∨
       (algebraMap R (Localization.Away s) y ≠ 0 ∧
        ∃ t : Localization.Away s, algebraMap R _ x = algebraMap R _ y * t)) := by
  obtain ⟨g, a, b, c, d, hg, hx, hy, hcd⟩ := s2v_i2a_cartier_pair_coefficients R x y e
  have ratio (a b : R) (ha : a ≠ 0) :
      algebraMap R (Localization.Away a) (a * g) ≠ 0 ∧
      ∃ t : Localization.Away a,
        algebraMap R _ (b * g) = algebraMap R _ (a * g) * t := by
    let L := Localization.Away a
    have hinj : Function.Injective (algebraMap R L) :=
      IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
    refine ⟨fun H => mul_ne_zero ha hg (hinj (H.trans (map_zero _).symm)),
      IsLocalization.Away.invSelf a * algebraMap R L b, ?_⟩
    rw [map_mul, map_mul]
    calc
      algebraMap R L b * algebraMap R L g =
          (algebraMap R L a * IsLocalization.Away.invSelf a) *
            (algebraMap R L b * algebraMap R L g) := by
              rw [IsLocalization.Away.mul_invSelf, one_mul]
      _ = _ := by ring
  have hab : a ∉ p.asIdeal ∨ b ∉ p.asIdeal := by
    by_cases ha : a ∈ p.asIdeal
    · right
      intro hb
      exact p.isPrime.one_notMem (hcd ▸ p.asIdeal.add_mem
        (p.asIdeal.mul_mem_left c ha) (p.asIdeal.mul_mem_left d hb))
    · exact Or.inl ha
  rcases hab with ha | hb
  · have hane : a ≠ 0 := fun h => ha (h ▸ p.asIdeal.zero_mem)
    refine ⟨a, ha, hane, Or.inl ?_⟩
    rw [hx, hy]
    exact ratio a b hane
  · have hbne : b ≠ 0 := fun h => hb (h ▸ p.asIdeal.zero_mem)
    refine ⟨b, hb, hbne, Or.inr ?_⟩
    rw [hx, hy]
    exact ratio b a hbne

end HodgeLean.Foundations.Program
