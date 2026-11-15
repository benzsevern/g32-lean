import HodgeLean.Foundations.Program.SchoenTowerI2aCartierPairNeighborhood

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- If a specified branch generates the nonzero image of a Cartier pair, one
principal neighborhood makes that same branch a generator and contains the
entire image of the coefficient map.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13;
Mathlib, `IsLocalization.Away.lift`. -/
theorem s2v_i2a_selected_cartier_pair_neighborhood
    (R S : Type) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    (φ : R →+* S) (x y : R)
    (e : (Ideal.span {x, y} : Ideal R) ≃ₗ[R] R)
    (hx : φ x ≠ 0) (himage : (Ideal.span {x, y}).map φ = Ideal.span {φ x}) :
    ∃ s : R, s ≠ 0 ∧ IsUnit (φ s) ∧
      algebraMap R (Localization.Away s) x ≠ 0 ∧
      (∃ t : Localization.Away s, algebraMap R _ y = algebraMap R _ x * t) ∧
      ∃ ψ : Localization.Away s →+* S, ψ.comp (algebraMap R _) = φ := by
  obtain ⟨g, a, b, c, d, hg, hxa, hyb, hcd⟩ :=
    s2v_i2a_cartier_pair_coefficients R x y e
  have hcomb : c * x + d * y = g := by
    rw [hxa, hyb]
    calc
      c * (a * g) + d * (b * g) = (c * a + d * b) * g := by ring
      _ = g := by rw [hcd, one_mul]
  have hgI : g ∈ (Ideal.span {x, y} : Ideal R) :=
    Ideal.mem_span_pair.mpr ⟨c, d, hcomb⟩
  have hgimage : φ g ∈ Ideal.span {φ x} := by
    rw [← himage]
    exact Ideal.mem_map_of_mem φ hgI
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hgimage
  have hφg : φ g ≠ 0 := by
    intro h
    apply hx
    rw [hxa, map_mul, h, mul_zero]
  have hunit : z * φ a = 1 := by
    apply mul_right_cancel₀ hφg
    rw [one_mul, mul_assoc, ← map_mul, ← hxa]
    exact hz
  have haunit : IsUnit (φ a) := isUnit_iff_exists_inv'.mpr ⟨z, hunit⟩
  have ha : a ≠ 0 := by
    intro h
    exact haunit.ne_zero (h ▸ φ.map_zero)
  let L := Localization.Away a
  have hinj : Function.Injective (algebraMap R L) :=
    IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  refine ⟨a, ha, haunit, ?_, ?_, IsLocalization.Away.lift a haunit,
    IsLocalization.Away.lift_comp a haunit⟩
  · intro H
    apply hx
    rw [hinj (H.trans (map_zero _).symm), map_zero]
  · refine ⟨IsLocalization.Away.invSelf a * algebraMap R L b, ?_⟩
    rw [hxa, hyb, map_mul, map_mul]
    calc
      algebraMap R L b * algebraMap R L g =
          (algebraMap R L a * IsLocalization.Away.invSelf a) *
            (algebraMap R L b * algebraMap R L g) := by
              rw [IsLocalization.Away.mul_invSelf, one_mul]
      _ = _ := by ring

end HodgeLean.Foundations.Program
