import HodgeLean.Foundations.Program.SchoenTowerI2aPairReesLift
import Mathlib.RingTheory.LocalRing.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A free paired image ideal supplies one nonzero generator and two
coefficients generating the unit ideal.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13, local generators
of an invertible image ideal. -/
theorem s2v_i2a_cartier_pair_coefficients
    (R : Type) [CommRing R] [IsDomain R] (x y : R)
    (e : (Ideal.span {x, y} : Ideal R) ≃ₗ[R] R) :
    ∃ g a b c d : R, g ≠ 0 ∧ x = a * g ∧ y = b * g ∧ c * a + d * b = 1 := by
  let I : Ideal R := Ideal.span {x, y}
  let g : I := e.symm 1
  let a := e ⟨x, Ideal.subset_span (by simp)⟩
  let b := e ⟨y, Ideal.subset_span (by simp)⟩
  have hg : (g : R) ≠ 0 := by
    intro h
    have h0 : g = 0 := Subtype.ext h
    have H := congrArg e h0
    simpa [g] using H
  have hz (z : I) : z = e z • g := by
    apply e.injective
    simp [g]
  have hx : x = a * (g : R) := congrArg Subtype.val (hz ⟨x, Ideal.subset_span (by simp)⟩)
  have hy : y = b * (g : R) := congrArg Subtype.val (hz ⟨y, Ideal.subset_span (by simp)⟩)
  obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.mp g.property
  refine ⟨g, a, b, c, d, hg, hx, hy, ?_⟩
  apply mul_right_cancel₀ hg
  rw [one_mul]
  calc
    (c * a + d * b) * (g : R) = c * x + d * y := by rw [hx, hy]; ring
    _ = g := hcd

/-- At a local integral coefficient ring, a paired Cartier image ideal chooses
one of its actual two generators as a nonzero denominator.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13;
Mathlib, `IsLocalRing.isUnit_or_isUnit_of_add_one`. -/
theorem s2v_i2a_local_cartier_pair_ratio
    (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (x y : R)
    (e : (Ideal.span {x, y} : Ideal R) ≃ₗ[R] R) :
    (x ≠ 0 ∧ ∃ t : R, y = x * t) ∨ (y ≠ 0 ∧ ∃ t : R, x = y * t) := by
  obtain ⟨g, a, b, c, d, hg, hx, hy, hcd⟩ := s2v_i2a_cartier_pair_coefficients R x y e
  have hratio (a b : R) (ha : IsUnit a) :
      a * g ≠ 0 ∧ ∃ t : R, b * g = (a * g) * t := by
    obtain ⟨v, rfl⟩ := ha
    refine ⟨mul_ne_zero (Units.ne_zero v) hg, ↑v⁻¹ * b, ?_⟩
    calc
      b * g = (↑v * ↑v⁻¹ : R) * (b * g) := by simp
      _ = (↑v * g) * (↑v⁻¹ * b) := by ring
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hcd with ha | hb
  · left
    rw [hx, hy]
    exact hratio a b (isUnit_of_mul_isUnit_right ha)
  · right
    rw [hx, hy]
    exact hratio b a (isUnit_of_mul_isUnit_right hb)

end HodgeLean.Foundations.Program
