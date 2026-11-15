import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveChartOverlap

/-! # Restriction relations for normalized Rees ratios -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RamifiedNormalization.StageFour
namespace HodgeLean.Foundations.Program.G32Native

/-- The two Rees equations force reciprocal ratios before restriction to
 the exceptional divisor. Cancellation takes place in the ambient overlap. -/
theorem pairedC3_rees_overlap_reciprocal {B : Type*} [CommRing B]
    (u v s t : B) (hu : IsRegular u)
    (hs : u = s * v) (ht : v = t * u) : s * t = 1 := by
  apply hu.right
  calc
    (s * t) * u = s * (t * u) := mul_assoc _ _ _
    _ = s * v := by rw [← ht]
    _ = u := hs.symm
    _ = 1 * u := (one_mul _).symm

/-- A change of branch equations determines the change of the actual
Rees parameter by ambient cancellation. -/
theorem pairedC3_rees_overlap_generator_change {B : Type*} [CommRing B]
    (u v t t' : B) (a b : Bˣ) (hu : IsRegular u)
    (ht : v = t * u) (ht' : (b : B) * v = t' * ((a : B) * u)) :
    t' = (b : B) * ↑a⁻¹ * t := by
  have h : t' * (a : B) = (b : B) * t := by
    apply hu.right
    calc
      (t' * ↑a) * u = t' * (↑a * u) := mul_assoc _ _ _
      _ = ↑b * v := ht'.symm
      _ = (↑b * t) * u := by rw [ht, mul_assoc]
  calc
    t' = (t' * (a : B)) * ↑a⁻¹ := by rw [mul_assoc, Units.mul_inv, mul_one]
    _ = ((b : B) * t) * ↑a⁻¹ := by rw [h]
    _ = (b : B) * ↑a⁻¹ * t := by ring

/-- Slice regularity determines the change of the normalization coefficient
modulo the slice ideal, even when neither ambient lift is a unit. -/
theorem pairedC3_slice_overlap_coefficient {B : Type*} [CommRing B]
    (I : Ideal B) (u v α α' : B) (a b : Bˣ)
    (hu : IsRegular (Ideal.Quotient.mk I u))
    (hα : v - α * u ∈ I)
    (hα' : (b : B) * v - α' * ((a : B) * u) ∈ I) :
    Ideal.Quotient.mk I α' =
      Ideal.Quotient.mk I ((b : B) * ↑a⁻¹ * α) := by
  let q := Ideal.Quotient.mk I
  have ht : q v = q α * q u := by
    apply sub_eq_zero.mp
    rw [← map_mul, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hα
  have ht' : q (b : B) * q v = q α' * (q (a : B) * q u) := by
    apply sub_eq_zero.mp
    rw [← map_mul, ← map_mul, ← map_mul, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hα'
  have h := pairedC3_rees_overlap_generator_change (q u) (q v) (q α) (q α')
    (Units.map q.toMonoidHom a) (Units.map q.toMonoidHom b) hu ht ht'
  change q α' = q (b : B) * q (↑a⁻¹ : B) * q α at h
  simpa only [q, map_mul] using h

/-- The actual ambient Rees equations imply agreement of the normalized
projective chart maps after any restriction to a reduced finite-type ring.
The reciprocal identity is derived before the exceptional quotient, where
the branch generators themselves vanish. -/
theorem pairedC3_projective_overlap_of_rees_equations
    {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ B]
    [IsReduced (Spec (CommRingCat.of B))]
    [LocallyOfFiniteType (ComplexPoint.affineSpecStructureMap B)]
    [IsSeparated projectiveLine.hom] [LocallyOfFiniteType projectiveLine.hom]
    (f : A →+* B) (u v s t : A) (hu : IsRegular u)
    (hs : u = s * v) (ht : v = t * u) (α : Bˣ) :
    projectiveLineChart 1 ((↑α⁻¹ : B) * f t) =
      projectiveLineChart 0 ((↑α : B) * f s) := by
  apply pairedC3_projective_normalized_overlap
  rw [← map_mul, pairedC3_rees_overlap_reciprocal u v s t hu hs ht, map_one]

#print axioms pairedC3_rees_overlap_reciprocal
#print axioms pairedC3_rees_overlap_generator_change
#print axioms pairedC3_slice_overlap_coefficient
#print axioms pairedC3_projective_overlap_of_rees_equations
end HodgeLean.Foundations.Program.G32Native
