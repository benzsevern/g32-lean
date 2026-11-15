import HodgeLean.Foundations.Program.G32Native.TypeIIIDefiniteQuaternion

noncomputable section
open scoped Quaternion
namespace HodgeLean.Foundations.Program.G32Native

/-- The reversed product with conjugation has the same scalar norm. -/
theorem typeIIIQuaternion_star_mul (b : ℚ) (q : ℍ[ℚ, -3, 0, b]) :
    star q * q = algebraMap ℚ _ (typeIIIQuaternionNorm b q) := by
  have hs : typeIIIQuaternionNorm b (star q) = typeIIIQuaternionNorm b q := by
    rcases q with ⟨r, i, j, k⟩
    simp [typeIIIQuaternionNorm, Star.star, QuaternionAlgebra.instStarQuaternionAlgebra]
  simpa only [star_star, hs] using typeIIIQuaternion_mul_star b (star q)

/-- Every nonzero quaternion in the negative-parameter presentation is a
unit, with inverse given by conjugation divided by the reduced norm. -/
theorem typeIIIQuaternion_isUnit (b : ℚ) (hb : b < 0)
    (q : ℍ[ℚ, -3, 0, b]) (hq : q ≠ 0) : IsUnit q := by
  have hn : typeIIIQuaternionNorm b q ≠ 0 :=
    fun h => hq ((typeIIIQuaternionNorm_eq_zero b hb q).1 h)
  refine ⟨⟨q, (typeIIIQuaternionNorm b q)⁻¹ • star q, ?_, ?_⟩, rfl⟩
  · rw [Algebra.mul_smul_comm, typeIIIQuaternion_mul_star,
      Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ hn, one_smul]
  · rw [smul_mul_assoc, typeIIIQuaternion_star_mul,
      Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ hn, one_smul]

/-- The specified totally definite quaternion presentation as a division ring. -/
abbrev typeIIIQuaternionDivisionRing (b : ℚ) (hb : b < 0) :
    DivisionRing ℍ[ℚ, -3, 0, b] :=
  DivisionRing.ofIsUnitOrEqZero fun q => by
    by_cases hq : q = 0
    · exact Or.inr hq
    · exact Or.inl (typeIIIQuaternion_isUnit b hb q hq)

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIQuaternion_star_mul
#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIQuaternion_isUnit
#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIQuaternionDivisionRing
