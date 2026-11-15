import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-! Generation of a fraction field from generators of its integral algebra. -/
noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.QuotientDuality

theorem fractionField_adjoin_eq_top
    {R A K F : Type*} [CommRing R] [CommRing A] [IsDomain A] [Field K] [Field F]
    [Algebra R A] [Algebra A F] [IsFractionRing A F]
    [Algebra R K] [Algebra K F] [Algebra R F]
    [IsScalarTower R A F] [IsScalarTower R K F]
    (S : Set A) (hS : Algebra.adjoin R S = ⊤) :
    IntermediateField.adjoin K (algebraMap A F '' S) = ⊤ := by
  let E := IntermediateField.adjoin K (algebraMap A F '' S)
  let f : A →ₐ[R] F := IsScalarTower.toAlgHom R A F
  have hle : Algebra.adjoin R S ≤
      (E.toSubalgebra.restrictScalars R).comap f := by
    apply Algebra.adjoin_le_iff.mpr
    intro a ha
    exact IntermediateField.subset_adjoin K _ ⟨a, ha, rfl⟩
  have hmem (a : A) : algebraMap A F a ∈ E := by
    exact hle (hS ▸ Algebra.mem_top)
  apply top_unique
  intro z _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective A z
  exact E.div_mem (hmem a) (hmem b)

#print axioms fractionField_adjoin_eq_top
end HodgeLean.Foundations.QuotientDuality
