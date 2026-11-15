import HodgeLean.Foundations.QuotientDuality.RetainedCycleExtendedCapDifferential
import HodgeLean.Foundations.QuotientDuality.RetainedCycleDerivedCapAction

noncomputable section
open CategoryTheory Limits CochainComplex.HomComplex
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- An explicit Hom-complex primitive gives a homotopy of the associated shifted morphism to zero. -/
theorem retained_shift_hom_nullhomotopic_of_boundary {K L : CochainComplex C ℤ}
    (m n : ℤ) (hmn : m + 1 = n) (z : Cocycle K L n)
    (β : Cochain K L m) (hβ : δ m n β = z.1) :
    Nonempty (Homotopy (Cocycle.equivHomShift.symm z) 0) := by
  simp only [Cocycle.equivHomShift_symm_apply]
  refine ⟨(Cochain.equivHomotopy _ _).symm ⟨n.negOnePow • β.rightShift n (-1) (by omega), ?_⟩⟩
  simp [β.δ_rightShift n (-1) 0 (by omega) n (zero_add n), hβ, smul_smul]

/-- A homogeneous primitive makes the associated shifted morphism zero after derived localization. -/
theorem retained_derived_shift_hom_zero_of_boundary
    {D : Type u} [Category.{v} D] [Abelian D] [HasDerivedCategory D]
    {K L : CochainComplex D ℤ} (m n : ℤ) (hmn : m + 1 = n)
    (z : Cocycle K L n) (β : Cochain K L m) (hβ : δ m n β = z.1) :
    DerivedCategory.Q.map (Cocycle.equivHomShift.symm z) = 0 := by
  obtain ⟨h⟩ := retained_shift_hom_nullhomotopic_of_boundary m n hmn z β hβ
  simpa only [Functor.map_zero] using DerivedCategory.Q_map_eq_of_homotopy D h

end HodgeLean.Foundations.QuotientDuality
