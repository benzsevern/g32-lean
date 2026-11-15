import HodgeLean.Adapters.NormalConeB4aGysinFibreLength
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Local fibre length and vector-space dimension

Over an algebraically closed field a finite local algebra has residue degree one.
Restriction of scalars therefore identifies its self-length with its dimension
over the ground field, without discarding nilpotents.
-/

noncomputable section
namespace HodgeLean.Adapters

/-- The length of a finite local algebra over an algebraically closed field
is its vector-space dimension. -/
theorem a3b4a_gysin_local_length_eq_finrank
    {k A : Type*} [Field k] [IsAlgClosed k] [CommRing A] [IsLocalRing A]
    [Algebra k A] [Module.Finite k A] :
    Module.length A A = (Module.finrank k A : ℕ∞) := by
  have hr : Module.length (IsLocalRing.ResidueField k) (IsLocalRing.ResidueField A) = 1 := by
    rw [← Module.length_eq_of_surjective (M := IsLocalRing.ResidueField A)
      (IsLocalRing.residue_surjective (R := k))]
    rw [Module.length_eq_of_surjective
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)
        (K := IsLocalRing.ResidueField A)).2]
    exact Module.length_eq_one _ _
  have h := IsLocalRing.length_restrictScalars k A A
  rw [hr, mul_one, Module.length_eq_finrank] at h
  exact h.symm

end HodgeLean.Adapters
