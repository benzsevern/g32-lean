import HodgeLean.Adapters.NormalConeB4aGysinEtaleLength

/-! # Parameter quotient lengths under étale local changes -/

noncomputable section
namespace HodgeLean.Adapters

/-- Flat unramified local extensions preserve the exact length of every parameter
quotient, measured over its own quotient ring. -/
theorem a3b4a_gysin_quotient_length_eq_of_flat_unramified
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    [Module.Flat A B] [Algebra.FormallyUnramified A B] (I : Ideal A) :
    Module.length (B ⧸ I.map (algebraMap A B)) (B ⧸ I.map (algebraMap A B)) =
      Module.length (A ⧸ I) (A ⧸ I) := by
  have hr : Module.length B (B ⧸ IsLocalRing.maximalIdeal B) = 1 := by
    change Module.length B (IsLocalRing.ResidueField B) = 1
    rw [Module.length_eq_of_surjective (IsLocalRing.residue_surjective (R := B))]
    exact Module.length_eq_one _ _
  have h := IsLocalRing.length_baseChange A B (A ⧸ I)
  rw [Algebra.FormallyUnramified.map_maximalIdeal, hr, mul_one,
    ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.length_eq,
    Module.length_eq_of_surjective (R := B ⧸ I.map (algebraMap A B))
      Ideal.Quotient.mk_surjective,
    Module.length_eq_of_surjective (R := A ⧸ I) Ideal.Quotient.mk_surjective] at h
  exact h

end HodgeLean.Adapters
