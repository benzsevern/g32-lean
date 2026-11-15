import HodgeLean.Adapters.NormalConeB4aGysinFiniteFlatLength

/-! # Exact lengths of finite local algebras with a residue-field section -/

noncomputable section
namespace HodgeLean.Adapters

/-- A finite local algebra with an augmentation to its base field has exact
self-length equal to its dimension, even when that field is not algebraically closed. -/
theorem a3b4a_gysin_augmented_local_length_eq_finrank
    {k A : Type*} [Field k] [CommRing A] [IsLocalRing A]
    [Algebra k A] [Module.Finite k A] (ε : A →ₐ[k] k) :
    Module.length A A = (Module.finrank k A : ℕ∞) := by
  have hε : Function.Surjective ε := fun x => ⟨algebraMap k A x, by simp⟩
  have hker := IsLocalRing.ker_eq_maximalIdeal ε.toRingHom hε
  let e : IsLocalRing.ResidueField A ≃ₐ[k] k :=
    (Ideal.quotientEquivAlgOfEq k hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hε)
  have hr : Module.length (IsLocalRing.ResidueField k) (IsLocalRing.ResidueField A) = 1 := by
    rw [← Module.length_eq_of_surjective (M := IsLocalRing.ResidueField A)
      (IsLocalRing.residue_surjective (R := k))]
    rw [Module.length_eq_finrank, e.toLinearEquiv.finrank_eq]
    simp
  have h := IsLocalRing.length_restrictScalars k A A
  rw [hr, mul_one, Module.length_eq_finrank] at h
  exact h.symm

/-- Finite flat local fibres with augmentations have equal exact lengths over
a domain, including a generic fibre whose residue field need not be algebraically closed. -/
theorem a3b4a_gysin_augmented_fibre_lengths_equal
    {R A : Type*} [CommRing R] [IsDomain R] [CommRing A]
    [Algebra R A] [Module.Finite R A] [Module.Flat R A]
    (p q : Ideal R) [p.IsPrime] [q.IsPrime]
    [IsLocalRing (p.Fiber A)] [IsLocalRing (q.Fiber A)]
    (εp : p.Fiber A →ₐ[p.ResidueField] p.ResidueField)
    (εq : q.Fiber A →ₐ[q.ResidueField] q.ResidueField) :
    Module.length (p.Fiber A) (p.Fiber A) = Module.length (q.Fiber A) (q.Fiber A) := by
  rw [a3b4a_gysin_augmented_local_length_eq_finrank εp,
    a3b4a_gysin_augmented_local_length_eq_finrank εq,
    p.finrank_fiber_eq_finrank, q.finrank_fiber_eq_finrank]

end HodgeLean.Adapters
