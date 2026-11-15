import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Basis.Defs

/-! # Cotangent bases over the coefficient field of an augmented local ring -/
noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native

/-- An augmentation to the coefficient field identifies that field with the
residue field of a local algebra.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 1,
local rings and residue fields. -/
theorem paired_c3_augmented_residue_surjective
    {k R : Type*} [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]
    (ε : R →ₐ[k] k) : Function.Surjective (algebraMap k (IsLocalRing.ResidueField R)) := by
  have hε : Function.Surjective ε := fun a => ⟨algebraMap k R a, ε.commutes a⟩
  have hker := IsLocalRing.ker_eq_maximalIdeal ε.toRingHom hε
  intro x
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  refine ⟨ε r, ?_⟩
  change IsLocalRing.residue R (algebraMap k R (ε r)) = IsLocalRing.residue R r
  apply Ideal.Quotient.eq.mpr
  rw [← hker]
  change ε (algebraMap k R (ε r) - r) = 0
  rw [map_sub, ε.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]

/-- A residue-field cotangent basis at an augmented local ring is the same
family of vectors as a basis over its coefficient field.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 1,
residue fields; Hartshorne, Algebraic Geometry, II.8, cotangent spaces. -/
def pairedC3AugmentedCotangentBasis
    {k R ι : Type*} [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]
    (ε : R →ₐ[k] k)
    (b : Module.Basis ι (IsLocalRing.ResidueField R) (IsLocalRing.maximalIdeal R).Cotangent) :
    Module.Basis ι k (IsLocalRing.maximalIdeal R).Cotangent := by
  let e : k ≃+* IsLocalRing.ResidueField R := RingEquiv.ofBijective
    (algebraMap k (IsLocalRing.ResidueField R))
    ⟨(algebraMap k (IsLocalRing.ResidueField R)).injective,
      paired_c3_augmented_residue_surjective ε⟩
  refine b.mapCoeffs e.symm ?_
  intro c x
  obtain ⟨a, rfl⟩ := e.surjective c
  rw [e.symm_apply_apply]
  change a • x = algebraMap k (IsLocalRing.ResidueField R) a • x
  change a • x = algebraMap k R a • x
  exact (IsScalarTower.algebraMap_smul R a x).symm

@[simp] theorem pairedC3AugmentedCotangentBasis_apply
    {k R ι : Type*} [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]
    (ε : R →ₐ[k] k)
    (b : Module.Basis ι (IsLocalRing.ResidueField R) (IsLocalRing.maximalIdeal R).Cotangent)
    (i : ι) : pairedC3AugmentedCotangentBasis ε b i = b i := by
  simp only [pairedC3AugmentedCotangentBasis, Module.Basis.mapCoeffs_apply]

#print axioms paired_c3_augmented_residue_surjective
#print axioms pairedC3AugmentedCotangentBasis
#print axioms pairedC3AugmentedCotangentBasis_apply
end HodgeLean.Foundations.Program.G32Native
