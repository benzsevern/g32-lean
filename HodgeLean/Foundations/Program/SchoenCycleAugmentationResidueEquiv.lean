import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A field-valued algebra augmentation identifies the actual residue field of a local algebra with the scalar field.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
def s2e_augmentation_residue_equiv
    (k A : Type*) [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    (ε : A →ₐ[k] k) : IsLocalRing.ResidueField A ≃ₐ[k] k := by
  have hε : Function.Surjective ε := fun c => ⟨algebraMap k A c, ε.commutes c⟩
  have hker := IsLocalRing.ker_eq_maximalIdeal ε.toRingHom hε
  exact (Ideal.quotientEquivAlgOfEq k hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hε)

#print axioms s2e_augmentation_residue_equiv

/-- The augmentation residue identification evaluates actual quotient classes by the original augmentation.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_augmentation_residue_equiv_apply
    (k A : Type*) [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    (ε : A →ₐ[k] k) (a : A) :
    s2e_augmentation_residue_equiv k A ε (IsLocalRing.residue A a) = ε a := by
  unfold s2e_augmentation_residue_equiv
  rw [AlgEquiv.trans_apply]
  change (Ideal.quotientKerAlgEquivOfSurjective _)
    ((Ideal.quotientEquivAlgOfEq k _) (Ideal.Quotient.mk _ a)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]

#print axioms s2e_augmentation_residue_equiv_apply
end HodgeLean.Foundations.Program
