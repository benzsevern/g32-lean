import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import HodgeLean.Foundations.Program.SchoenTowerAtPrimeAdic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.FieldTheory.Separable

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeLean.Foundations.Program

/-- At maximal ideals of finite-type algebras over an algebraically closed field, the actual
residue map of a coefficient-algebra homomorphism is bijective. -/
theorem s2t_quotientMap_bijective_of_algClosed {K A B : Type*}
    [Field K] [IsAlgClosed K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    [Algebra.FiniteType K A] [Algebra.FiniteType K B]
    (f : A →ₐ[K] B) (p : Ideal A) (q : Ideal B) [p.IsMaximal] [q.IsMaximal]
    (h : p ≤ q.comap f.toRingHom) :
    Function.Bijective (Ideal.quotientMap q f.toRingHom h) := by
  letI : Field (A ⧸ p) := Ideal.Quotient.field p
  letI : Field (B ⧸ q) := Ideal.Quotient.field q
  letI : Module.Finite K (B ⧸ q) := finite_of_finite_type_of_isJacobsonRing K (B ⧸ q)
  letI : Algebra.IsIntegral K (B ⧸ q) := .of_finite K (B ⧸ q)
  let F : (A ⧸ p) →ₐ[K] (B ⧸ q) := Ideal.quotientMapₐ q f h
  change Function.Bijective F
  refine ⟨F.toRingHom.injective, ?_⟩
  intro y
  obtain ⟨k, hk⟩ := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := B ⧸ q) |>.surjective y
  exact ⟨algebraMap K (A ⧸ p) k, (F.commutes k).trans hk⟩

/-- The residue field of the actual point-local ring is finite over the coefficient field. -/
theorem s2t_atPrimeResidue_finite {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A] (q : Ideal A) [q.IsMaximal] :
    Module.Finite K (IsLocalRing.ResidueField (Localization.AtPrime q)) := by
  letI : Field (A ⧸ q) := Ideal.Quotient.field q
  letI : Module.Finite K (A ⧸ q) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ q)
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal q (Localization.AtPrime q)
  exact Module.Finite.equiv ((e.restrictScalars K).toLinearEquiv)

/-- A finite residue extension over an algebraically closed coefficient field makes the
actual local residue map separable. -/
theorem s2t_residue_separable_of_algClosed {K R S : Type*}
    [Field K] [IsAlgClosed K] [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra K R] [Algebra K S] [Algebra R S]
    [IsScalarTower K R S] [IsLocalHom (algebraMap R S)]
    [Module.Finite K (IsLocalRing.ResidueField S)] :
    Algebra.IsSeparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := by
  let kR := IsLocalRing.ResidueField R
  let kS := IsLocalRing.ResidueField S
  letI : Algebra.IsIntegral K kS := .of_finite K kS
  have hsurj : Function.Surjective (algebraMap kR kS) := by
    intro y
    obtain ⟨k, hk⟩ := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := kS) |>.surjective y
    exact ⟨algebraMap K kR k, (IsScalarTower.algebraMap_apply K kR kS k).symm.trans hk⟩
  let e : kR ≃ₐ[kR] kS := AlgEquiv.ofBijective (Algebra.ofId kR kS)
    ⟨(algebraMap kR kS).injective, hsurj⟩
  exact Algebra.IsSeparable.of_algHom kR kR e.symm.toAlgHom

/-- Pullback preserves maximal ideals for coefficient maps into finite-type algebras over
an algebraically closed field. -/
theorem s2t_comap_isMaximal_of_algClosed {K A B : Type*}
    [Field K] [IsAlgClosed K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    [Algebra.FiniteType K B] (f : A →ₐ[K] B) (q : Ideal B) [q.IsMaximal] :
    (q.comap f.toRingHom).IsMaximal := by
  letI : Field (B ⧸ q) := Ideal.Quotient.field q
  letI : Module.Finite K (B ⧸ q) := finite_of_finite_type_of_isJacobsonRing K (B ⧸ q)
  letI : Algebra.IsIntegral K (B ⧸ q) := .of_finite K (B ⧸ q)
  have hsurj : Function.Surjective ((Ideal.Quotient.mk q).comp f.toRingHom) := by
    intro y
    obtain ⟨k, hk⟩ := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := B ⧸ q) |>.surjective y
    refine ⟨algebraMap K A k, ?_⟩
    change Ideal.Quotient.mk q (f (algebraMap K A k)) = y
    rw [f.commutes]
    exact hk
  have hmax := Ideal.comap_isMaximal_of_surjective ((Ideal.Quotient.mk q).comp f.toRingHom) hsurj (K := ⊥)
  change (Ideal.comap f.toRingHom (RingHom.ker (Ideal.Quotient.mk q))).IsMaximal at hmax
  rwa [Ideal.mk_ker] at hmax

end HodgeLean.Foundations.Program
