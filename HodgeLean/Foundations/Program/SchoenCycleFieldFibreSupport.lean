import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Unramified.Locus

/-! # Finite module support detected by actual field fibres -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Vanishing over a field with the stated prime kernel excludes that prime from the support of a finite module.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.5 and II.8; Atiyah–Macdonald, Corollary 2.7. -/
theorem s2e_not_mem_support_of_field_fibre
    (A K M : Type) [CommRing A] [Field K] [AddCommGroup M] [Module A M]
    [Module.Finite A M] (φ : A →+* K) (p : PrimeSpectrum A)
    (hp : p.asIdeal = RingHom.ker φ) :
    letI : Algebra A K := φ.toAlgebra
    Subsingleton (K ⊗[A] M) → p ∉ Module.support A M := by
  letI : Algebra A K := φ.toAlgebra
  intro h
  have hu : p.asIdeal.primeCompl ≤ (IsUnit.submonoid K).comap φ := by
    intro a ha
    apply isUnit_iff_ne_zero.mpr
    intro hz
    exact ha (hp.symm ▸ hz)
  let ψ := Ideal.ResidueField.lift p.asIdeal φ hp.le hu
  letI : Algebra p.asIdeal.ResidueField K := ψ.toAlgebra
  letI : IsScalarTower A p.asIdeal.ResidueField K :=
    IsScalarTower.of_algebraMap_eq fun a => (Ideal.ResidueField.lift_algebraMap p.asIdeal φ hp.le hu a).symm
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange A p.asIdeal.ResidueField K K M
  have ht : Subsingleton (K ⊗[p.asIdeal.ResidueField] (p.asIdeal.ResidueField ⊗[A] M)) :=
    e.toEquiv.subsingleton_congr.mpr h
  have hk : Subsingleton (p.asIdeal.ResidueField ⊗[A] M) :=
    (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right p.asIdeal.ResidueField K).mp ht
  intro hm
  have hn := (Module.mem_support_iff_nontrivial_residueField_tensorProduct p).mp hm
  exact @not_nontrivial_iff_subsingleton.mpr hk hn

/-- A vanishing relative cotangent field fibre gives unramifiedness at its actual prime kernel.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Hartshorne, Algebraic Geometry, II.8; Atiyah–Macdonald, Corollary 2.7. -/
theorem s2e_isUnramifiedAt_of_field_cotangent_fibre
    (R A K : Type) [CommRing R] [CommRing A] [Field K] [Algebra R A]
    [Module.Finite A Ω[A⁄R]] (φ : A →+* K) (p : PrimeSpectrum A)
    (hp : p.asIdeal = RingHom.ker φ) :
    letI : Algebra A K := φ.toAlgebra
    Subsingleton (K ⊗[A] Ω[A⁄R]) → Algebra.IsUnramifiedAt R p.asIdeal := by
  letI : Algebra A K := φ.toAlgebra
  intro h
  change p ∈ Algebra.unramifiedLocus R A
  rw [Algebra.unramifiedLocus_eq_compl_support]
  exact s2e_not_mem_support_of_field_fibre A K Ω[A⁄R] φ p hp h

end HodgeLean.Foundations.Program
