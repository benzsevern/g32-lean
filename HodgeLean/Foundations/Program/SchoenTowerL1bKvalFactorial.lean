import HodgeLean.Foundations.Port.AlgebraicGeometry.Smooth.RegularLocal
import HodgeLean.Foundations.DivisorClassHodgeRegular

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- The actual stalk of a smooth complex scheme is factorial.
Source: Matsumura, Commutative Ring Theory, Theorem 20.3. -/
theorem s2v_l1b_kval_stalk_factorial
    (B : Over (Spec (CommRingCat.of ℂ))) [Smooth B.hom] (x : B.left) :
    UniqueFactorizationMonoid (B.left.presheaf.stalk x) := by
  obtain ⟨V, hV, hxV, hf⟩ := Smooth.exists_affine_isStandardSmooth B.hom x
  let P : Ideal Γ(B.left, V) := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hstandard := algebraMap_isStandardSmooth B hf
  have : IsRegularRing Γ(B.left, V) := by
    have : Algebra.IsStandardSmooth ℂ Γ(B.left, V) := hstandard
    have : Algebra.FiniteType ℂ Γ(B.left, V) := inferInstance
    have : IsNoetherianRing Γ(B.left, V) := Algebra.FiniteType.isNoetherianRing ℂ _
    exact ⟨fun Q _ => hstandard.isRegularLocalRing_atPrime Q⟩
  have hfactorial := HodgeLean.Foundations.dcl_ufd_localization_atPrime P
  let : Algebra Γ(B.left, V) (B.left.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk B.left.presheaf ⟨x, hxV⟩
  let : IsLocalization.AtPrime (B.left.presheaf.stalk x) P :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  exact (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
    (B.left.presheaf.stalk x)).toRingEquiv.toMulEquiv.uniqueFactorizationMonoid hfactorial

/-- Factoriality and the domain property transport to the specified representation of a stalk. -/
theorem s2v_l1b_kval_represented_stalk_factorial
    (B : Over (Spec (CommRingCat.of ℂ))) [IsIntegral B.left] [Smooth B.hom]
    (x : B.left) (R : Type) [CommRing R]
    (eR : R ≃+* B.left.presheaf.stalk x) :
    IsDomain R ∧ UniqueFactorizationMonoid R := by
  exact ⟨eR.toMulEquiv.isDomain_iff.mpr inferInstance,
    eR.symm.toMulEquiv.uniqueFactorizationMonoid (s2v_l1b_kval_stalk_factorial B x)⟩

end HodgeLean.Foundations.Program
