import HodgeLean.Foundations.QuotientDuality.RetainedBirationalPowerBasis
import HodgeLean.Foundations.QuotientDuality.RetainedFieldSourceScalars
import HodgeLean.Foundations.QuotientDuality.MonomialPowerBasisGeneration
import HodgeLean.Foundations.QuotientDuality.MonomialSignedGeneratorReduction
import HodgeLean.Foundations.QuotientDuality.MonomialWeightedGeneratorReduction

/-! The retained generic square and weighted branch identity construct the strict Kummer equation. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

theorem retained_strict_kummer_field_chart
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (P : X.PartialIso Y)
    (hP : P.iso.hom ≫ P.target.ι = P.source.ι ≫ f)
    (L : Type) [Field L] (ηX : Spec (CommRingCat.of L) ⟶ X) [IsDominant ηX]
    (ηY : Spec (CommRingCat.of L) ⟶ Y) (hη : ηX ≫ f = ηY)
    (φY : Y.functionField →+* L)
    (hY : Spec.map (CommRingCat.ofHom φY) ≫ Y.fromSpecStalk (genericPoint Y) = ηY)
    (m : ℕ) (hm : 0 < m) (U : X.affineOpens) [Nonempty U.1]
    (hU : ηX ⁻¹ᵁ U.1 = ⊤) {J : Type} [Fintype J]
    (g s : J → Γ(X, U)) (hg : ∀ j, g j ≠ 0) (a : J → ℤ)
    (E : Γ(X, U)) (u : Γ(X, U)ˣ) :
    letI := φY.toAlgebra
    letI : Algebra Γ(X, U) L :=
      (ηX.app U.1 ≫ (s2v_fieldSourceSectionsIso ηX U.1 hU).hom).hom.toAlgebra
    let hg := s2e_c1_dominant_generic_point f
    let ψ := (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫
      f.stalkMap (genericPoint X)).hom
    ∀ (B : PowerBasis Y.functionField L) (c : Y.functionField),
      B.gen ^ m = φY c →
      ψ c = X.germToFunctionField U.1 (u : Γ(X, U)) *
        ∏ j, (X.germToFunctionField U.1 (g j)) ^ a j →
      (∏ j, (Ideal.span {g j}) ^ (a j % (m : ℤ)).toNat) =
        (∏ j, (Ideal.span {s j}) ^ (a j % (m : ℤ)).toNat) * (Ideal.span {E}) ^ m →
      ∃ (ε : Γ(X, U)ˣ) (v : L),
        v ^ m = algebraMap Γ(X, U) L (ε : Γ(X, U)) *
          ∏ j, (algebraMap Γ(X, U) L (s j)) ^ (a j % (m : ℤ)).toNat ∧
        Subfield.closure (Set.range (algebraMap Γ(X, U) L) ∪ {v}) = ⊤ := by
  letI := φY.toAlgebra
  letI : Algebra Γ(X, U) L :=
    (ηX.app U.1 ≫ (s2v_fieldSourceSectionsIso ηX U.1 hU).hom).hom.toAlgebra
  dsimp only
  intro B c hroot hcoeff hI
  obtain ⟨κ, hκ, C, hC, hdimC, hrootC⟩ :=
    retained_birational_kummer_power_basis f P hP L ηX ηY hη φY hY B c m hroot
  letI : Algebra X.functionField L := κ.toAlgebra
  have hscalars : κ.comp (X.germToFunctionField U.1).hom = algebraMap Γ(X, U) L :=
    (fieldSourceChart_scalar_eq_generic X ηX κ hκ U hU).symm
  letI : IsScalarTower Γ(X, U) X.functionField L :=
    IsScalarTower.of_algebraMap_eq' hscalars.symm
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  have hinj : Function.Injective (algebraMap Γ(X, U) L) := by
    rw [IsScalarTower.algebraMap_eq Γ(X, U) X.functionField L]
    exact κ.injective.comp (IsFractionRing.injective Γ(X, U) X.functionField)
  have hκR (r : Γ(X, U)) : κ (X.germToFunctionField U.1 r) = algebraMap Γ(X, U) L r :=
    RingHom.congr_fun hscalars r
  have hv : C.gen ^ m = algebraMap Γ(X, U) L (u : Γ(X, U)) *
      ∏ j, (algebraMap Γ(X, U) L (g j)) ^ a j := by
    rw [hrootC, hcoeff, map_mul, map_prod]
    simp_rw [map_zpow₀, hκR]
  obtain ⟨v, hv, hgen⟩ := signed_kummer_generator_residue_reduction hinj m hm g hg a u C.gen hv
    (powerBasis_field_closure_eq_top C)
  exact weighted_kummer_generator_strict_reduction hinj m hm g s hg
    (fun j => (a j % (m : ℤ)).toNat) E u v hI hv hgen

#print axioms retained_strict_kummer_field_chart
end HodgeLean.Foundations.QuotientDuality
