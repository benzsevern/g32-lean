import HodgeLean.Foundations.Program.SchoenTowerL1bKummerGermPullback
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerRationalDescent
import HodgeLean.Foundations.Program.SchoenTowerL1aInvariantComparison

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Rational functions fixed by a finite categorical quotient's symmetries come from its actual base field. -/
theorem s2v_l1b_categorical_quotient_fixed_rational_function
    {S : Scheme.{0}} (X Y : Over S) [IsIntegral X.left] [IsIntegral Y.left]
    {I : Type} [Finite I] (f : X ⟶ Y) [IsFinite f.left] [IsDominant f.left]
    (a : I → (X ⟶ X)) [∀ i, IsIso (a i)] (hinv : ∀ i, a i ≫ f = f)
    (hcat : ∀ (T : Over S) (g : X ⟶ T),
      (∀ i, a i ≫ g = g) → ∃! u : Y ⟶ T, f ≫ u = g)
    (U : Y.left.affineOpens) [Nonempty U.1] :
    letI := (s2v_l1b_functionFieldPullback f.left).hom.toAlgebra
    ∀ τ : I → (X.left.functionField ≃ₐ[Y.left.functionField] X.left.functionField),
      (∀ i, (τ i).toRingHom = (s2v_l1b_functionFieldPullback (a i).left).hom) →
      ∀ z : X.left.functionField, (∀ i, τ i z = z) →
        ∃ c : Y.left.functionField, s2v_l1b_functionFieldPullback f.left c = z := by
  letI := (s2v_l1b_functionFieldPullback f.left).hom.toAlgebra
  intro τ hτ z hz
  haveI : Nonempty (f.left ⁻¹ᵁ U.1) := by
    refine ⟨⟨genericPoint X.left, ?_⟩⟩
    change f.left (genericPoint X.left) ∈ U.1
    rw [s2_dominant_genericPoint f.left]
    exact ((genericPoint_spec Y.left).mem_open_set_iff U.1.isOpen).mpr
      (by simpa using ‹Nonempty U.1›)
  let A := Γ(Y.left, U)
  let B := Γ(X.left, f.left ⁻¹ᵁ U.1)
  letI : Algebra A B := (f.left.app U.1).hom.toAlgebra
  letI : Algebra A X.left.functionField :=
    ((X.left.germToFunctionField (f.left ⁻¹ᵁ U.1)).hom.comp (f.left.app U.1).hom).toAlgebra
  haveI : IsFractionRing A Y.left.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y.left U.1 U.2
  haveI : IsFractionRing B X.left.functionField :=
    functionField_isFractionRing_of_isAffineOpen X.left (f.left ⁻¹ᵁ U.1) (U.2.preimage f.left)
  haveI : IsScalarTower A B X.left.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower A Y.left.functionField X.left.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change (X.left.germToFunctionField (f.left ⁻¹ᵁ U.1)) ((f.left.app U.1) c) =
        (s2v_l1b_functionFieldPullback f.left) (Y.left.germToFunctionField U.1 c)
      simpa only [Scheme.Hom.appLE_eq_app, CommRingCat.comp_apply] using
        (congrArg (fun k : A ⟶ X.left.functionField => k c)
          (s2v_l1b_functionFieldPullback_germ f.left (f.left ⁻¹ᵁ U.1) U.1 le_rfl)).symm
  haveI : Algebra.IsIntegral A B := ⟨f.left.isIntegral_app U.1 U.2⟩
  let ha : ∀ i, (a i).left ≫ f.left = f.left :=
    fun i => congrArg Over.Hom.left (hinv i)
  let ρ : I → (B →+* B) := fun i =>
    (s2v_l1a_saturatedSectionEnd f.left (fun i => (a i).left) ha U.1 i).hom
  apply s2v_l1b_fixed_rational_function_descends A B Y.left.functionField X.left.functionField
    I ρ τ ?_ ?_ z hz
  · intro i b
    have hpre : f.left ⁻¹ᵁ U.1 ≤ (a i).left ⁻¹ᵁ (f.left ⁻¹ᵁ U.1) := by
      rw [← Scheme.Hom.comp_preimage, ha i]
    have h := s2v_l1b_functionFieldPullback_germ (a i).left
      (f.left ⁻¹ᵁ U.1) (f.left ⁻¹ᵁ U.1) hpre
    have he := congrArg (fun k : B ⟶ X.left.functionField => k b) h
    change algebraMap B X.left.functionField (ρ i b) = τ i (algebraMap B X.left.functionField b)
    change algebraMap B X.left.functionField (ρ i b) =
      (τ i).toRingHom (algebraMap B X.left.functionField b)
    rw [hτ]
    exact he.symm
  · intro b hb
    exact (s2v_l1a_affine_sections_range_of_categorical_quotient X Y f a hinv hcat U).2 b |>.mpr hb

end HodgeLean.Foundations.Program
