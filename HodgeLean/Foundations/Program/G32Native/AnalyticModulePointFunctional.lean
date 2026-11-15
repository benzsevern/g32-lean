import HodgeLean.Foundations.Program.G32Native.AnalyticPointDerivation
import HodgeLean.Foundations.Program.G32Native.AffinePointGlobalSection

/-! # Analytic equation derivatives as functionals on actual affine point fibres -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- Differentiate an ambient-ring-linear module of equations whose values
vanish at the specified analytic point. -/
def analyticModulePointDerivative (d : ℕ) (v : Fin d → ℂ)
    {R : Type*} [CommRing R] (φ : R →+* s2e_nativeAnalyticGermRing d)
    {N : Type*} [AddCommGroup N] [Module R N] (j : N →ₗ[R] R)
    (hj : ∀ n, s2e_nativeAnalyticGerm_value d (φ (j n)) = 0) :
    letI : Algebra R ℂ := ((s2e_nativeAnalyticGerm_value d).comp φ).toAlgebra
    N →ₗ[R] ℂ := by
  letI : Algebra R ℂ := ((s2e_nativeAnalyticGerm_value d).comp φ).toAlgebra
  let D := analyticPointDerivation d v φ
  refine {
    toFun := fun n => D (j n)
    map_add' := ?_
    map_smul' := ?_ }
  · intro n m
    rw [map_add, map_add]
  · intro r n
    rw [map_smul]
    change D (r * j n) = r • D (j n)
    rw [D.leibniz]
    have hz : j n • D r = 0 := by
      change s2e_nativeAnalyticGerm_value d (φ (j n)) * D r = 0
      rw [hj, zero_mul]
    rw [hz, add_zero]

/-- Analytic differentiation of a module of vanishing equations gives a
functional on its actual affine point fibre through the canonical dual comparison. -/
def affineAnalyticModuleFunctional (d : ℕ) (v : Fin d → ℂ)
    (R : CommRingCat.{0}) (φ : R →+* s2e_nativeAnalyticGermRing d)
    (M : (Spec R).Modules) [IsIso M.fromTildeΓ]
    (j : (moduleSpecΓFunctor (R := R)).obj M →ₗ[R] R)
    (hj : ∀ m, s2e_nativeAnalyticGerm_value d (φ (j m)) = 0) :
    let ε : R ⟶ CommRingCat.of ℂ := CommRingCat.ofHom ((s2e_nativeAnalyticGerm_value d).comp φ)
    Module.Dual ℂ ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback (Spec.map ε)).obj M)) := by
  let ε : R ⟶ CommRingCat.of ℂ := CommRingCat.ofHom ((s2e_nativeAnalyticGerm_value d).comp φ)
  letI : Algebra R ℂ := ε.hom.toAlgebra
  exact (affinePointDualEquiv R ε M).symm (analyticModulePointDerivative d v φ j hj)

/-- The constructed actual point-fibre functional evaluates each original
global equation section by its original analytic point derivation. -/
theorem affineAnalyticModuleFunctional_globalSection (d : ℕ) (v : Fin d → ℂ)
    (R : CommRingCat.{0}) (φ : R →+* s2e_nativeAnalyticGermRing d)
    (M : (Spec R).Modules) [IsIso M.fromTildeΓ]
    (j : (moduleSpecΓFunctor (R := R)).obj M →ₗ[R] R)
    (hj : ∀ m, s2e_nativeAnalyticGerm_value d (φ (j m)) = 0)
    (s : unit (Spec R) ⟶ M) :
    let ε : R ⟶ CommRingCat.of ℂ := CommRingCat.ofHom ((s2e_nativeAnalyticGerm_value d).comp φ)
    affineAnalyticModuleFunctional d v R φ M j hj
      ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
        ((Scheme.Modules.pullback (Spec.map ε)).map s)
        ((moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map (pullbackUnit (Spec.map ε)).inv
          (1 : Γ(Spec ↧ℂ, ⊤)))) =
      analyticPointDerivation d v φ
        (j (show (moduleSpecΓFunctor (R := R)).obj M from
          s.val.app (op ⊤) (1 : Γ(Spec R, ⊤)))) := by
  let ε : R ⟶ CommRingCat.of ℂ := CommRingCat.ofHom ((s2e_nativeAnalyticGerm_value d).comp φ)
  letI : Algebra R ℂ := ε.hom.toAlgebra
  have h := affinePointDualEquiv_globalSection R ε M s
    (affineAnalyticModuleFunctional d v R φ M j hj)
  rw [show affinePointDualEquiv R ε M (affineAnalyticModuleFunctional d v R φ M j hj) =
      analyticModulePointDerivative d v φ j hj from
    (affinePointDualEquiv R ε M).apply_symm_apply _] at h
  exact h.symm

#print axioms affineAnalyticModuleFunctional_globalSection
#print axioms affineAnalyticModuleFunctional
#print axioms analyticModulePointDerivative
end HodgeLean.Foundations.Program.G32Native
