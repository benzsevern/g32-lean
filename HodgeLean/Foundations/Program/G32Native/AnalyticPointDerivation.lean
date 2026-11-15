import HodgeLean.Foundations.Program.SchoenCycleNativeAnalyticDerivation
import HodgeLean.Foundations.Program.SchoenCycleNativeAnalyticStalk
import HodgeLean.Foundations.Program.G32Native.PointConormalDerivative

/-! # Point-valued derivatives through the actual analytic germ comparison -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Topology CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native

/-- Differentiate a ring of analytic germs and evaluate at the original point.
The ambient-ring action on values is its actual germ evaluation. -/
def analyticPointDerivation (d : ℕ) (v : Fin d → ℂ)
    {R : Type*} [CommRing R] (φ : R →+* s2e_nativeAnalyticGermRing d) :
    letI : Algebra R ℂ := ((s2e_nativeAnalyticGerm_value d).comp φ).toAlgebra
    Derivation ℤ R ℂ := by
  letI : Algebra R ℂ := ((s2e_nativeAnalyticGerm_value d).comp φ).toAlgebra
  let D : R →+ ℂ := {
    toFun r := s2e_nativeAnalyticGerm_value d (s2e_nativeAnalytic_derivation d v (φ r))
    map_zero' := by simp only [map_zero]
    map_add' r s := by simp only [map_add] }
  apply Derivation.mk' D.toIntLinearMap
  intro r s
  change s2e_nativeAnalyticGerm_value d
    (s2e_nativeAnalytic_derivation d v (φ (r * s))) =
      s2e_nativeAnalyticGerm_value d (φ r) *
        s2e_nativeAnalyticGerm_value d (s2e_nativeAnalytic_derivation d v (φ s)) +
      s2e_nativeAnalyticGerm_value d (φ s) *
        s2e_nativeAnalyticGerm_value d (s2e_nativeAnalytic_derivation d v (φ r))
  rw [map_mul, Derivation.leibniz]
  simp only [smul_eq_mul, map_add, map_mul]

/-- On a specified germ representative, the point derivation evaluates the
original coordinate derivative with its original direction and scalar. -/
theorem analyticPointDerivation_representative (d : ℕ) (v : Fin d → ℂ)
    {R : Type*} [CommRing R] (φ : R →+* s2e_nativeAnalyticGermRing d)
    (r : R) (f : (Fin d → ℂ) → ℂ)
    (he : (φ r).val = Filter.Germ.ofFun f) :
    analyticPointDerivation d v φ r = fderiv ℂ f 0 v := by
  change Filter.Germ.liftOn
    (Filter.Germ.liftOn (φ r).val
      (fun F => Filter.Germ.ofFun (fun z => fderiv ℂ F z v)) _)
    (fun F => F 0) _ = _
  rw [he]
  rfl

/-- The actual regular-section germ comparison gives precisely the derivative
in the original ambient chart, with no change of normalization. -/
theorem regularSection_pointDerivative
    (W : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d W.hom]
    (p : ComplexPoint W) (U : W.left.Opens) (hp : p.underlying ∈ U)
    (s : Γ(W.left, U)) (v : Fin d → ℂ) :
    analyticPointDerivation d v (s2e_regularSection_nativeAnalyticGerm W d p U hp) s =
      fderiv ℂ (fun w => Point.evaluate U s ((localChart W d p).symm w))
        (localChart W d p p) v := by
  rw [analyticPointDerivation_representative d v _ s
    (fun z => Point.evaluate U s ((localChart W d p).symm (localChart W d p p + z))) rfl]
  have h := fderiv_comp_add_left (𝕜 := ℂ)
    (f := fun w => Point.evaluate U s ((localChart W d p).symm w))
    (x := (0 : Fin d → ℂ)) (localChart W d p p)
  rw [add_zero] at h
  exact DFunLike.congr_fun h v

/-- The analytic point derivation is additive in the original ambient
coordinate direction. -/
theorem analyticPointDerivation_add_direction (d : ℕ) (v w : Fin d → ℂ)
    {R : Type*} [CommRing R] (φ : R →+* s2e_nativeAnalyticGermRing d) (r : R) :
    analyticPointDerivation d (v + w) φ r =
      analyticPointDerivation d v φ r + analyticPointDerivation d w φ r := by
  obtain ⟨f, _, he⟩ := (φ r).property
  rw [analyticPointDerivation_representative d (v + w) φ r f he.symm,
    analyticPointDerivation_representative d v φ r f he.symm,
    analyticPointDerivation_representative d w φ r f he.symm]
  exact map_add (fderiv ℂ f 0) v w

/-- The analytic point derivation retains complex scalar multiplication of
the original ambient coordinate direction. -/
theorem analyticPointDerivation_smul_direction (d : ℕ) (c : ℂ) (v : Fin d → ℂ)
    {R : Type*} [CommRing R] (φ : R →+* s2e_nativeAnalyticGermRing d) (r : R) :
    analyticPointDerivation d (c • v) φ r = c * analyticPointDerivation d v φ r := by
  obtain ⟨f, _, he⟩ := (φ r).property
  rw [analyticPointDerivation_representative d (c • v) φ r f he.symm,
    analyticPointDerivation_representative d v φ r f he.symm]
  exact map_smul (fderiv ℂ f 0) c v

#print axioms analyticPointDerivation_smul_direction
#print axioms analyticPointDerivation_add_direction
#print axioms regularSection_pointDerivative
#print axioms analyticPointDerivation_representative
#print axioms analyticPointDerivation
end HodgeLean.Foundations.Program.G32Native
