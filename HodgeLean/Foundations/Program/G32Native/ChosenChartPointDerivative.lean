import HodgeLean.Foundations.Program.G32Native.ChosenChartCoordinateMap
import HodgeLean.Foundations.Program.G32Native.EtaleAnalyticPointDerivation
import HodgeLean.Foundations.Program.G32Native.EtaleCoordinateDerivations
import HodgeLean.Foundations.Program.SchoenCycleActualAnalyticAdic

/-! # Original point derivatives on the chosen coordinate open -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native

/-- Differentiation of an original chosen coordinate section retains exactly
its original tangent coordinate. -/
theorem chosenChart_pointDerivative_coordinate (W : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d W.hom] (p : ComplexPoint W)
    (hp : p.underlying ∈ (localEtaleCoordinates W d p).ambientCoordinateOpen)
    (v : Fin d → ℂ) (i : Fin d) :
    letI := overSpecAlgebra W (localEtaleCoordinates W d p).ambientCoordinateOpen
    analyticPointDerivation d v
      (s2e_regularSection_nativeAnalyticGerm W d p _ hp)
      (chosenChartCoordinateMap W d p (MvPolynomial.X i)) = v i := by
  change s2e_nativeAnalyticGerm_value d
    (s2e_nativeAnalytic_derivation d v
      (s2e_regularSection_nativeAnalyticGerm W d p _ hp
        ((localEtaleCoordinates W d p).ambientCoordinateSection i))) = v i
  rw [s2e_actual_coordinateSection_nativeAnalytic, map_add,
    s2e_nativeAnalytic_derivation_constant, s2e_nativeAnalytic_derivation_coordinate,
    zero_add]
  rfl

/-- The original regular germ map on any ambient open retains its complex
scalar structure. -/
theorem regularGermMap_complexConstants (W : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d W.hom] (p : ComplexPoint W)
    (U : W.left.Opens) (hp : p.underlying ∈ U) :
    letI := overSpecAlgebra W U
    ∀ c : ℂ, s2e_regularSection_nativeAnalyticGerm W d p U hp
      (algebraMap ℂ Γ(W.left, U) c) = s2e_nativeAnalytic_constant d c := by
  intro c
  exact s2e_actual_constantSection_nativeAnalytic W d p U hp c

/-- The analytic derivative in the original chart equals the algebraic
point derivation specified by those same original coordinate values. -/
theorem chosenChart_pointDerivative_eq (W : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d W.hom] (p : ComplexPoint W)
    (hp : p.underlying ∈ (localEtaleCoordinates W d p).ambientCoordinateOpen)
    (v : Fin d → ℂ) :
    let U := (localEtaleCoordinates W d p).ambientCoordinateOpen
    letI := overSpecAlgebra W U
    let φ := s2e_regularSection_nativeAnalyticGerm W d p U hp
    letI : Algebra Γ(W.left, U) ℂ := ((s2e_nativeAnalyticGerm_value d).comp φ).toAlgebra
    letI : IsScalarTower ℂ Γ(W.left, U) ℂ :=
      analyticPoint_scalarTower d φ (regularGermMap_complexConstants W d p U hp)
    analyticComplexPointDerivation d v φ (regularGermMap_complexConstants W d p U hp) =
      etaleCoordinateDerivationEquiv ℂ Γ(W.left, U) d
        (chosenChartCoordinateMap W d p) (chosenChartCoordinateMap_etale W d p) v := by
  let U := (localEtaleCoordinates W d p).ambientCoordinateOpen
  letI := overSpecAlgebra W U
  let φ := s2e_regularSection_nativeAnalyticGerm W d p U hp
  letI : Algebra Γ(W.left, U) ℂ := ((s2e_nativeAnalyticGerm_value d).comp φ).toAlgebra
  letI : IsScalarTower ℂ Γ(W.left, U) ℂ :=
    analyticPoint_scalarTower d φ (regularGermMap_complexConstants W d p U hp)
  exact etaleAnalyticPointDerivation_eq d φ
    (regularGermMap_complexConstants W d p U hp) (chosenChartCoordinateMap W d p)
    (chosenChartCoordinateMap_etale W d p) (localChart W d p p)
    (fun i => s2e_actual_coordinateSection_nativeAnalytic W d p hp i) v

/-- Every algebraic point derivation on the original coordinate open is
represented by an original analytic tangent direction. -/
theorem chosenChart_pointDerivative_surjective (W : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d W.hom] (p : ComplexPoint W)
    (hp : p.underlying ∈ (localEtaleCoordinates W d p).ambientCoordinateOpen) :
    let U := (localEtaleCoordinates W d p).ambientCoordinateOpen
    letI := overSpecAlgebra W U
    let φ := s2e_regularSection_nativeAnalyticGerm W d p U hp
    letI : Algebra Γ(W.left, U) ℂ := ((s2e_nativeAnalyticGerm_value d).comp φ).toAlgebra
    ∀ D : Derivation ℂ Γ(W.left, U) ℂ, ∃ v : Fin d → ℂ,
      ∀ r, analyticPointDerivation d v φ r = D r := by
  let U := (localEtaleCoordinates W d p).ambientCoordinateOpen
  letI := overSpecAlgebra W U
  let φ := s2e_regularSection_nativeAnalyticGerm W d p U hp
  letI : Algebra Γ(W.left, U) ℂ := ((s2e_nativeAnalyticGerm_value d).comp φ).toAlgebra
  letI : IsScalarTower ℂ Γ(W.left, U) ℂ :=
    analyticPoint_scalarTower d φ (regularGermMap_complexConstants W d p U hp)
  change ∀ D : Derivation ℂ Γ(W.left, U) ℂ, ∃ v : Fin d → ℂ,
    ∀ r, analyticPointDerivation d v φ r = D r
  intro D
  obtain ⟨v, hv⟩ := (etaleCoordinateDerivationEquiv ℂ Γ(W.left, U) d
    (chosenChartCoordinateMap W d p) (chosenChartCoordinateMap_etale W d p)).surjective D
  refine ⟨v, ?_⟩
  intro r
  exact DFunLike.congr_fun ((chosenChart_pointDerivative_eq W d p hp v).trans hv) r

#print axioms chosenChart_pointDerivative_surjective
#print axioms chosenChart_pointDerivative_eq
#print axioms regularGermMap_complexConstants
#print axioms chosenChart_pointDerivative_coordinate
end HodgeLean.Foundations.Program.G32Native
