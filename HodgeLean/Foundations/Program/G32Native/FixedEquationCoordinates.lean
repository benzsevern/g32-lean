import Mathlib.Analysis.Normed.Module.FiniteDimension
import HodgeLean.Foundations.Program.G32Native.FixedChartTangentMaps
import HodgeLean.Foundations.Program.G32Native.FixedChartRegularChange
import HodgeLean.Foundations.Program.G32Native.CanonicalConormalDerivativeEquation
import HodgeLean.Foundations.Program.G32Native.ConormalLocalEquationBasis

/-! # Finite actual equation coordinates in a fixed ambient chart -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Curves.Picard.LineBundles
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- The derivative rows of the original ideal equations in one fixed chart.
Source: Hartshorne, Algebraic Geometry, II.8; Lee, Introduction to Smooth Manifolds, ch. 10. -/
def equationFixedDerivative (G : CanonicalAbelGeometry) (x : ComplexPoint G.Q)
    (U : G.W.left.Opens)
    (s : Fin G.k → (unit U.toScheme ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule G.ι.left)))
    (y : ComplexPoint G.Q) :
    (Fin (G.k + G.k) → ℂ) →L[ℂ] (Fin G.k → ℂ) :=
  ContinuousLinearMap.pi (fun j =>
    fderiv ℂ (fun v => Point.evaluate U (conormalLocalFunction G.ι U (s j))
      ((localChart G.W (G.k + G.k) (Point.map G.ι x)).symm v))
      (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y)))

/-- Evaluation of actual normal functionals on the original finite equation classes.
Source: Hartshorne, Algebraic Geometry, II.8, conormal dual coordinates. -/
def equationPointCoordinates (G : CanonicalAbelGeometry) (U : G.W.left.Opens)
    (s : Fin G.k → (unit U.toScheme ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule G.ι.left)))
    (y : ComplexPoint G.Q) (hy : Point.map G.ι y ∈ Point.overOpen U) :
    canonicalNormalFibre G y →ₗ[ℂ] (Fin G.k → ℂ) where
  toFun ν j := ν (conormalLocalClass G.ι U (s j) y hy)
  map_add' ν μ := by ext j; rfl
  map_smul' c ν := by ext j; rfl

#print axioms equationFixedDerivative
#print axioms equationPointCoordinates

/-- Transporting a vector from its original point chart makes the fixed
matrix evaluate exactly the original conormal equation classes. -/
theorem equationFixedDerivative_comp_pointToFixed (G : CanonicalAbelGeometry)
    (x : ComplexPoint G.Q) (U : G.W.left.Opens)
    (s : Fin G.k → (unit U.toScheme ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule G.ι.left)))
    (y : ComplexPoint G.Q) (hy : Point.map G.ι y ∈ Point.overOpen U)
    (hyp : Point.map G.ι y ∈ (localChart G.W (G.k + G.k) (Point.map G.ι x)).source) :
    (equationFixedDerivative G x U s y).toLinearMap.comp
      (pointToFixedTangent G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y)).toLinearMap =
    (equationPointCoordinates G U s y hy).comp (canonicalConormalDerivative G y) := by
  apply LinearMap.ext
  intro v
  funext j
  change
    (fderiv ℂ (fun u => Point.evaluate U (conormalLocalFunction G.ι U (s j))
      ((localChart G.W (G.k + G.k) (Point.map G.ι x)).symm u))
      (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y)))
      (pointToFixedTangent G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y) v) =
    canonicalConormalDerivative G y v (conormalLocalClass G.ι U (s j) y hy)
  rw [canonicalConormalDerivative_localEquation]
  exact (DFunLike.congr_fun (regular_fderiv_change_to_point_chart G.W (G.k + G.k)
    (Point.map G.ι x) (Point.map G.ι y) U (conormalLocalFunction G.ι U (s j)) hy hyp) v).symm

#print axioms equationFixedDerivative_comp_pointToFixed


/-- The fixed equation matrix factors through the actual conormal derivative
and the original fixed-to-point tangent change. -/
theorem equationFixedDerivative_factor (G : CanonicalAbelGeometry)
    (x : ComplexPoint G.Q) (U : G.W.left.Opens)
    (s : Fin G.k → (unit U.toScheme ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule G.ι.left)))
    (y : ComplexPoint G.Q) (hy : Point.map G.ι y ∈ Point.overOpen U)
    (hyp : Point.map G.ι y ∈ (localChart G.W (G.k + G.k) (Point.map G.ι x)).source) :
    (equationFixedDerivative G x U s y).toLinearMap =
      (equationPointCoordinates G U s y hy).comp
        ((canonicalConormalDerivative G y).comp
          (fixedToPointTangent G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y)).toLinearMap) := by
  let I := pointToFixedTangent G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y)
  let J := fixedToPointTangent G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y)
  apply LinearMap.ext
  intro v
  have hIJ : I (J v) = v := DFunLike.congr_fun
    (pointToFixed_comp_fixedToPoint G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y) hyp) v
  have hh := DFunLike.congr_fun (equationFixedDerivative_comp_pointToFixed G x U s y hy hyp) (J v)
  change equationFixedDerivative G x U s y (I (J v)) =
    equationPointCoordinates G U s y hy (canonicalConormalDerivative G y (J v)) at hh
  change equationFixedDerivative G x U s y v = _
  rw [hIJ] at hh
  exact hh

#print axioms equationFixedDerivative_factor


/-- Original equation coordinates spanning the normal dual make the fixed
ambient equation derivative surjective. -/
theorem equationFixedDerivative_surjective (G : CanonicalAbelGeometry)
    (x : ComplexPoint G.Q) (U : G.W.left.Opens)
    (s : Fin G.k → (unit U.toScheme ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule G.ι.left)))
    (y : ComplexPoint G.Q) (hy : Point.map G.ι y ∈ Point.overOpen U)
    (hyp : Point.map G.ι y ∈ (localChart G.W (G.k + G.k) (Point.map G.ι x)).source)
    (hs : Function.Surjective (equationPointCoordinates G U s y hy)) :
    Function.Surjective (equationFixedDerivative G x U s y) := by
  intro a
  obtain ⟨ν, hν⟩ := hs a
  obtain ⟨v, hv⟩ := canonicalConormalDerivative_surjective G y ν
  refine ⟨pointToFixedTangent G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y) v, ?_⟩
  have hh := DFunLike.congr_fun (equationFixedDerivative_comp_pointToFixed G x U s y hy hyp) v
  change equationFixedDerivative G x U s y
    (pointToFixedTangent G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y) v) =
      equationPointCoordinates G U s y hy (canonicalConormalDerivative G y v) at hh
  rw [hh, hv]
  exact hν

#print axioms equationFixedDerivative_surjective


/-- On every original containing affine open there are actual ideal equations
whose fixed-chart matrix is surjective at the reference point. -/
theorem exists_equationFixedDerivative_surjective (G : CanonicalAbelGeometry)
    (x : ComplexPoint G.Q) (U : G.W.left.Opens) (hU : IsAffineOpen U)
    (hx : Point.map G.ι x ∈ Point.overOpen U) :
    ∃ s : Fin G.k → (unit U.toScheme ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule G.ι.left)),
      Function.Surjective (equationFixedDerivative G x U s x) := by
  obtain ⟨s, e, he⟩ := conormalLocalClasses_exists_dual_coordinates G.k G.k G.ι x U hU hx
  refine ⟨s, equationFixedDerivative_surjective G x U s x hx
    (mem_localChart_source _ _ _) ?_⟩
  have hh : equationPointCoordinates G U s x hx = e.toLinearMap := by
    ext ν j
    exact (he ν j).symm
  rw [hh]
  exact e.surjective

#print axioms exists_equationFixedDerivative_surjective


/-- The fixed matrix of actual regular equation derivatives is continuous on
the original chart and equation domain. -/
theorem continuousOn_equationFixedDerivative (G : CanonicalAbelGeometry)
    (x : ComplexPoint G.Q) (U : G.W.left.Opens)
    (s : Fin G.k → (unit U.toScheme ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule G.ι.left))) :
    ContinuousOn (equationFixedDerivative G x U s)
      {y | Point.map G.ι y ∈ (Point.overOpen U : Set (ComplexPoint G.W)) ∩
        (localChart G.W (G.k + G.k) (Point.map G.ι x)).source} := by
  apply continuousOn_clm_apply.mpr
  intro v
  apply continuousOn_pi.mpr
  intro j
  have hc := (continuousOn_fixedChart_regular_fderiv G.W (G.k + G.k) (Point.map G.ι x)
    U (conormalLocalFunction G.ι U (s j))).comp
      (Point.continuous_map G.ι).continuousOn (fun _ hy => hy)
  exact hc.clm_apply continuousOn_const

#print axioms continuousOn_equationFixedDerivative

end HodgeLean.Foundations.Program.G32Native
