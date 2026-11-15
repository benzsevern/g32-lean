import HodgeLean.Foundations.Program.SchoenCycleS1j4Proofs

/-! # Local comparison, formal unramifiedness and sheaf assembly
Implication from the explicit inputs to the stated local comparisons.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MvPolynomial
open Filter Topology Manifold HodgeLean.Adapters
open HodgeLean.Foundations.AnalyticDivisorAlgebraic4
open scoped BigOperators ContDiff Classical
namespace HodgeLean.Foundations.Program

/-- Injectivity of the analytic tangent map at every complex point gives formal unramifiedness.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.3, printed pp. 13–14; Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.5 and II.8. -/
theorem s2e_analytic_tangent_injective_formally_unramified
    (X Y : Over (Spec ↧ℂ)) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
    (f : X ⟶ Y)
    (ht : ∀ p : ComplexPoint X,
      Function.Injective (fderiv ℂ (fun z : Fin d → ℂ =>
        ComplexPoint.localChart Y e (Point.map f p)
          (Point.map f ((ComplexPoint.localChart X d p).symm
            (ComplexPoint.localChart X d p p + z)))) 0)) :
    FormallyUnramified f.left :=
  s2e_analytic_tangent_injective_formally_unramified_aux X Y d e f ht

example := @s2e_analytic_tangent_injective_formally_unramified

/-- Equality on affine neighbourhoods of all complex points detects equality of actual ideal sheaves.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.3, printed pp. 13–14; Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.5 and II.8. -/
theorem s2e_ideal_sheaf_eq_on_complex_neighbourhoods
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (I J : X.left.IdealSheafData)
    (h : ∀ p : ComplexPoint X, ∃ U : X.left.affineOpens,
      ∃ hp : p.underlying ∈ U.1,
        Ideal.map (X.left.presheaf.germ U.1 p.underlying hp).hom (I.ideal U) =
          Ideal.map (X.left.presheaf.germ U.1 p.underlying hp).hom (J.ideal U)) : I = J :=
  s2e_ideal_sheaf_eq_on_complex_neighbourhoods_aux X I J h

example := @s2e_ideal_sheaf_eq_on_complex_neighbourhoods

/-- The actual vanishing ideal of a projective linear hyperplane has its normalized linear local equation.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.3, printed pp. 13–14; Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.5 and II.8. -/
theorem s2e_projective_linear_hyperplane_local_generator
    (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (k d : ℕ) (hd : Module.finrank ℂ V = k + 1)
    [SmoothOfRelativeDimension d
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom]
    (L : V →ₗ[ℂ] ℂ) (hL : L ≠ 0)
    (p : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))))
    (a : (Fin d → ℂ) → (Fin (k + 1) → ℂ)) (ha : AnalyticAt ℂ a 0)
    (hlift :
      let ep := s2e_finiteDimensionalProjectivePointEquiv (V := V) k hd
      let b := Module.finBasisOfFinrankEq ℂ V hd
      ∀ᶠ z in 𝓝 0, ∃ hz : (∑ i, a z i • b i) ≠ 0,
        ep.symm ((ComplexPoint.localChart
          (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) d p).symm
          (ComplexPoint.localChart
            (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) d p p + z)) =
          Projectivization.mk ℂ (∑ i, a z i • b i) hz) :
    let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    let ep := s2e_finiteDimensionalProjectivePointEquiv (V := V) k hd
    let b := Module.finBasisOfFinrankEq ℂ V hd
    let H : PP.left.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Point.underlying ''
        {R : ComplexPoint PP | ∃ (v : V) (hv : v ≠ 0),
          ep.symm R = Projectivization.mk ℂ v hv ∧ L v = 0}))
    ∃ (U : PP.left.affineOpens) (_hp : p.underlying ∈ U.1)
      (c : Γ(PP.left, U.1)) (η : (Fin d → ℂ) → ℂ),
      H.ideal U = Ideal.span {c} ∧ AnalyticAt ℂ η 0 ∧ η 0 ≠ 0 ∧
      (∀ᶠ z in 𝓝 0,
        Point.evaluate U.1 c ((ComplexPoint.localChart PP d p).symm
          (ComplexPoint.localChart PP d p p + z)) = η z * L (∑ i, a z i • b i)) :=
  s2e_projective_linear_hyperplane_local_generator_aux V k d hd L hL p a ha hlift

example := @s2e_projective_linear_hyperplane_local_generator

end HodgeLean.Foundations.Program
