import HodgeLean.Foundations.Program.SchoenCycleProjectiveHyperplaneIdeal
import HodgeLean.Foundations.Program.SchoenCycleProjectiveAnalyticLift
import HodgeLean.Foundations.Program.SchoenCycleS1j3
import HodgeLean.Foundations.Program.SchoenCycleFiniteUnramified
import HodgeLean.Foundations.Program.SchoenCycleIdealClosedPointDetection
import HodgeLean.Foundations.Program.SchoenCycleRelativeUnramifiedNeighbourhood
import HodgeLean.Foundations.Program.SchoenCycleUnramifiedBasicOpen
import HodgeLean.Foundations.Program.SchoenCycleUnramifiedComplexDetection

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
theorem s2e_analytic_tangent_injective_formally_unramified_aux
    (X Y : Over (Spec ↧ℂ)) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
    (f : X ⟶ Y)
    (ht : ∀ p : ComplexPoint X,
      Function.Injective (fderiv ℂ (fun z : Fin d → ℂ =>
        ComplexPoint.localChart Y e (Point.map f p)
          (Point.map f ((ComplexPoint.localChart X d p).symm
            (ComplexPoint.localChart X d p p + z)))) 0)) :
    FormallyUnramified f.left := by
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth (n := d) X.hom
  apply s2e_formallyUnramified_of_complex_affine_neighbourhoods X Y f
  intro p
  let DX := ComplexPoint.localEtaleCoordinates X d p
  let DY := ComplexPoint.localEtaleCoordinates Y e (Point.map f p)
  have hpY : f.left p.underlying ∈ DY.neighborhood := by
    simpa only [Point.underlying_map] using DY.mem
  obtain ⟨W, hW, hpW, hsub⟩ := exists_isAffineOpen_mem_and_subset
    (show p.underlying ∈ DX.neighborhood ⊓ f.left ⁻¹ᵁ DY.neighborhood from ⟨DX.mem, hpY⟩)
  have hWX : W ≤ DX.neighborhood := fun _ hx => (hsub hx).1
  have hWY : W ≤ f.left ⁻¹ᵁ DY.neighborhood := fun _ hx => (hsub hx).2
  obtain ⟨a, ha, hu⟩ := s2e_relative_unramified_localization_neighbourhood
    X Y d e f p ⟨W, hW⟩ hpW hWX hWY (ht p)
  have hane : Point.evaluate W a p ≠ 0 := by
    rw [s2e_regular_evaluation_eq_pointEvaluation X W p hpW
      (s2e_step1_point_preimage X p W hpW)]
    exact ha
  have hpB : p.underlying ∈ X.left.basicOpen a :=
    (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero a p hpW).mpr hane
  refine ⟨⟨DY.neighborhood, DY.isAffine⟩, ⟨X.left.basicOpen a, hW.basicOpen a⟩,
    hpB, (X.left.basicOpen_le a).trans hWY, ?_⟩
  exact s2e_formallyUnramified_appLE_basicOpen X.left Y.left f.left
    ⟨DY.neighborhood, DY.isAffine⟩ ⟨W, hW⟩ hWY a hu

/-- Equality on affine neighbourhoods of all complex points detects equality of actual ideal sheaves.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.3, printed pp. 13–14; Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.5 and II.8. -/
theorem s2e_ideal_sheaf_eq_on_complex_neighbourhoods_aux
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (I J : X.left.IdealSheafData)
    (h : ∀ p : ComplexPoint X, ∃ U : X.left.affineOpens,
      ∃ hp : p.underlying ∈ U.1,
        Ideal.map (X.left.presheaf.germ U.1 p.underlying hp).hom (I.ideal U) =
          Ideal.map (X.left.presheaf.germ U.1 p.underlying hp).hom (J.ideal U)) : I = J := by
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hh (U : X.left.affineOpens) (x : X.left) (hxU : x ∈ U.1)
      (hc : IsClosed ({x} : Set X.left)) :
      Ideal.map (X.left.presheaf.germ U.1 x hxU).hom (I.ideal U) =
        Ideal.map (X.left.presheaf.germ U.1 x hxU).hom (J.ideal U) := by
    obtain ⟨p, hp⟩ : ∃ p : ComplexPoint X, p.underlying = x :=
      ⟨Over.homMk (pointOfClosedPoint X.hom x hc) (by simp),
        pointOfClosedPoint_apply X.hom x hc _⟩
    subst x
    obtain ⟨V, hxV, he⟩ := h p
    exact (s2e_ideal_stalk_affine_chart_independent I U V _ hxU hxV).trans
      (he.trans (s2e_ideal_stalk_affine_chart_independent J U V _ hxU hxV).symm)
  apply Scheme.IdealSheafData.ext
  funext U
  exact le_antisymm
    (s2e_affine_ideal_le_of_closed_stalks U (I.ideal U) (J.ideal U)
      (fun x hx hc => (hh U x hx hc).le))
    (s2e_affine_ideal_le_of_closed_stalks U (J.ideal U) (I.ideal U)
      (fun x hx hc => (hh U x hx hc).ge))

/-- The actual vanishing ideal of a projective linear hyperplane has its normalized linear local equation.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Lemma 2.3, printed pp. 13–14; Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.5 and II.8. -/
theorem s2e_projective_linear_hyperplane_local_generator_aux
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
          (ComplexPoint.localChart PP d p p + z)) = η z * L (∑ i, a z i • b i)) := by
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  let r : (Fin d → ℂ) → ComplexPoint PP := fun z =>
    (ComplexPoint.localChart PP d p).symm (ComplexPoint.localChart PP d p p + z)
  obtain ⟨i, η, hp0, hη, hη0, heq⟩ :=
    s2e_standardProjectiveLinearSection_analytic_lift V k d hd L r a ha hlift
  have hr0 : r 0 = p := by
    dsimp only [r]
    rw [add_zero]
    exact (ComplexPoint.localChart PP d p).left_inv (ComplexPoint.mem_localChart_source PP d p)
  refine ⟨s2e_standardProjectiveAffineOpen i, ?_,
    s2e_standardProjectiveLinearSection V k hd L i, η, ?_, hη, hη0, heq⟩
  · rwa [hr0] at hp0
  · letI : Smooth PP.hom := SmoothOfRelativeDimension.smooth (n := d) PP.hom
    exact s2e_projective_hyperplane_chart_ideal V k hd L i

end HodgeLean.Foundations.Program
