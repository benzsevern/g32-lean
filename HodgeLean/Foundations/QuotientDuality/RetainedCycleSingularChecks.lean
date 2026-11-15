import HodgeLean.Foundations.QuotientDuality.RetainedCycleDefs
import HodgeLean.Foundations.Analytic.Analytification
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.StandardEtale
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Localization
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Local.Purity
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator

/-! # Intrinsic coordinates along the singular axis of a cusp cylinder

The reduced axis has its own complex coordinate despite the ambient cusp singularity.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Foundations.Program HodgeLean.Foundations.Analytic
open AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.QuotientDuality.RetainedCycleSingularChecks

private abbrev R := Polynomial ℂ
private def cusp : WeierstrassCurve R := ⟨0, 0, 0, 0, 0⟩
private abbrev A := cusp.toAffine.CoordinateRing
private abbrev I := WeierstrassCurve.Affine.CoordinateRing.XYIdeal cusp.toAffine 0 0
private abbrev B := A ⧸ I
private def axisEquiv : B ≃ₐ[R] R :=
  WeierstrassCurve.Affine.CoordinateRing.quotientXYIdealEquiv
    (W' := cusp.toAffine) (x := 0) (y := 0) (by
      simp [WeierstrassCurve.Affine.polynomial, cusp])
private instance cuspComplexAlgebra : Algebra ℂ A :=
  ((algebraMap R A).comp (algebraMap ℂ R)).toAlgebra
private instance axisDomain : IsDomain B := MulEquiv.isDomain R axisEquiv.toRingEquiv.toMulEquiv
private abbrev ambient : Over (Spec ↧ℂ) := Over.mk (affineSpecStructureMap A)
private abbrev axis : Over (Spec ↧ℂ) := Over.mk (affineSpecStructureMap B)
private instance ambientIntegral : IsIntegral ambient.left := by
  change IsIntegral (Spec (CommRingCat.of A)); infer_instance
private instance axisIntegral : IsIntegral axis.left := by
  change IsIntegral (Spec (CommRingCat.of B)); infer_instance
private def axisInclusion : axis ⟶ ambient :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl)
private instance axisInclusionClosed : IsClosedImmersion axisInclusion.left := by
  dsimp [axisInclusion]
  exact IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.mk_surjective)

private theorem reducedClosedKernel {Z X : Scheme.{0}} [IsReduced Z]
    (f : Z ⟶ X) [IsClosedImmersion f] : f.ker.radical = f.ker := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  change (Ideal.comap (f.app U).hom ⊥).radical = Ideal.comap (f.app U).hom ⊥
  rw [← Ideal.comap_radical, Ideal.radical_eq_iff.mpr Ideal.isRadical_bot]

private theorem range_generic {Z X : Scheme.{0}} [IsIntegral Z]
    (f : Z ⟶ X) [IsClosedImmersion f] :
    Set.range f = closure {f (genericPoint Z)} := by
  rw [← Set.image_singleton, f.isClosedMap.closure_image_eq_of_continuous f.continuous,
    genericPoint_closure, Set.image_univ]

private def componentIso {Z X : Scheme.{0}} [IsIntegral Z]
    (f : Z ⟶ X) [IsClosedImmersion f] :
    Z ≅ cycleComponent X (f (genericPoint Z)) := by
  let i := cycleComponentι X (f (genericPoint Z))
  have he : i.ker = f.ker := by
    change (Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {f (genericPoint Z)}, isClosed_closure⟩).subschemeι.ker = f.ker
    rw [Scheme.IdealSheafData.ker_subschemeι]
    rw [← reducedClosedKernel f, ← Scheme.IdealSheafData.vanishingIdeal_support]
    congr 1
    apply TopologicalSpace.Closeds.ext
    change closure {f (genericPoint Z)} = (f.ker.support : Set X)
    rw [Scheme.Hom.support_ker, ← range_generic f, f.isClosedMap.isClosed_range.closure_eq]
  let g := IsClosedImmersion.lift i f he.le
  letI : IsIso g := IsClosedImmersion.isIso_lift i f he
  exact asIso g

private theorem componentIso_fac {Z X : Scheme.{0}} [IsIntegral Z]
    (f : Z ⟶ X) [IsClosedImmersion f] :
    (componentIso f).hom ≫ cycleComponentι X (f (genericPoint Z)) = f := by
  dsimp only [componentIso, asIso_hom]
  exact IsClosedImmersion.lift_fac _ _ _

private abbrev intrinsicAxis := intrinsicComponent ambient
  (axisInclusion.left (genericPoint axis.left))
private def axisOverIso : axis ≅ intrinsicAxis :=
  Over.isoMk (componentIso axisInclusion.left) (by
    change (componentIso axisInclusion.left).hom ≫
      (cycleComponentι ambient.left (axisInclusion.left (genericPoint axis.left)) ≫ ambient.hom) = axis.hom
    rw [← Category.assoc, componentIso_fac]
    exact Over.w axisInclusion)

private def axisPolynomialEquiv : B ≃ₐ[ℂ] MvPolynomial (Fin 1) ℂ := by
  let e : B ≃ₐ[ℂ] R :=
    { axisEquiv.toRingEquiv with
      commutes' := fun c => by
        change axisEquiv (algebraMap R B (Polynomial.C c)) = Polynomial.C c
        exact axisEquiv.commutes (Polynomial.C c) }
  exact e.trans (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm
private def axisCoordinates : ComplexPoint axis ≃ₜ (Fin 1 → ℂ) :=
  (affineSpecHomeomorph B).trans
    ((ComplexAlgHom.precompAlgEquivHomeomorph axisPolynomialEquiv).symm.trans
      (ComplexAlgHom.mvPolynomialAlgHomHomeomorph 1))
private def intrinsicCoordinates : ComplexPoint intrinsicAxis ≃ₜ (Fin 1 → ℂ) :=
  (Point.isoMapHomeomorph axisOverIso).symm.trans axisCoordinates
private instance intrinsicAxisT2 : T2Space (ComplexPoint intrinsicAxis) :=
  intrinsicCoordinates.isEmbedding.t2Space
private def axisChart := intrinsicCoordinates.toOpenPartialHomeomorph
private def axisOrigin := intrinsicCoordinates.symm (0 : Fin 1 → ℂ)
private def axisLocalClass := localClassOfChart 1 axisChart axisOrigin (Set.mem_univ _)
private theorem axisLocalClass_ne_zero : axisLocalClass ≠ 0 :=
  localClassOfChart_ne_zero 1 axisChart axisOrigin (Set.mem_univ _)
private def axisNormalized := normalizedRelativeCoclass axisLocalClass axisLocalClass_ne_zero
private theorem axisNormalization :
    relativeCohomologyEquivDualHomology ℚ (pointComplementPair axisOrigin) 2
      axisNormalized axisLocalClass = 1 := by
  rw [axisNormalized, relativeCohomologyEquivDualHomology_normalizedRelativeCoclass,
    normalizedDual_apply_self]

/-- The singular cusp axis is an actual integral reduced component, and its coordinate quotient
is a polynomial line. Ambient nonsingularity cannot replace its intrinsic normalization.
Source: Hartshorne, Algebraic Geometry, I.5, cusp; II.3, reduced induced subschemes.
HC no distance; AV milestone no distance. -/
theorem check_singular_axis :
    Nonempty (axis.left ≅ (intrinsicComponent ambient
      (axisInclusion.left (genericPoint axis.left))).left) ∧
    Nonempty (B ≃ₐ[R] Polynomial ℂ) ∧
    (∀ t : ℂ, ¬ (cusp.map (Polynomial.evalRingHom t)).toAffine.Nonsingular 0 0) ∧
    axisEquiv.symm (Polynomial.X : Polynomial ℂ) ≠ 0 ∧
    relativeCohomologyEquivDualHomology ℚ (pointComplementPair axisOrigin) 2
      axisNormalized axisLocalClass = 1 ∧
    relativeCohomologyEquivDualHomology ℚ (pointComplementPair axisOrigin) 2
      axisNormalized axisLocalClass ≠ -1 := by
  refine ⟨⟨componentIso axisInclusion.left⟩, ⟨axisEquiv⟩, ?_, ?_⟩
  · intro t
    simp [WeierstrassCurve.Affine.nonsingular_zero, cusp, WeierstrassCurve.map]
  · refine ⟨?_, axisNormalization, ?_⟩
    · intro h
      have he := congrArg axisEquiv h
      exact Polynomial.X_ne_zero (by simpa only [AlgEquiv.apply_symm_apply, map_zero] using he)
    · rw [axisNormalization]
      norm_num
example := check_singular_axis

end HodgeLean.Foundations.QuotientDuality.RetainedCycleSingularChecks
