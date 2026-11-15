import HodgeLean.Foundations.QuotientDuality.ModificationComplexLocalDegree
import HodgeLean.Foundations.QuotientDuality.LocalChartDimension
import HodgeLean.Foundations.Program.SchoenTowerComplexPointsExist
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Locus
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional

/-! A nonempty algebraic isomorphism domain supplies a normalized local degree witness. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Foundations.Analytic HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

theorem exists_singletonFibre_complex_local_degree
    (A X Y : Over (Spec ↧ℂ)) [IsIntegral A.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (d : ℕ)
    (oX : LocalRationalOrientation (TopCat.of (ComplexPoint X)) (2 * d))
    (oY : LocalRationalOrientation (TopCat.of (ComplexPoint Y)) (2 * d))
    (hnX : ∀ (x : ComplexPoint X)
      (E : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ)) (hx : x ∈ E.source),
      (∀ i, (f4_analytification X).IsHolFun (fun y : E.source => E y i)) →
      oX.generator x = localClassOfChart d E x hx)
    (hnY : ∀ (y : ComplexPoint Y)
      (E : OpenPartialHomeomorph (ComplexPoint Y) (Fin d → ℂ)) (hy : y ∈ E.source),
      (∀ i, (f4_analytification Y).IsHolFun (fun z : E.source => E z i)) →
      oY.generator y = localClassOfChart d E y hy)
    (j : A ⟶ X) [IsOpenImmersion j.left] (f : X ⟶ Y)
    [IsOpenImmersion (j ≫ f).left]
    (hsing : ∀ z : ComplexPoint A, ∀ x,
      Point.map f x = Point.map f (Point.map j z) → x = Point.map j z) :
    ∃ (x : ComplexPoint X)
      (hf : ∀ z, Point.map f z = Point.map f x → z = x),
      relativeHomologyMap ℚ (2 * d)
        (singletonFibrePairMap (TopCat.ofHom (Point.continuousMap f)) x (Point.map f x) hf)
        (oX.generator x) = oY.generator (Point.map f x) := by
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  letI : LocallyOfFiniteType A.hom := by
    rw [← Over.w j]
    infer_instance
  let U := A.hom.smoothLocus
  obtain ⟨a, ha⟩ := A.hom.dense_smoothLocus_of_perfectField.nonempty
  letI : Nonempty U := ⟨⟨a, ha⟩⟩
  let S := openScheme A U
  letI : Nonempty S.left := inferInstanceAs (Nonempty U)
  letI : IsIntegral S.left := isIntegral_of_isOpenImmersion U.ι
  letI : Smooth S.hom := A.hom.smooth_restrict_smoothLocus
  letI : LocallyOfFiniteType S.hom := by
    change LocallyOfFiniteType (U.ι ≫ A.hom)
    infer_instance
  obtain ⟨s⟩ := s2t_nonempty_complexPoints S
  let j' := openInclusion A U ≫ j
  letI : IsOpenImmersion j'.left := inferInstanceAs (IsOpenImmersion (U.ι ≫ j.left))
  letI : IsOpenImmersion (j' ≫ f).left := by
    change IsOpenImmersion ((U.ι ≫ j.left) ≫ f.left)
    rw [Category.assoc]
    infer_instance
  let k := TopologicalSpace.dim S.left
  let E := (localChart S k s).lift_openEmbedding
    (HodgeLean.Foundations.ComplexTopology.openImmersion_points j')
  have hE : Point.map j' s ∈ E.source := ⟨s, mem_localChart_source S k s, rfl⟩
  have hdim : d = k := by
    have he := localOrientation_degree_eq_chart_dimension (TopCat.of (ComplexPoint X))
      (2 * d) oX k E (Point.map j' s) hE
    omega
  letI : SmoothOfRelativeDimension d S.hom := by rw [hdim]; infer_instance
  have hf : ∀ x, Point.map f x = Point.map f (Point.map j' s) → x = Point.map j' s := by
    simpa only [j', Point.map_comp_apply] using hsing (Point.map (openInclusion A U) s)
  exact ⟨Point.map j' s, hf,
    singletonFibre_map_complex_generators S X Y d oX oY hnX hnY j' f s hf⟩

#print axioms exists_singletonFibre_complex_local_degree
end HodgeLean.Foundations.QuotientDuality
