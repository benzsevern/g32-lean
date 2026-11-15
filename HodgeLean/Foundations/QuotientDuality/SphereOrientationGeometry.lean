import Mathlib.Topology.Compactification.OnePoint.Sphere
import HodgeLean.Foundations.QuotientDuality.LocalTraceDefs
import HodgeLean.Foundations.Program.HurwitzPrymCovSphere
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSurfaceFundamentalClass
import HodgeLean.Foundations.Semialgebraic.CompatibleTriangulation
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.LocalHomologyVanishing

/-! Finite triangulation and normalized rational orientation of the two-sphere. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Program
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.QuotientDuality

private theorem chart_local_vanishing {M : Type} [TopologicalSpace M] [T1Space M]
    (d : ℕ) (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source)
    (i : ℕ) (hi : i ≠ 2 * d) :
    Subsingleton (RelativeHomology ℚ (pointComplementPair x) i) := by
  have ht : Function.Bijective
      (relativeHomologyMap ℚ i (standardComplexChartTargetPairIso d e x hx).hom) :=
    (ConcreteCategory.isIso_iff_bijective
      ((relativeHomologyFunctor ℚ i).map (standardComplexChartTargetPairIso d e x hx).hom)).mp
      inferInstance
  have he := b6m_point_excision_bijective ℚ
    (chartModelEmbedding d e x hx).target x (chartModelEmbedding d e x hx).open_target
    (chartModelEmbedding_mem_target d e x hx) i
  have hsur : Function.Surjective (relativeHomologyMap ℚ i
      (chartModelEmbeddingPair d e x hx)) := by
    rw [← standardComplexChartTargetPairIso_hom_comp_neighborhoodMap d e x hx,
      relativeHomologyMap_comp]
    exact (he.comp ht).2
  letI := ModuleCat.subsingleton_of_isZero (standardComplexLocalHomology_isZero_of_ne d i hi)
  exact hsur.subsingleton

theorem sphere_finite_triangulation :
    ∃ (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
      K.faces.Finite ∧ Nonempty (K.space ≃ₜ OnePoint ℂ) := by
  let P : MvPolynomial (Fin 3) ℝ := (∑ i, MvPolynomial.X i ^ 2) - 1
  let f : s2v_t11b_Formula 3 := .inter (.nonneg P) (.nonneg (-P))
  have hf : f.realize = Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) (1 : ℝ) := by
    ext x
    have hp : MvPolynomial.eval (fun i => x i) P = ‖x‖ ^ 2 - 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      change MvPolynomial.eval (fun i => x i) ((∑ i : Fin 3, MvPolynomial.X i ^ 2) - MvPolynomial.C (1 : ℝ)) = _
      simp only [MvPolynomial.eval_sub, MvPolynomial.eval_sum, MvPolynomial.eval_pow,
        MvPolynomial.eval_X, MvPolynomial.eval_C]

    change (0 ≤ MvPolynomial.eval (fun i => x i) P ∧
      0 ≤ MvPolynomial.eval (fun i => x i) (-P)) ↔ _
    rw [MvPolynomial.eval_neg, hp]
    rw [Metric.mem_sphere, dist_zero_right]
    constructor
    · intro h
      nlinarith [norm_nonneg x]
    · intro h
      rw [h]
      norm_num
  have hc : IsCompact f.realize := by
    rw [hf]
    exact isCompact_sphere 0 1
  obtain ⟨K, hK, eK, _, _⟩ :=
    Semialgebraic.CompatibleTriangulation.compact_compatible_triangulation 3 f hc
      (fun i : Fin 0 => Fin.elim0 i)
  let e : OnePoint ℂ ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) (1 : ℝ) :=
    onePointEquivSphereOfFinrankEq (by simp)
  exact ⟨K, hK, ⟨eK.trans ((Homeomorph.setCongr hf).trans e.symm)⟩⟩

attribute [local instance] b4cov_sphChartedSpace

def sphereLocalOrientation : LocalRationalOrientation (TopCat.of (OnePoint ℂ)) 2 := by
  letI : IsManifold 𝓘(ℂ, ℂ) 1 (OnePoint ℂ) :=
    b4cov_sph_isManifold.of_le (by simp)
  exact
    { generator := b6m_surfaceLocalClass ℚ
      generates := b6m_surfaceLocalClass_smul_bijective ℚ
      vanishes := fun x i hi => chart_local_vanishing 1 (b6m_surfaceChart x) x
        (by simpa only [b6m_surfaceChart_source] using mem_chart_source ℂ x) i hi
      coherent := b6m_surfaceLocalClass_neighborhood ℚ }

theorem sphereLocalOrientation_generator (x : OnePoint ℂ) :
    sphereLocalOrientation.generator x = b6m_surfaceLocalClass ℚ x := rfl

theorem sphere_surface_fundamental :
    ∃ c : Homology ℚ (TopCat.of (OnePoint ℂ)) 2,
      (∀ x, localOrientation (TopCat.of (OnePoint ℂ)) 2 c x =
        sphereLocalOrientation.generator x) ∧
      Function.Bijective (fun q : ℚ => q • c) := by
  letI : IsManifold 𝓘(ℂ, ℂ) 1 (OnePoint ℂ) :=
    b4cov_sph_isManifold.of_le (by simp)
  exact b6m_surface_fundamental_generator ℚ (C := OnePoint ℂ)

theorem sphere_orientation_geometry :
    ∃ (o : LocalRationalOrientation (TopCat.of (OnePoint ℂ)) 2)
      (c : Homology ℚ (TopCat.of (OnePoint ℂ)) 2),
      (∀ x, localOrientation (TopCat.of (OnePoint ℂ)) 2 c x = o.generator x) ∧
      Function.Bijective (fun q : ℚ => q • c) := by
  obtain ⟨c, hc, hg⟩ := sphere_surface_fundamental
  exact ⟨sphereLocalOrientation, c, hc, hg⟩

#print axioms sphere_finite_triangulation
#print axioms sphere_orientation_geometry
end HodgeLean.Foundations.QuotientDuality
