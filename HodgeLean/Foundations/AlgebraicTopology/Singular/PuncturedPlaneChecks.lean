import HodgeLean.Foundations.Program.SchoenTowerL1bActionBallDegree
import HodgeLean.Foundations.AlgebraicTopology.Singular.PuncturedPlaneDefs

/-! Integral winding and local-degree checks.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters
open scoped Manifold ContDiff
open Complex
open scoped ComplexConjugate
namespace AlgebraicTopology.Singular.PuncturedPlane

-- These checks import only definitions and existing checked infrastructure.
example (c : ℂ) (k : ℤ) (s : ℝ) :
    (windingCircle c k (s : UnitAddCircle)).val =
      Complex.exp (c + (s : ℂ) * ((k : ℂ) * (2 * Real.pi * Complex.I))) := rfl

example (s : ℝ) :
    (windingCircle 0 (-1) (s : UnitAddCircle)).val =
      Complex.exp (-(s : ℂ) * (2 * Real.pi * Complex.I)) := by
  change Complex.exp (0 + (s : ℂ) * (((-1 : ℤ) : ℂ) * _)) = _
  congr 1
  simp only [Int.cast_neg, Int.cast_one, one_mul, zero_add, mul_neg, neg_mul]

example (c : ℂ) (k : ℤ) (t : UnitAddCircle) :
    ‖(windingCircle c k t).val‖ = Real.exp c.re :=
  HodgeLean.Foundations.Program.s2v_l1b_action_windingCircleMap_norm c k t

example (r ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ < r) :
    (neighborhoodPointComplementPairMap (Metric.ball (0 : ℂ) r) 0).left.hom.comp
      (HodgeLean.Foundations.Program.s2v_l1b_action_ball_loop r ρ hρ hρr) =
    windingCircle (ρ.log : ℂ) 1 := rfl

example {M : Type} [TopologicalSpace M] [T1Space M] [ChartedSpace ℂ M]
    (x : M) (n : ℤ) : localCoefficient x (n • localClass x) = n := by
  rw [← int_smul_eq_zsmul (ModuleCat.isModule _) n (localClass x)]
  exact (Equiv.ofBijective _
    (HodgeLean.Foundations.Program.b6m_surfaceLocalClass_smul_bijective ℤ x)).symm_apply_apply n

-- Negative integral winding is checked at the homology-class level as well.
example :
    ((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
      (loopCycle ℤ (windingCircle 0 (-1))) =
    (-1 : ℤ) • ((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
      (loopCycle ℤ (windingCircle 0 1)) :=
  HodgeLean.Foundations.Program.s2v_l1b_action_winding_loop_class (-1)

open HodgeLean.Foundations.Program

-- Compatibility with the historical definitions is reduction, not a new comparison.
example (c : ℂ) (k : ℤ) : windingCircle c k = s2v_l1b_action_windingCircleMap c k := rfl

example (x : ℂ) : localClass x = b6m_surfaceLocalClass ℤ x := rfl

-- Disk inclusion: the radius-two neighborhood contains a radius-one generator.
example : Function.Bijective (homologyMap ℤ 1
    (neighborhoodPointComplementPairMap (Metric.ball (0 : ℂ) 2) 0).left) :=
  s2v_l1b_action_ball_homology_bijective 2 (by norm_num)

private abbrev positiveClass :=
  ((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
    (loopCycle ℤ (windingCircle 0 1))

private theorem positiveClass_ne_zero : positiveClass ≠ 0 := by
  intro hz
  let b := (b6m_relativeSingularBoundary ℤ (pointComplementPair (0 : ℂ)) 1).hom
    (localClass (0 : ℂ))
  obtain ⟨n, hn⟩ := s2v_l1b_action_winding_class_smul_surjective b
  have hb : b = 0 := by
    change n • positiveClass = b at hn
    rw [hz, zsmul_zero] at hn
    exact hn.symm
  have h := s2v_l1b_action_plane_boundary_generator.1
    (show (1 : ℤ) • b = (0 : ℤ) • b by rw [hb, zsmul_zero, zsmul_zero])
  exact one_ne_zero h

example : positiveClass ≠ 0 := positiveClass_ne_zero

-- The relative boundary comparison is tested on a nonzero local class.
example : (b6m_relativeSingularBoundary ℤ (pointComplementPair (0 : ℂ)) 1).hom
    (localClass (0 : ℂ)) ≠ 0 := by
  intro h
  have he := s2v_l1b_action_plane_boundary_generator.1
    (show (1 : ℤ) • _ = (0 : ℤ) • _ by rw [h, zsmul_zero, zsmul_zero])
  exact one_ne_zero he

private theorem degree_transport {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [T1Space N] [ChartedSpace ℂ M] [ChartedSpace ℂ N] (e : M ≃ₜ N) (x : M) :
    relativeHomologyMap ℤ 2
      (imagePointPairMap (TopCat.ofHom ⟨e, e.continuous⟩) e.injective x) (localClass x) =
        localDegree e x • localClass (e x) := by
  rw [← int_smul_eq_zsmul (ModuleCat.isModule _) (localDegree e x)]
  exact ((Equiv.ofBijective _ (b6m_surfaceLocalClass_smul_bijective ℤ (e x))).apply_symm_apply _).symm

private def imagePairAt {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (e : M ≃ₜ N) (x : M) (y : N) (h : e x = y) :
    pointComplementPair x ⟶ pointComplementPair y :=
  imagePointPairMap (TopCat.ofHom ⟨e, e.continuous⟩) e.injective x ≫
    eqToHom (congrArg pointComplementPair h)

private theorem imagePairAt_left {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (e : M ≃ₜ N) (x : M) (y : N) (h : e x = y) (z : (pointComplementPair x).snd) :
    ((imagePairAt e x y h).left z).val = e z.val := by
  cases h
  rfl

private theorem degree_transport_at {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [T1Space N] [ChartedSpace ℂ M] [ChartedSpace ℂ N]
    (e : M ≃ₜ N) (x : M) (y : N) (h : e x = y) :
    relativeHomologyMap ℤ 2 (imagePairAt e x y h) (localClass x) =
      localDegree e x • localClass y := by
  cases h
  unfold imagePairAt
  rw [eqToHom_refl, Category.comp_id]
  exact degree_transport e x

private theorem conjugation_degree : localDegree Complex.conjCLE.toHomeomorph 0 = -1 := by
  let e := Complex.conjCLE.toHomeomorph
  have he0 : e 0 = 0 := map_zero Complex.conjCLE
  let F := imagePairAt e 0 0 he0
  have ht := degree_transport_at e 0 0 he0
  have h : (-1 : ℤ) = localDegree e 0 := s2v_l1b_action_deck_local_sign
    F (fun z : ℂ => conj z) Complex.continuous_conj ?_ (-1) ?_
    (localDegree e 0) ht
  · exact h.symm
  · intro z
    rw [show (F.left ⟨Complex.exp z, Complex.exp_ne_zero z⟩).val = e (Complex.exp z) from
      imagePairAt_left e 0 0 he0 _]
    exact Complex.exp_conj z
  · intro z
    simp only [map_add, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
      Int.cast_neg, Int.cast_one, neg_one_mul, mul_neg]

example : localDegree Complex.conjCLE.toHomeomorph 0 = -1 := conjugation_degree

-- Sign and constancy examples for both public and auxiliary interfaces.
example : localDegree Complex.conjCLE.toHomeomorph 0 = 1 ∨
    localDegree Complex.conjCLE.toHomeomorph 0 = -1 := Or.inr conjugation_degree

example : relativeHomologyMap ℤ 2
    (imagePointPairMap
      (TopCat.ofHom ⟨Complex.conjCLE.toHomeomorph, Complex.conjCLE.continuous⟩)
      Complex.conjCLE.toHomeomorph.injective 0) (localClass (0 : ℂ)) =
      (-1 : ℤ) • localClass (Complex.conjCLE.toHomeomorph (0 : ℂ)) := by
  rw [degree_transport, conjugation_degree]

end AlgebraicTopology.Singular.PuncturedPlane
