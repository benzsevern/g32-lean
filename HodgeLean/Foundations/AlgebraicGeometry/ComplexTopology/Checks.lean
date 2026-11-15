import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Defs
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Algebra.Group.Basic
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineSpace
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open

/-! Independent tests of singular carriers, small neighborhoods and map transport.
HC no distance; AV milestone no distance. -/

noncomputable section
open Topology
namespace HodgeLean.Foundations.ComplexTopology

-- Both branches of a crossing survive, and a point off the crossing does not.
example :
    (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0) ∈
      zeroSet (fun _ : Fin 1 => MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1) ∧
    (fun i : Fin 2 => if i = 0 then (0 : ℂ) else 1) ∈
      zeroSet (fun _ : Fin 1 => MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1) ∧
    (fun _ : Fin 2 => (1 : ℂ)) ∉
      zeroSet (fun _ : Fin 1 => MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1) := by
  simp [zeroSet]

-- A genuine open neighborhood in positive real dimension.
example : ContractibleSpace (Metric.ball (0 : ℂ) 1) :=
  (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, by simp⟩

-- Translation moves the basepoint and transports the open topology.
example : IsOpenEmbedding (fun z : ℂ => z + 1) ∧ (0 : ℂ) + 1 ≠ 0 := by
  exact ⟨(Homeomorph.addRight (1 : ℂ)).isOpenEmbedding, by norm_num⟩

-- A nonzero nilpotent relation has exactly the same point carrier as its radical.
example : zeroSet (fun _ : Fin 1 => (MvPolynomial.X (0 : Fin 1) :
      MvPolynomial (Fin 1) ℂ) ^ 2) =
    zeroSet (fun _ : Fin 1 => MvPolynomial.X (0 : Fin 1)) := by
  ext z
  simp [zeroSet]

private abbrev node := zeroSet (fun _ : Fin 1 =>
  MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1 : Fin 1 → MvPolynomial (Fin 2) ℂ)

private def origin : node := ⟨0, by simp [zeroSet]⟩

private lemma node_star : StarConvex ℝ (0 : Fin 2 → ℂ) node := by
  intro y hy a b ha hb hab
  have h : y 0 * y 1 = 0 := by simpa using hy 0
  rcases mul_eq_zero.mp h with h | h
  · simp [zeroSet, Pi.add_apply, Pi.smul_apply, h]
  · simp [zeroSet, Pi.add_apply, Pi.smul_apply, h]

private lemma node_ball (r : ℝ) (hr : 0 < r) :
    ContractibleSpace (Metric.ball origin r) := by
  let e : Metric.ball origin r ≃ₜ
      (node ∩ Metric.ball (0 : Fin 2 → ℂ) r : Set (Fin 2 → ℂ)) :=
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  letI : ContractibleSpace (node ∩ Metric.ball (0 : Fin 2 → ℂ) r : Set (Fin 2 → ℂ)) :=
    (node_star.inter ((convex_ball (0 : Fin 2 → ℂ) r).starConvex
    (by simpa using hr))).contractibleSpace ⟨0, by simp [zeroSet, hr]⟩
  exact e.contractibleSpace

/-- Every requested neighborhood of the crossing contains a contractible open ball.
Source: Munkres, Topology, §58; StarConvex.contractibleSpace. -/
theorem node_origin_basis_check (U : TopologicalSpace.Opens node) (h : origin ∈ U) :
    ∃ V : TopologicalSpace.Opens node,
      origin ∈ V ∧ ContractibleSpace V ∧ V ≤ U := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp U.isOpen origin h
  exact ⟨⟨Metric.ball origin r, Metric.isOpen_ball⟩, by simpa using hr,
    node_ball r hr, hsub⟩

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint

private abbrev plane := Over.mk (complexAffineSpace (Fin 2) ↘ Spec ↧ℂ)
private abbrev planeChart := affineSpaceHomeomorph (Fin 2)
private abbrev coord := AffineSpace.coord (Spec ↧ℂ) (0 : Fin 2)
private abbrev principal := plane.left.basicOpen coord

private lemma plane_eval (v : Fin 2 → ℂ) (i : Fin 2) :
    Point.evaluate ⊤ (AffineSpace.coord (Spec ↧ℂ) i) (planeChart.symm v) = v i := by
  rw [evaluate_top_eq_appTop]
  exact congrFun ((affineSpaceEquiv (Fin 2)).apply_symm_apply v) i

/-- Two coordinates are actual evaluations on an affine plane, with distinct values.
Source: Hartshorne, Algebraic Geometry, II.2; ComplexPoint.affineSpaceEquiv. -/
theorem affine_plane_coordinates_check : Point.evaluate ⊤ coord (planeChart.symm ![1, 2]) = 1 ∧
    Point.evaluate ⊤ (AffineSpace.coord (Spec ↧ℂ) (1 : Fin 2))
      (planeChart.symm ![1, 2]) = 2 := by
  constructor <;> apply plane_eval

private lemma principal_mem (v : Fin 2 → ℂ) :
    planeChart.symm v ∈ Point.overOpen principal ↔ v 0 ≠ 0 := by
  rw [Point.mem_overOpen_basicOpen_iff_isUnit_evaluate (X := plane) coord _ (by trivial), plane_eval]
  exact isUnit_iff_ne_zero

/-- The principal chart contains (1,2), and excludes the origin.
Source: Hartshorne, Algebraic Geometry, II.2; Point.mem_overOpen_basicOpen_iff_isUnit_evaluate. -/
theorem principal_open_membership_check : planeChart.symm ![1, 2] ∈ Point.overOpen principal ∧
    planeChart.symm 0 ∉ Point.overOpen principal := by
  constructor
  · exact (principal_mem _).mpr (by norm_num)
  · rw [principal_mem]; simp

/-- The actual principal inclusion has a proper image on complex points.
Source: Hartshorne, Algebraic Geometry, II.2; ComplexPoint.openHomeomorph. -/
theorem principal_open_points_check : IsOpenEmbedding (Point.map (openInclusion plane principal)) ∧
    ¬ Function.Surjective (Point.map (openInclusion plane principal)) := by
  refine ⟨isOpenEmbedding_map_open plane principal, ?_⟩
  intro h
  obtain ⟨x, hx⟩ := h (planeChart.symm 0)
  have hm := (openHomeomorph plane principal x).property
  change Point.map (openInclusion plane principal) x ∈ Point.overOpen principal at hm
  rw [hx, principal_mem] at hm
  exact hm rfl

private def small : TopologicalSpace.Opens (ComplexPoint plane) :=
  ⟨planeChart.symm '' Metric.ball (fun _ => (1 : ℂ)) (1 / 2 : ℝ),
    planeChart.symm.isOpenMap _ Metric.isOpen_ball⟩

private lemma small_contractible : ContractibleSpace small := by
  letI : ContractibleSpace (Metric.ball (fun _ : Fin 2 => (1 : ℂ)) (1 / 2 : ℝ)) :=
    (convex_ball _ _).contractibleSpace ⟨_, Metric.mem_ball_self (by norm_num)⟩
  exact (planeChart.symm.image _).symm.contractibleSpace

private lemma small_subset : (small : Set (ComplexPoint plane)) ⊆ Point.overOpen principal := by
  rintro z ⟨v, hv, rfl⟩
  apply (principal_mem v).mpr
  intro hz
  have hd := lt_of_le_of_lt (dist_le_pi_dist v (fun _ => (1 : ℂ)) 0) hv
  norm_num [hz] at hd

private lemma small_mem : planeChart.symm (fun _ => (1 : ℂ)) ∈ small := by
  exact ⟨_, Metric.mem_ball_self (by norm_num), rfl⟩

/-- Transport an actual contractible neighborhood through the proper principal chart.
Source: Munkres, Topology, §§16 and 25; ComplexPoint.openHomeomorph. -/
theorem principal_open_transport_check : ∃ (V : TopologicalSpace.Opens (ComplexPoint (openScheme plane principal)))
    (W : TopologicalSpace.Opens (ComplexPoint plane)),
    ContractibleSpace V ∧ ContractibleSpace W ∧
    (W : Set (ComplexPoint plane)) = Point.map (openInclusion plane principal) '' V ∧
    planeChart.symm (fun _ => (1 : ℂ)) ∈ W := by
  let f := Point.map (openInclusion plane principal)
  have hf := isOpenEmbedding_map_open plane principal
  have hr : (small : Set (ComplexPoint plane)) ⊆ Set.range f := by
    intro z hz
    exact ⟨(openHomeomorph plane principal).symm ⟨z, small_subset hz⟩,
      congrArg Subtype.val ((openHomeomorph plane principal).apply_symm_apply _)⟩
  let V : TopologicalSpace.Opens (ComplexPoint (openScheme plane principal)) :=
    ⟨f ⁻¹' small, small.isOpen.preimage hf.continuous⟩
  letI : ContractibleSpace small := small_contractible
  have hc : ContractibleSpace V := (hf.isEmbedding.homeomorphOfSubsetRange hr).contractibleSpace
  exact ⟨V, small, hc, small_contractible, (Set.image_preimage_eq_of_subset hr).symm, small_mem⟩

/-- Actual affine-plane points have a pointed contractible open basis.
Source: Munkres, Topology, §58; ComplexPoint.affineSpaceHomeomorph. -/
theorem affine_plane_basis_check (x : ComplexPoint plane)
    (U : TopologicalSpace.Opens (ComplexPoint plane)) (hx : x ∈ U) :
    ∃ V : TopologicalSpace.Opens (ComplexPoint plane),
      x ∈ V ∧ ContractibleSpace V ∧ V ≤ U := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp
    (planeChart.isOpenMap _ U.isOpen) (planeChart x) ⟨x, hx, rfl⟩
  let V : TopologicalSpace.Opens (ComplexPoint plane) :=
    ⟨planeChart.symm '' Metric.ball (planeChart x) r,
      planeChart.symm.isOpenMap _ Metric.isOpen_ball⟩
  letI : ContractibleSpace (Metric.ball (planeChart x) r) :=
    (convex_ball _ _).contractibleSpace ⟨_, Metric.mem_ball_self hr⟩
  refine ⟨V, ⟨planeChart x, Metric.mem_ball_self hr, planeChart.symm_apply_apply x⟩,
    (planeChart.symm.image _).symm.contractibleSpace, ?_⟩
  rintro z ⟨v, hv, rfl⟩
  obtain ⟨y, hy, heq⟩ := hsub hv
  change planeChart.symm v ∈ U
  rw [← heq, planeChart.symm_apply_apply]
  exact hy

example (U : TopologicalSpace.Opens node) (h : origin ∈ U) :
    ∃ V : TopologicalSpace.Opens node,
      origin ∈ V ∧ ContractibleSpace V ∧ V ≤ U :=
  node_origin_basis_check U h

example : Point.evaluate ⊤ coord (planeChart.symm ![1, 2]) = 1 ∧
    Point.evaluate ⊤ (AffineSpace.coord (Spec ↧ℂ) (1 : Fin 2))
      (planeChart.symm ![1, 2]) = 2 :=
  affine_plane_coordinates_check

example (x : ComplexPoint plane)
    (U : TopologicalSpace.Opens (ComplexPoint plane)) (hx : x ∈ U) :
    ∃ V : TopologicalSpace.Opens (ComplexPoint plane),
      x ∈ V ∧ ContractibleSpace V ∧ V ≤ U :=
  affine_plane_basis_check x U hx

example : IsOpenEmbedding (Point.map (openInclusion plane principal)) ∧
    ¬ Function.Surjective (Point.map (openInclusion plane principal)) :=
  principal_open_points_check

example : ∃ (V : TopologicalSpace.Opens (ComplexPoint (openScheme plane principal)))
    (W : TopologicalSpace.Opens (ComplexPoint plane)),
    ContractibleSpace V ∧ ContractibleSpace W ∧
    (W : Set (ComplexPoint plane)) = Point.map (openInclusion plane principal) '' V ∧
    planeChart.symm (fun _ => (1 : ℂ)) ∈ W :=
  principal_open_transport_check

example : planeChart.symm ![1, 2] ∈ Point.overOpen principal ∧
    planeChart.symm 0 ∉ Point.overOpen principal :=
  principal_open_membership_check

-- The chart homeomorphism and its regular functions are retained together.
example : ∃ (p : Fin 0 → MvPolynomial (Fin 2) ℂ)
    (a : Fin 2 → Γ(plane.left, ⊤))
    (h : ComplexPoint plane ≃ₜ zeroSet p),
    ∀ (z : ComplexPoint plane) (i : Fin 2),
      (h z).val i = Point.evaluate ⊤ (a i) z := by
  let p : Fin 0 → MvPolynomial (Fin 2) ℂ := Fin.elim0
  have hp : zeroSet p = Set.univ := by
    ext z
    simp [zeroSet]
  let e : (Fin 2 → ℂ) ≃ₜ zeroSet p :=
    (Homeomorph.Set.univ _).symm.trans (Homeomorph.setCongr hp.symm)
  refine ⟨p, AffineSpace.coord (Spec ↧ℂ), planeChart.trans e, ?_⟩
  intro z i
  change planeChart z i = Point.evaluate ⊤ (AffineSpace.coord (Spec ↧ℂ) i) z
  rw [AlgebraicGeometry.ComplexPoint.evaluate_top_eq_appTop]
  rfl

end HodgeLean.Foundations.ComplexTopology
