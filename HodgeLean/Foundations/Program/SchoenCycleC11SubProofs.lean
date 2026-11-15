import HodgeLean.Foundations.Program.SchoenCycleC11SmoothComponentHelpers
import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveSmooth
import HodgeLean.Foundations.Program.SchoenCycleC11DegreeHelpers
import Mathlib.Topology.Algebra.Module.LocallyConvex
import HodgeLean.Foundations.Program.SchoenCycleC11Sub2Proofs
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Projective
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Smaller projective etale comparison interfaces
Implication from explicit finite etale and finite-type inputs to analytic and scheme interfaces.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped LinearAlgebra.Projectivization
namespace HodgeLean.Foundations.Program

/-- Etale maps have analytic local inverses.
Source: Hartshorne, Algebraic Geometry, Appendix B, analytification of etale maps. -/
theorem s2e_c11_etale_local_homeomorph_aux
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsFinite f.left] [Etale f.left] :
    IsLocalHomeomorph (Point.map f) := by
  apply s2e_c11_local_inverse_transport_aux X Y f
  intro y
  obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  refine ⟨U, hy, hU, ?_⟩
  letI : IsAffine (openScheme X (f.left ⁻¹ᵁ U)).left := hU.preimage f.left
  letI : IsAffine (openScheme Y U).left := hU
  let fU := s2e_c11_restrictOver X Y f U
  letI : Etale fU.left := by
    change Etale (f.left ∣_ U)
    infer_instance
  have hp := s2e_c11_affine_scheme_etale_local_inverse _ _ fU
  let ex := openHomeomorph X (f.left ⁻¹ᵁ U)
  let ey := openHomeomorph Y U
  let r := (Point.underlying ⁻¹' (U : Set Y.left)).restrictPreimage (Point.map f)
  have heq : r = ey ∘ Point.map fU ∘ ex.symm := by
    funext z
    have h := s2e_c11_restrictOver_point_square X Y f U (ex.symm z)
    change ey (Point.map fU (ex.symm z)) = r (ex (ex.symm z)) at h
    rw [ex.apply_symm_apply] at h
    exact h.symm
  change IsLocalHomeomorph r
  rw [heq]
  exact ey.isLocalHomeomorph.comp (hp.comp ex.symm.isLocalHomeomorph)

/-- Finite maps have finite complex fibres.
Source: Hartshorne, Algebraic Geometry, II.3, finite algebras over a field. -/
theorem s2e_c11_finite_point_fibres_aux
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsFinite f.left] :
    ∀ y : Point ℂ Y, Set.Finite ((Point.map f) ⁻¹' {y}) := by
  intro y
  have hinj : Function.Injective (Point.underlying (X := X) (R := ℂ)) := by
    intro z w hzw
    apply Over.OverMorphism.ext
    exact ext_of_apply_closedPoint_eq X.hom (Over.w z) (Over.w w) hzw
  apply ((f.left.finite_preimage_singleton y.underlying).preimage hinj.injOn).subset
  intro z hz
  change f.left z.underlying = y.underlying
  exact congrArg Point.underlying hz

/-- Finite maps are analytically proper on affine base restrictions.
Source: Hartshorne, Algebraic Geometry, Appendix B, finite-map analytification. -/
theorem s2e_c11_finite_affine_closed_map_aux
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsFinite f.left]
    (U : Y.left.Opens) (hU : IsAffineOpen U) :
    IsClosedMap ((Point.underlying ⁻¹' (U : Set Y.left)).restrictPreimage (Point.map f)) := by
  exact (s2e_c11_finite_affine_restriction_proper_aux X Y f U hU).isClosedMap

/-- The coordinate comparison is a homeomorphism.
Source: Hartshorne, Algebraic Geometry, Appendix B; upstream ComplexPoint.Projective. -/
theorem s2e_c11_projective_comparison_aux
    (k : ℕ) :
    ∃ e : Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k) ≃ₜ
      (Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))),
      (e : Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k) → _) =
        ComplexProjectiveSpace.projectivizationToComplexPoint := by
  let e := Equiv.ofBijective
    (ComplexProjectiveSpace.projectivizationToComplexPoint (n := k))
    ⟨s2e_c11_projective_coordinate_injective_aux k,
      ComplexProjectiveSpace.surjective_projectivizationToComplexPoint⟩
  exact ⟨e.toHomeomorphOfContinuousClosed
    ComplexProjectiveSpace.continuous_projectivizationToComplexPoint
    ComplexProjectiveSpace.continuous_projectivizationToComplexPoint.isClosedMap, rfl⟩

/-- Classical complex projective space has affine local charts.
Source: Hartshorne, Algebraic Geometry, Appendix B, standard projective charts. -/
theorem s2e_c11_classical_projective_locally_path_connected_aux
    (k : ℕ) :
    LocallyPathConnectedSpace (Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k)) := by
  letI : LocallyPathConnectedSpace
      {v : ComplexProjectiveSpace.CoordinateSpace k // v ≠ 0} :=
    isOpen_ne.locallyPathConnectedSpace
  have hq : Topology.IsQuotientMap (Projectivization.mk' ℂ :
      {v : ComplexProjectiveSpace.CoordinateSpace k // v ≠ 0} →
        Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k)) :=
    isQuotientMap_quotient_mk'
  exact hq.locallyPathConnectedSpace

/-- Dimension zero is a point; positive dimensions are simply connected.
Source: Hatcher, Algebraic Topology, Example 0.6 and the CW structure of complex projective space. -/
theorem s2e_c11_classical_projective_simple_connectivity_aux
    (k : ℕ) :
    (k = 0 → Nonempty ((Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k)) ≃ₜ PUnit)) ∧
      (0 < k → SimplyConnectedSpace (Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k))) := by
  refine ⟨?_, ?_⟩
  · intro hk
    subst k
    exact s2e_c11_classical_projective_zero_aux
  · intro hk
    letI := s2e_c11_complex_coordinate_sphere_simply_connected_aux k hk
    exact s2e_c11_simplyConnected_of_basedLoop_lifts
      ⟨ComplexProjectiveSpace.sphereToProjectivization,
        ComplexProjectiveSpace.continuous_sphereToProjectivization⟩
      ComplexProjectiveSpace.surjective_sphereToProjectivization
      (fun v γ => s2e_c11_hopf_loop_lift_aux k hk v γ)

/-- An analytic sheet selects an algebraic clopen subset.
Source: SGA 1, Expose XII, Theoreme 5.1, comparison of finite etale covers. -/
theorem s2e_c11_section_algebraic_open_aux
    (k : ℕ) (W : Over (Spec ↧ℂ))
    (β : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite β.left] [Etale β.left]
    (s : Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) →
      Point ℂ W) (hc : Continuous s) (hs : ∀ x, Point.map β (s x) = x)
    (himage : IsOpen (Set.range s) ∧ IsClosed (Set.range s)) :
    ∃ U : W.left.Opens, IsClosed (U : Set W.left) ∧
      Point.underlying ⁻¹' (U : Set W.left) = Set.range s := by
  letI : Smooth (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) :=
    s0_projective_space_smooth k (Spec ↧ℂ)
  letI : Smooth W.hom := by
    rw [← Over.w β]
    change Smooth (β.left ≫ ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    infer_instance
  exact s2e_c11_smooth_clopen_preimage W (Set.range s) ⟨himage.2, himage.1⟩

/-- The selected component has finite etale degree one.
Source: SGA 1, Expose I, Proposition 5.1, finite etale covers of degree one. -/
theorem s2e_c11_section_component_degree_one_aux
    (k : ℕ) (W : Over (Spec ↧ℂ))
    (β : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite β.left] [Etale β.left]
    (s : Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) →
      Point ℂ W) (hc : Continuous s) (hs : ∀ x, Point.map β (s x) = x)
    (himage : IsOpen (Set.range s) ∧ IsClosed (Set.range s))
    (U : W.left.Opens) (hU : IsClosed (U : Set W.left))
    (hpoints : Point.underlying ⁻¹' (U : Set W.left) = Set.range s) :
    IsIso (U.ι ≫ β.left) := by
  letI : Smooth (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) :=
    s0_projective_space_smooth k (Spec ↧ℂ)
  letI : LocallyOfFiniteType
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom := by
    change LocallyOfFiniteType (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    infer_instance
  letI : LocallyOfFiniteType W.hom := by
    rw [← Over.w β]
    change LocallyOfFiniteType (β.left ≫ ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    infer_instance
  letI : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι (by
    rwa [Scheme.Opens.range_ι])
  letI : LocallyOfFiniteType (openScheme W U).hom := by
    change LocallyOfFiniteType (U.ι ≫ W.hom)
    infer_instance
  letI : IsFinite (openInclusion W U ≫ β).left := by
    change IsFinite (U.ι ≫ β.left)
    infer_instance
  letI : Etale (openInclusion W U ≫ β).left := by
    change Etale (U.ι ≫ β.left)
    infer_instance
  change IsIso (openInclusion W U ≫ β).left
  apply s2e_c11_finite_etale_isIso_of_point_bijective
    (openScheme W U) _ (openInclusion W U ≫ β)
  exact s2e_c11_section_component_point_bijective W _ β s hs U hpoints

/-- Complex points detect intersections of algebraic closed subsets.
Source: Hartshorne, Algebraic Geometry, II.3.14, closed points over an algebraically closed field. -/
theorem s2e_c11_complex_points_detect_intersection_aux
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (A B : Set X.left) (hA : IsClosed A) (hB : IsClosed B)
    (h : Disjoint (Point.underlying ⁻¹' A : Set (Point ℂ X))
      (Point.underlying ⁻¹' B)) :
    Disjoint A B := by
  haveI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  apply Set.disjoint_left.mpr
  intro x hxA hxB
  obtain ⟨z, hzAB, hz⟩ := nonempty_inter_closedPoints
    (show (A ∩ B).Nonempty from ⟨x, hxA, hxB⟩) (hA.inter hB).isLocallyClosed
  let p : Point ℂ X := Over.homMk (pointOfClosedPoint X.hom z hz)
    (pointOfClosedPoint_comp X.hom z hz)
  have hp : p.underlying = z := pointOfClosedPoint_apply X.hom z hz _
  exact Set.disjoint_left.mp h (by change p.underlying ∈ A; rw [hp]; exact hzAB.1)
    (by change p.underlying ∈ B; rw [hp]; exact hzAB.2)

/-- Complex points detect the complement of a finite union of closed subsets.
Source: Hartshorne, Algebraic Geometry, II.3.14, density of closed points. -/
theorem s2e_c11_complex_points_detect_complement_aux
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (n : ℕ) (A : Fin n → Set X.left) (hA : ∀ i, IsClosed (A i))
    (h : ∀ x : Point ℂ X, ∃ i, Point.underlying x ∈ A i) :
    ∀ x : X.left, ∃ i, x ∈ A i := by
  classical
  haveI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  intro x
  by_contra hx
  have hU : IsOpen ((⋃ i, A i)ᶜ) := (isClosed_iUnion_of_finite hA).isOpen_compl
  have hxU : x ∈ (⋃ i, A i)ᶜ := by
    simpa only [Set.mem_compl_iff, Set.mem_iUnion] using hx
  obtain ⟨z, hzU, hz⟩ := nonempty_inter_closedPoints ⟨x, hxU⟩ hU.isLocallyClosed
  let p : Point ℂ X := Over.homMk (pointOfClosedPoint X.hom z hz)
    (pointOfClosedPoint_comp X.hom z hz)
  have hp : p.underlying = z := pointOfClosedPoint_apply X.hom z hz _
  obtain ⟨i, hi⟩ := h p
  exact hzU (Set.mem_iUnion.mpr ⟨i, hp ▸ hi⟩)

end HodgeLean.Foundations.Program
