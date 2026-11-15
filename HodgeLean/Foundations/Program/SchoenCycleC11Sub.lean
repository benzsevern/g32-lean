import HodgeLean.Foundations.Program.SchoenCycleC11SubProofs
/-! # Smaller projective etale comparison interfaces
Implication from explicit finite etale and finite-type inputs to analytic and scheme interfaces.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped LinearAlgebra.Projectivization
namespace HodgeLean.Foundations.Program

/-- Etale maps have analytic local inverses.
Source: Hartshorne, Algebraic Geometry, Appendix B, analytification of etale maps. -/
theorem s2e_c11_etale_local_homeomorph
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsFinite f.left] [Etale f.left] :
    IsLocalHomeomorph (Point.map f) := by
  exact s2e_c11_etale_local_homeomorph_aux X Y f

example
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsFinite f.left] [Etale f.left] :
    IsLocalHomeomorph (Point.map f) := by
  exact s2e_c11_etale_local_homeomorph_aux X Y f


/-- Finite maps have finite complex fibres.
Source: Hartshorne, Algebraic Geometry, II.3, finite algebras over a field. -/
theorem s2e_c11_finite_point_fibres
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsFinite f.left] :
    ∀ y : Point ℂ Y, Set.Finite ((Point.map f) ⁻¹' {y}) := by
  exact s2e_c11_finite_point_fibres_aux X Y f

example
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsFinite f.left] :
    ∀ y : Point ℂ Y, Set.Finite ((Point.map f) ⁻¹' {y}) := by
  exact s2e_c11_finite_point_fibres_aux X Y f


/-- Finite maps are analytically proper on affine base restrictions.
Source: Hartshorne, Algebraic Geometry, Appendix B, finite-map analytification. -/
theorem s2e_c11_finite_affine_closed_map
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsFinite f.left]
    (U : Y.left.Opens) (hU : IsAffineOpen U) :
    IsClosedMap ((Point.underlying ⁻¹' (U : Set Y.left)).restrictPreimage (Point.map f)) := by
  exact s2e_c11_finite_affine_closed_map_aux X Y f U hU

example
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsFinite f.left]
    (U : Y.left.Opens) (hU : IsAffineOpen U) :
    IsClosedMap ((Point.underlying ⁻¹' (U : Set Y.left)).restrictPreimage (Point.map f)) := by
  exact s2e_c11_finite_affine_closed_map_aux X Y f U hU


/-- The coordinate comparison is a homeomorphism.
Source: Hartshorne, Algebraic Geometry, Appendix B; upstream ComplexPoint.Projective. -/
theorem s2e_c11_projective_comparison
    (k : ℕ) :
    ∃ e : Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k) ≃ₜ
      (Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))),
      (e : Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k) → _) =
        ComplexProjectiveSpace.projectivizationToComplexPoint := by
  exact s2e_c11_projective_comparison_aux k

example
    (k : ℕ) :
    ∃ e : Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k) ≃ₜ
      (Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))),
      (e : Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k) → _) =
        ComplexProjectiveSpace.projectivizationToComplexPoint := by
  exact s2e_c11_projective_comparison_aux k


/-- Classical complex projective space has affine local charts.
Source: Hartshorne, Algebraic Geometry, Appendix B, standard projective charts. -/
theorem s2e_c11_classical_projective_locally_path_connected
    (k : ℕ) :
    LocallyPathConnectedSpace (Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k)) := by
  exact s2e_c11_classical_projective_locally_path_connected_aux k

example
    (k : ℕ) :
    LocallyPathConnectedSpace (Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k)) := by
  exact s2e_c11_classical_projective_locally_path_connected_aux k


/-- Dimension zero is a point; positive dimensions are simply connected.
Source: Hatcher, Algebraic Topology, Example 0.6 and the CW structure of complex projective space. -/
theorem s2e_c11_classical_projective_simple_connectivity
    (k : ℕ) :
    (k = 0 → Nonempty ((Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k)) ≃ₜ PUnit)) ∧
      (0 < k → SimplyConnectedSpace (Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k))) := by
  exact s2e_c11_classical_projective_simple_connectivity_aux k

example
    (k : ℕ) :
    (k = 0 → Nonempty ((Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k)) ≃ₜ PUnit)) ∧
      (0 < k → SimplyConnectedSpace (Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k))) := by
  exact s2e_c11_classical_projective_simple_connectivity_aux k


/-- An analytic sheet selects an algebraic clopen subset.
Source: SGA 1, Expose XII, Theoreme 5.1, comparison of finite etale covers. -/
theorem s2e_c11_section_algebraic_open
    (k : ℕ) (W : Over (Spec ↧ℂ))
    (β : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite β.left] [Etale β.left]
    (s : Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) →
      Point ℂ W) (hc : Continuous s) (hs : ∀ x, Point.map β (s x) = x)
    (himage : IsOpen (Set.range s) ∧ IsClosed (Set.range s)) :
    ∃ U : W.left.Opens, IsClosed (U : Set W.left) ∧
      Point.underlying ⁻¹' (U : Set W.left) = Set.range s := by
  exact s2e_c11_section_algebraic_open_aux k W β s hc hs himage

example
    (k : ℕ) (W : Over (Spec ↧ℂ))
    (β : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite β.left] [Etale β.left]
    (s : Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) →
      Point ℂ W) (hc : Continuous s) (hs : ∀ x, Point.map β (s x) = x)
    (himage : IsOpen (Set.range s) ∧ IsClosed (Set.range s)) :
    ∃ U : W.left.Opens, IsClosed (U : Set W.left) ∧
      Point.underlying ⁻¹' (U : Set W.left) = Set.range s := by
  exact s2e_c11_section_algebraic_open_aux k W β s hc hs himage


/-- The selected component has finite etale degree one.
Source: SGA 1, Expose I, Proposition 5.1, finite etale covers of degree one. -/
theorem s2e_c11_section_component_degree_one
    (k : ℕ) (W : Over (Spec ↧ℂ))
    (β : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite β.left] [Etale β.left]
    (s : Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) →
      Point ℂ W) (hc : Continuous s) (hs : ∀ x, Point.map β (s x) = x)
    (himage : IsOpen (Set.range s) ∧ IsClosed (Set.range s))
    (U : W.left.Opens) (hU : IsClosed (U : Set W.left))
    (hpoints : Point.underlying ⁻¹' (U : Set W.left) = Set.range s) :
    IsIso (U.ι ≫ β.left) := by
  exact s2e_c11_section_component_degree_one_aux k W β s hc hs himage U hU hpoints

example
    (k : ℕ) (W : Over (Spec ↧ℂ))
    (β : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite β.left] [Etale β.left]
    (s : Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) →
      Point ℂ W) (hc : Continuous s) (hs : ∀ x, Point.map β (s x) = x)
    (himage : IsOpen (Set.range s) ∧ IsClosed (Set.range s))
    (U : W.left.Opens) (hU : IsClosed (U : Set W.left))
    (hpoints : Point.underlying ⁻¹' (U : Set W.left) = Set.range s) :
    IsIso (U.ι ≫ β.left) := by
  exact s2e_c11_section_component_degree_one_aux k W β s hc hs himage U hU hpoints


/-- Complex points detect intersections of algebraic closed subsets.
Source: Hartshorne, Algebraic Geometry, II.3.14, closed points over an algebraically closed field. -/
theorem s2e_c11_complex_points_detect_intersection
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (A B : Set X.left) (hA : IsClosed A) (hB : IsClosed B)
    (h : Disjoint (Point.underlying ⁻¹' A : Set (Point ℂ X))
      (Point.underlying ⁻¹' B)) :
    Disjoint A B := by
  exact s2e_c11_complex_points_detect_intersection_aux X A B hA hB h

example
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (A B : Set X.left) (hA : IsClosed A) (hB : IsClosed B)
    (h : Disjoint (Point.underlying ⁻¹' A : Set (Point ℂ X))
      (Point.underlying ⁻¹' B)) :
    Disjoint A B := by
  exact s2e_c11_complex_points_detect_intersection_aux X A B hA hB h


/-- Complex points detect the complement of a finite union of closed subsets.
Source: Hartshorne, Algebraic Geometry, II.3.14, density of closed points. -/
theorem s2e_c11_complex_points_detect_complement
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (n : ℕ) (A : Fin n → Set X.left) (hA : ∀ i, IsClosed (A i))
    (h : ∀ x : Point ℂ X, ∃ i, Point.underlying x ∈ A i) :
    ∀ x : X.left, ∃ i, x ∈ A i := by
  exact s2e_c11_complex_points_detect_complement_aux X n A hA h

example
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (n : ℕ) (A : Fin n → Set X.left) (hA : ∀ i, IsClosed (A i))
    (h : ∀ x : Point ℂ X, ∃ i, Point.underlying x ∈ A i) :
    ∀ x : X.left, ∃ i, x ∈ A i := by
  exact s2e_c11_complex_points_detect_complement_aux X n A hA h


end HodgeLean.Foundations.Program
