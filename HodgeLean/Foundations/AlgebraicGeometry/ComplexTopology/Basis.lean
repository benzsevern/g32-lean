import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Checks
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Proofs

/-! First-stage affine-chart and open-immersion basis specification.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Topology
namespace HodgeLean.Foundations.ComplexTopology

private abbrev node := zeroSet (fun _ : Fin 1 =>
  MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1 : Fin 1 → MvPolynomial (Fin 2) ℂ)
private def origin : node := ⟨0, by simp [zeroSet]⟩
private abbrev plane := Over.mk (AlgebraicGeometry.ComplexPoint.complexAffineSpace (Fin 2) ↘ Spec ↧ℂ)
private abbrev planeChart := AlgebraicGeometry.ComplexPoint.affineSpaceHomeomorph (Fin 2)
private abbrev coord := AffineSpace.coord (Spec ↧ℂ) (0 : Fin 2)
private abbrev principal := plane.left.basicOpen coord


/-- Polynomial zero sets have pointed contractible neighborhoods.
Source: Łojasiewicz, Triangulation of semi-analytic sets (1964), triangulation theorem; Bochnak, Coste, Roy, Real Algebraic Geometry, Theorem 9.2.1. -/
theorem zeroSet_basis {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℂ)
    (x : zeroSet p) (U : Opens (zeroSet p)) (hx : x ∈ U) :
    ∃ V : Opens (zeroSet p), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U :=
  zeroSet_basis_aux p x U hx

example (U : TopologicalSpace.Opens node) (h : origin ∈ U) :
    ∃ V : TopologicalSpace.Opens node,
      origin ∈ V ∧ ContractibleSpace V ∧ V ≤ U :=
  node_origin_basis_check U h

/-- Affine finite-type coordinates use actual regular-function evaluation.
Source: Hartshorne, Algebraic Geometry, II.2, Proposition 2.3; Hilbert basis theorem; Point.analyticTopology_eq_generateFrom. -/
theorem affine_coordinates (X : Over (Spec ↧ℂ)) [IsAffine X.left] [LocallyOfFiniteType X.hom] :
    ∃ (n m : ℕ) (p : Fin m → MvPolynomial (Fin n) ℂ)
      (a : Fin n → Γ(X.left, ⊤)) (h : ComplexPoint X ≃ₜ zeroSet p),
      ∀ (z : ComplexPoint X) (i : Fin n), (h z).val i = Point.evaluate ⊤ (a i) z :=
  affine_coordinates_aux X

example : Point.evaluate ⊤ coord (planeChart.symm ![1, 2]) = 1 ∧
    Point.evaluate ⊤ (AffineSpace.coord (Spec ↧ℂ) (1 : Fin 2))
      (planeChart.symm ![1, 2]) = 2 :=
  affine_plane_coordinates_check

/-- The affine basis lies in the existing analytic topology.
Source: Łojasiewicz, Triangulation of semi-analytic sets (1964); Hartshorne, Algebraic Geometry, II.2. -/
theorem affine_basis (X : Over (Spec ↧ℂ)) [IsAffine X.left] [LocallyOfFiniteType X.hom]
    (x : ComplexPoint X) (U : Opens (ComplexPoint X)) (hx : x ∈ U) :
    ∃ V : Opens (ComplexPoint X), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U :=
  affine_basis_aux X x U hx

example (x : ComplexPoint plane)
    (U : TopologicalSpace.Opens (ComplexPoint plane)) (hx : x ∈ U) :
    ∃ V : TopologicalSpace.Opens (ComplexPoint plane),
      x ∈ V ∧ ContractibleSpace V ∧ V ≤ U :=
  affine_plane_basis_check x U hx

/-- An actual open immersion gives an open embedding of point spaces.
Source: Hartshorne, Algebraic Geometry, II.2, open subschemes; Point.analyticTopology_eq_generateFrom and Point.continuous_map. -/
theorem openImmersion_points {X Y : Over (Spec ↧ℂ)} (j : X ⟶ Y) [IsOpenImmersion j.left] :
    IsOpenEmbedding (Point.map j : ComplexPoint X → ComplexPoint Y) :=
  openImmersion_points_aux j

example : IsOpenEmbedding (Point.map (openInclusion plane principal)) ∧
    ¬ Function.Surjective (Point.map (openInclusion plane principal)) :=
  principal_open_points_check

/-- Transport retains the image of the specified chart map and the specified point.
Source: Munkres, Topology, §16 (subspace topology) and §25 (local properties); Homeomorph.contractibleSpace_iff. -/
theorem openImmersion_basis_transport {X Y : Over (Spec ↧ℂ)} (j : X ⟶ Y) [IsOpenImmersion j.left]
    (hX : ∀ (x : ComplexPoint X) (U : Opens (ComplexPoint X)), x ∈ U →
      ∃ V : Opens (ComplexPoint X), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (x : ComplexPoint X) (U : Opens (ComplexPoint Y)) (hx : Point.map j x ∈ U) :
    ∃ (V : Opens (ComplexPoint X)) (W : Opens (ComplexPoint Y)),
      x ∈ V ∧ ContractibleSpace V ∧
      (W : Set (ComplexPoint Y)) = Point.map j '' (V : Set (ComplexPoint X)) ∧
      Point.map j x ∈ W ∧ ContractibleSpace W ∧ W ≤ U :=
  openImmersion_basis_transport_aux j hX x U hx

example : ∃ (V : TopologicalSpace.Opens (ComplexPoint (openScheme plane principal)))
    (W : TopologicalSpace.Opens (ComplexPoint plane)),
    ContractibleSpace V ∧ ContractibleSpace W ∧
    (W : Set (ComplexPoint plane)) = Point.map (openInclusion plane principal) '' V ∧
    planeChart.symm (fun _ => (1 : ℂ)) ∈ W :=
  principal_open_transport_check

/-- Local finite type suffices for the pointed basis on the whole scheme.
Source: Hartshorne, Algebraic Geometry, II.3 (local finite type); Łojasiewicz, Triangulation of semi-analytic sets (1964). -/
theorem finiteType_basis (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (x : ComplexPoint X) (U : Opens (ComplexPoint X)) (hx : x ∈ U) :
    ∃ V : Opens (ComplexPoint X), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U :=
  finiteType_basis_aux X x U hx

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
