import HodgeLean.Foundations.Program.SchoenCycleC11Sub2Proofs

/-! # Third subdivision of projective etale comparison
Implication from explicit algebra, scheme and topology inputs to local comparison interfaces.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped LinearAlgebra.Projectivization
namespace HodgeLean.Foundations.Program

/-- Etale algebras have standard etale source neighbourhoods.
Source: Stacks Project, Proposition 10.144.4, Tag 00UE, https://stacks.math.columbia.edu/tag/00UE. -/
theorem s2e_c11_standard_etale_neighbourhood
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Etale A B] (q : PrimeSpectrum B) :
    ∃ s : B, s ∉ q.asIdeal ∧
      Nonempty (StandardEtalePresentation A (Localization.Away s)) := by
  exact s2e_c11_standard_etale_neighbourhood_aux A B q

/-- Standard etale presentations give analytic local inverses over a possibly singular base.
Source: Hartshorne, Algebraic Geometry, Appendix B, analytic inverse function theorem for etale presentations. -/
theorem s2e_c11_standard_etale_local_inverse
    (A B : Type) [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
    [Algebra.FiniteType ℂ A] (P : StandardEtalePresentation A B) :
    IsLocalHomeomorph (fun φ : B →ₐ[ℂ] ℂ =>
      φ.comp (IsScalarTower.toAlgHom ℂ A B)) := by
  exact s2e_c11_standard_etale_local_inverse_aux A B P

/-- Local inverses on affine restrictions transport to the entire analytic map.
Source: Mathlib, IsLocalHomeomorph and open restriction locality; Hartshorne, Appendix B. -/
theorem s2e_c11_local_inverse_transport
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y)
    (h : ∀ y : Y.left, ∃ U : Y.left.Opens, y ∈ U ∧ IsAffineOpen U ∧
      IsLocalHomeomorph
        ((Point.underlying ⁻¹' (U : Set Y.left)).restrictPreimage (Point.map f))) :
    IsLocalHomeomorph (Point.map f) := by
  exact s2e_c11_local_inverse_transport_aux X Y f h

/-- A finite affine algebra map induces a proper analytic map.
Source: Hartshorne, Algebraic Geometry, Appendix B, analytification of finite morphisms. -/
theorem s2e_c11_finite_affine_proper
    (A B : Type) [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
    [Algebra.FiniteType ℂ A] [Module.Finite A B] :
    IsProperMap (fun φ : B →ₐ[ℂ] ℂ =>
      φ.comp (IsScalarTower.toAlgHom ℂ A B)) := by
  exact s2e_c11_finite_affine_proper_aux A B

/-- Affine restriction identifications transport finite analytic properness.
Source: Hartshorne, Algebraic Geometry, II.3 and Appendix B; upstream ComplexPoint.affineSpecHomeomorph. -/
theorem s2e_c11_finite_affine_restriction_proper
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsFinite f.left]
    (U : Y.left.Opens) (hU : IsAffineOpen U) :
    IsProperMap
      ((Point.underlying ⁻¹' (U : Set Y.left)).restrictPreimage (Point.map f)) := by
  exact s2e_c11_finite_affine_restriction_proper_aux X Y f U hU

/-- The actual coordinate comparison identifies only scalar-equivalent vectors.
Source: Hartshorne, Algebraic Geometry, II.2, standard projective charts; upstream ComplexProjectiveSpace.chartCoordinate. -/
theorem s2e_c11_projective_coordinate_injective
    (k : ℕ) :
    Function.Injective
      (ComplexProjectiveSpace.projectivizationToComplexPoint (n := k)) := by
  exact s2e_c11_projective_coordinate_injective_aux k

/-- Each normalized-coordinate chart is a complex affine space.
Source: Hartshorne, Algebraic Geometry, I.2, standard affine charts of projective space. -/
theorem s2e_c11_classical_projective_chart
    (k : ℕ) (i : Fin (k + 1)) :
    ∃ U : TopologicalSpace.Opens
        (Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k)),
      (∀ v : ComplexProjectiveSpace.CoordinateSpace k, ∀ hv : v ≠ 0,
        Projectivization.mk ℂ v hv ∈ U ↔ v i ≠ 0) ∧
      Nonempty (U ≃ₜ ({j : Fin (k + 1) // j ≠ i} → ℂ)) := by
  exact s2e_c11_classical_projective_chart_aux k i

/-- Projective dimension zero is a single point with its topology.
Source: Hartshorne, Algebraic Geometry, I.2, projective zero-space. -/
theorem s2e_c11_classical_projective_zero
    : Nonempty
      (Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace 0) ≃ₜ PUnit) := by
  exact s2e_c11_classical_projective_zero_aux

/-- The sphere above positive-dimensional projective space is simply connected.
Source: Hatcher, Algebraic Topology, Proposition 1.14, spheres of dimension at least two. -/
theorem s2e_c11_complex_coordinate_sphere_simply_connected
    (k : ℕ) (hk : 0 < k) :
    SimplyConnectedSpace
      (Metric.sphere (0 : ComplexProjectiveSpace.CoordinateSpace k) 1) := by
  exact s2e_c11_complex_coordinate_sphere_simply_connected_aux k hk

/-- Every based projective loop has a based sphere loop representative.
Source: Hatcher, Algebraic Topology, section 4.2, Hopf bundle and homotopy lifting; connected circle fibre. -/
theorem s2e_c11_hopf_loop_lift
    (k : ℕ) (hk : 0 < k)
    (v : Metric.sphere (0 : ComplexProjectiveSpace.CoordinateSpace k) 1)
    (γ : Path (ComplexProjectiveSpace.sphereToProjectivization v)
      (ComplexProjectiveSpace.sphereToProjectivization v)) :
    ∃ δ : Path v v,
      Path.Homotopic
        (δ.map ComplexProjectiveSpace.continuous_sphereToProjectivization) γ := by
  exact s2e_c11_hopf_loop_lift_aux k hk v γ

example
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Etale A B] (q : PrimeSpectrum B) :
    ∃ s : B, s ∉ q.asIdeal ∧
      Nonempty (StandardEtalePresentation A (Localization.Away s)) := by
  exact s2e_c11_standard_etale_neighbourhood A B q

example
    (A B : Type) [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
    [Algebra.FiniteType ℂ A] (P : StandardEtalePresentation A B) :
    IsLocalHomeomorph (fun φ : B →ₐ[ℂ] ℂ =>
      φ.comp (IsScalarTower.toAlgHom ℂ A B)) := by
  exact s2e_c11_standard_etale_local_inverse A B P

example
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y)
    (h : ∀ y : Y.left, ∃ U : Y.left.Opens, y ∈ U ∧ IsAffineOpen U ∧
      IsLocalHomeomorph
        ((Point.underlying ⁻¹' (U : Set Y.left)).restrictPreimage (Point.map f))) :
    IsLocalHomeomorph (Point.map f) := by
  exact s2e_c11_local_inverse_transport X Y f h

example
    (A B : Type) [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
    [Algebra.FiniteType ℂ A] [Module.Finite A B] :
    IsProperMap (fun φ : B →ₐ[ℂ] ℂ =>
      φ.comp (IsScalarTower.toAlgHom ℂ A B)) := by
  exact s2e_c11_finite_affine_proper A B

example
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsFinite f.left]
    (U : Y.left.Opens) (hU : IsAffineOpen U) :
    IsProperMap
      ((Point.underlying ⁻¹' (U : Set Y.left)).restrictPreimage (Point.map f)) := by
  exact s2e_c11_finite_affine_restriction_proper X Y f U hU

example
    (k : ℕ) :
    Function.Injective
      (ComplexProjectiveSpace.projectivizationToComplexPoint (n := k)) := by
  exact s2e_c11_projective_coordinate_injective k

example
    (k : ℕ) (i : Fin (k + 1)) :
    ∃ U : TopologicalSpace.Opens
        (Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k)),
      (∀ v : ComplexProjectiveSpace.CoordinateSpace k, ∀ hv : v ≠ 0,
        Projectivization.mk ℂ v hv ∈ U ↔ v i ≠ 0) ∧
      Nonempty (U ≃ₜ ({j : Fin (k + 1) // j ≠ i} → ℂ)) := by
  exact s2e_c11_classical_projective_chart k i

example
    : Nonempty
      (Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace 0) ≃ₜ PUnit) := by
  exact s2e_c11_classical_projective_zero

example
    (k : ℕ) (hk : 0 < k) :
    SimplyConnectedSpace
      (Metric.sphere (0 : ComplexProjectiveSpace.CoordinateSpace k) 1) := by
  exact s2e_c11_complex_coordinate_sphere_simply_connected k hk

example
    (k : ℕ) (hk : 0 < k)
    (v : Metric.sphere (0 : ComplexProjectiveSpace.CoordinateSpace k) 1)
    (γ : Path (ComplexProjectiveSpace.sphereToProjectivization v)
      (ComplexProjectiveSpace.sphereToProjectivization v)) :
    ∃ δ : Path v v,
      Path.Homotopic
        (δ.map ComplexProjectiveSpace.continuous_sphereToProjectivization) γ := by
  exact s2e_c11_hopf_loop_lift k hk v γ

end HodgeLean.Foundations.Program
