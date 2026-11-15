import HodgeLean.Foundations.Program.SchoenCycleC11SphereTopologyHelpers
import HodgeLean.Foundations.Program.SchoenCycleC11HopfHelpers
import HodgeLean.Foundations.Program.SchoenCycleC11StandardHelpers
import Mathlib.RingTheory.Unramified.LocalStructure
import HodgeLean.Foundations.Program.SchoenCycleC11AffineHelpers
import HodgeLean.Foundations.Program.SchoenCycleC11FiniteHelpers
import HodgeLean.Foundations.Program.SchoenCycleC11ProperHelpers
import HodgeLean.Foundations.Program.SchoenCycleC11ChartHelpers
import HodgeLean.Foundations.Program.SchoenCycleC11LowerHelpers
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Projective
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.StandardEtale
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Maps.Proper.Basic

/-! # Third subdivision of projective etale comparison
Implication from explicit algebra, scheme and topology inputs to local comparison interfaces.
HC no distance; AV milestone no distance.
-/
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped LinearAlgebra.Projectivization
namespace HodgeLean.Foundations.Program

/-- Etale algebras have standard etale source neighbourhoods.
Source: Stacks Project, Proposition 10.144.4, Tag 00UE, https://stacks.math.columbia.edu/tag/00UE. -/
theorem s2e_c11_standard_etale_neighbourhood_aux
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Etale A B] (q : PrimeSpectrum B) :
    ∃ s : B, s ∉ q.asIdeal ∧
      Nonempty (StandardEtalePresentation A (Localization.Away s)) := by
  obtain ⟨s, hs, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) q.asIdeal
  letI := hstd
  exact ⟨s, hs, inferInstance⟩

/-- Standard etale presentations give analytic local inverses over a possibly singular base.
Source: Hartshorne, Algebraic Geometry, Appendix B, analytic inverse function theorem for etale presentations. -/
theorem s2e_c11_standard_etale_local_inverse_aux
    (A B : Type) [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
    [Algebra.FiniteType ℂ A] (P : StandardEtalePresentation A B) :
    IsLocalHomeomorph (fun φ : B →ₐ[ℂ] ℂ =>
      φ.comp (IsScalarTower.toAlgHom ℂ A B)) := by
  exact (s2e_c11_standardRoot_projection P.P).comp
    (s2e_c11_standardPresentationRootHomeomorph P).isLocalHomeomorph

/-- Local inverses on affine restrictions transport to the entire analytic map.
Source: Mathlib, IsLocalHomeomorph and open restriction locality; Hartshorne, Appendix B. -/
theorem s2e_c11_local_inverse_transport_aux
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y)
    (h : ∀ y : Y.left, ∃ U : Y.left.Opens, y ∈ U ∧ IsAffineOpen U ∧
      IsLocalHomeomorph
        ((Point.underlying ⁻¹' (U : Set Y.left)).restrictPreimage (Point.map f))) :
    IsLocalHomeomorph (Point.map f) := by
  apply s2e_c11_local_homeomorph_of_target_opens (Point.map f) (Point.continuous_map f)
  intro y
  obtain ⟨U, hy, _, hloc⟩ := h y.underlying
  exact ⟨Point.underlying ⁻¹' (U : Set Y.left), hy, Point.isOpen_overOpen U, hloc⟩

/-- A finite affine algebra map induces a proper analytic map.
Source: Hartshorne, Algebraic Geometry, Appendix B, analytification of finite morphisms. -/
theorem s2e_c11_finite_affine_proper_aux
    (A B : Type) [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
    [Algebra.FiniteType ℂ A] [Module.Finite A B] :
    IsProperMap (fun φ : B →ₐ[ℂ] ℂ =>
      φ.comp (IsScalarTower.toAlgHom ℂ A B)) := by
  letI : T2Space (A →ₐ[ℂ] ℂ) :=
    (s2e_c11_algebraHom_isClosedEmbedding A).isEmbedding.t2Space
  apply s2e_c11_proper_of_coordinate_bounds
    (fun φ : B →ₐ[ℂ] ℂ => (φ : B → ℂ)) (s2e_c11_algebraHom_isClosedEmbedding B)
  · rw [continuous_induced_rng]
    exact continuous_pi (fun a =>
      AlgebraicGeometry.ComplexPoint.continuous_affineAlgebraHom_apply B (algebraMap A B a))
  · exact s2e_c11_finite_element_continuous_bound

/-- Affine restriction identifications transport finite analytic properness.
Source: Hartshorne, Algebraic Geometry, II.3 and Appendix B; upstream ComplexPoint.affineSpecHomeomorph. -/
theorem s2e_c11_finite_affine_restriction_proper_aux
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsFinite f.left]
    (U : Y.left.Opens) (hU : IsAffineOpen U) :
    IsProperMap
      ((Point.underlying ⁻¹' (U : Set Y.left)).restrictPreimage (Point.map f)) := by
  letI : IsAffine (openScheme X (f.left ⁻¹ᵁ U)).left := hU.preimage f.left
  letI : IsAffine (openScheme Y U).left := hU
  let fU := s2e_c11_restrictOver X Y f U
  letI : IsFinite fU.left := by
    change IsFinite (f.left ∣_ U)
    infer_instance
  have hp := s2e_c11_affine_scheme_finite_proper _ _ fU
  let ex := openHomeomorph X (f.left ⁻¹ᵁ U)
  let ey := openHomeomorph Y U
  let r := (Point.underlying ⁻¹' (U : Set Y.left)).restrictPreimage (Point.map f)
  have heq : r = ey ∘ Point.map fU ∘ ex.symm := by
    funext z
    have h := s2e_c11_restrictOver_point_square X Y f U (ex.symm z)
    change ey (Point.map fU (ex.symm z)) = r (ex (ex.symm z)) at h
    rw [ex.apply_symm_apply] at h
    exact h.symm
  change IsProperMap r
  rw [heq]
  exact ey.isProperMap.comp (hp.comp ex.symm.isProperMap)

/-- The actual coordinate comparison identifies only scalar-equivalent vectors.
Source: Hartshorne, Algebraic Geometry, II.2, standard projective charts; upstream ComplexProjectiveSpace.chartCoordinate. -/
theorem s2e_c11_projective_coordinate_injective_aux
    (k : ℕ) :
    Function.Injective
      (ComplexProjectiveSpace.projectivizationToComplexPoint (n := k)) := by
  intro p q hpq
  induction p using Projectivization.ind with
  | _ v hv =>
    induction q using Projectivization.ind with
    | _ w hw =>
      have he : ComplexProjectiveSpace.chartIntegralProj v hv =
          ComplexProjectiveSpace.chartIntegralProj w hw := by
        have hh := congrArg (fun z => z.left ≫ Limits.pullback.snd
          (Limits.terminal.from (Spec ↧ℂ))
          (Limits.terminal.from (Proj (ComplexProjectiveSpace.UniversalGrading k)))) hpq
        simpa only [ComplexProjectiveSpace.projectivizationToComplexPoint_mk,
          ComplexProjectiveSpace.vectorToComplexPoint,
          ComplexProjectiveSpace.vectorToProjectiveSpace,
          Over.homMk_left, Limits.pullback.lift_snd] using hh
      obtain ⟨i, hi⟩ := ComplexProjectiveSpace.exists_coordinate_ne_zero v hv
      obtain ⟨j, hj⟩ := ComplexProjectiveSpace.exists_coordinate_ne_zero w hw
      have hwi : w i ≠ 0 := by
        apply (s2e_c11_chart_coordinate_membership w j i hj).mp
        rw [← ComplexProjectiveSpace.chartIntegralProj_eq_chartIntegralProjAt w hw j hj,
          ← he, ComplexProjectiveSpace.chartIntegralProj_eq_chartIntegralProjAt v hv i hi]
        exact (s2e_c11_chart_coordinate_membership v i i hi).mpr hi
      have hchart : ComplexProjectiveSpace.chartIntegralProjAt v i hi =
          ComplexProjectiveSpace.chartIntegralProjAt w i hwi := by
        rw [← ComplexProjectiveSpace.chartIntegralProj_eq_chartIntegralProjAt v hv i hi,
          ← ComplexProjectiveSpace.chartIntegralProj_eq_chartIntegralProjAt w hw i hwi]
        exact he
      have hr := s2e_c11_same_chart_ratios v w i hi hwi hchart
      apply (Projectivization.mk_eq_mk_iff' ℂ v w hv hw).mpr
      refine ⟨v i / w i, ?_⟩
      funext a
      change (v i / w i) * w a = v a
      calc
        (v i / w i) * w a = (w a * (w i)⁻¹) * v i := by ring
        _ = (v a * (v i)⁻¹) * v i := by rw [hr a]
        _ = v a := by rw [mul_assoc, inv_mul_cancel₀ hi, mul_one]

/-- Each normalized-coordinate chart is a complex affine space.
Source: Hartshorne, Algebraic Geometry, I.2, standard affine charts of projective space. -/
theorem s2e_c11_classical_projective_chart_aux
    (k : ℕ) (i : Fin (k + 1)) :
    ∃ U : TopologicalSpace.Opens
        (Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k)),
      (∀ v : ComplexProjectiveSpace.CoordinateSpace k, ∀ hv : v ≠ 0,
        Projectivization.mk ℂ v hv ∈ U ↔ v i ≠ 0) ∧
      Nonempty (U ≃ₜ ({j : Fin (k + 1) // j ≠ i} → ℂ)) := by
  refine ⟨⟨{p | s2e_c11_normalizedCoordinates i p i ≠ 0},
    s2e_c11_normalizedChart_isOpen i⟩, ?_, ⟨s2e_c11_normalizedChartHomeomorph i⟩⟩
  intro v hv
  exact s2e_c11_normalizedCoordinates_nonzero i v hv

/-- Projective dimension zero is a single point with its topology.
Source: Hartshorne, Algebraic Geometry, I.2, projective zero-space. -/
theorem s2e_c11_classical_projective_zero_aux
    : Nonempty
      (Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace 0) ≃ₜ PUnit) := by
  letI : Subsingleton (Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace 0)) :=
    ⟨s2e_c11_one_coordinate_line_unique⟩
  let p : Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace 0) :=
    Projectivization.mk ℂ (fun _ => 1) (by
      intro h
      have := congrFun h 0
      exact one_ne_zero this)
  letI : Unique (Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace 0)) :=
    ⟨⟨p⟩, fun _ => Subsingleton.elim _ _⟩
  exact ⟨Homeomorph.homeomorphOfUnique _ _⟩

/-- The sphere above positive-dimensional projective space is simply connected.
Source: Hatcher, Algebraic Topology, Proposition 1.14, spheres of dimension at least two. -/
theorem s2e_c11_complex_coordinate_sphere_simply_connected_aux
    (k : ℕ) (hk : 0 < k) :
    SimplyConnectedSpace
      (Metric.sphere (0 : ComplexProjectiveSpace.CoordinateSpace k) 1) := by
  letI : SimplyConnectedSpace
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin ((k + 1) * 2))) 1) :=
    s2e_c11_realSphere_simplyConnected (by
      simp only [finrank_euclideanSpace, Fintype.card_fin]
      omega)
  exact (s2e_c11_coordinateSphereRealEuclideanHomeomorph k).toHomotopyEquiv.simplyConnectedSpace

/-- Every based projective loop has a based sphere loop representative.
Source: Hatcher, Algebraic Topology, section 4.2, Hopf bundle and homotopy lifting; connected circle fibre. -/
theorem s2e_c11_hopf_loop_lift_aux
    (k : ℕ) (hk : 0 < k)
    (v : Metric.sphere (0 : ComplexProjectiveSpace.CoordinateSpace k) 1)
    (γ : Path (ComplexProjectiveSpace.sphereToProjectivization v)
      (ComplexProjectiveSpace.sphereToProjectivization v)) :
    ∃ δ : Path v v,
      Path.Homotopic
        (δ.map ComplexProjectiveSpace.continuous_sphereToProjectivization) γ := by
  obtain ⟨α, hα, h₀⟩ := s2e_c11_hopf_path_lift k γ.toContinuousMap v γ.source
  exact s2e_c11_hopf_correct_endpoint k v γ α h₀ (fun t => congrFun hα t)

end HodgeLean.Foundations.Program
