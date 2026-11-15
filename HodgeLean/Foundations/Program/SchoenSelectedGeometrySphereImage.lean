import HodgeLean.Foundations.Program.SchoenSelectedGeometryPowerHolomorphic
import HodgeLean.Foundations.Program.SchoenSelectedGeometryPowerProjections
import HodgeLean.Foundations.Program.SchoenSelectedGeometryAnalyticImmersion

noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Set
open HodgeLean.Adapters Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Finite separating meromorphic coordinates unramified at every point have analytic image
in the algebraic product of projective lines.
Source: the local inverse function theorem and the projective line comparison. -/
theorem s0_sphere_coordinates_analytic_image
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C]
    (n : ℕ) (F : Fin n → b4c_MeroFun ℂ C)
    (hsep : Function.Injective (fun x : C ↦ fun i ↦ F i x))
    (hder : ∀ x : C, ∃ i, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (F i) x ≠ 0) :
    let A : Over (Spec ↧ℂ) := Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))
    letI : SmoothOfRelativeDimension 1 A.hom := s0_complex_projective_relative_dimension 1
    letI : SmoothOfRelativeDimension n (g3_power A n).hom := by
      simpa only [Nat.mul_one] using spec_g3_smoothOfRelativeDimension_power A 1 n
    let f : C → ComplexPoint (g3_power A n) := fun x ↦
      (s0_power_point_homeomorph A n).symm
        (fun i ↦ s0_sphere_projective_homeomorph (F i x))
    IsClosedEmbedding f ∧ ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin n → ℂ) ω f ∧
      IsClosedAnalytic (Fin n → ℂ) (range f) := by
  let A : Over (Spec ↧ℂ) := Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))
  letI : SmoothOfRelativeDimension 1 A.hom := s0_complex_projective_relative_dimension 1
  letI : SmoothOfRelativeDimension n (g3_power A n).hom := by
    simpa only [Nat.mul_one] using spec_g3_smoothOfRelativeDimension_power A 1 n
  let e : (Fin n → OnePoint ℂ) ≃ₜ ComplexPoint (g3_power A n) :=
    (Homeomorph.piCongrRight (fun _ ↦ s0_sphere_projective_homeomorph)).trans
      (s0_power_point_homeomorph A n).symm
  let f : C → ComplexPoint (g3_power A n) := fun x ↦ e (fun i ↦ F i x)
  have htuple : IsClosedEmbedding (fun x : C ↦ fun i ↦ F i x) :=
    (continuous_pi (fun i ↦ (F i).property.1.continuous)).isClosedEmbedding hsep
  have he : IsClosedEmbedding f := e.isClosedEmbedding.comp htuple
  have hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin n → ℂ) ω f :=
    s0_power_point_tuple_holomorphic A n
      (fun i x ↦ s0_sphere_projective_homeomorph (F i x))
      (fun i ↦ s0_sphere_projective_holomorphic.comp (F i).property.1)
  refine ⟨he, hf, s0_image_analytic_of_unramified_coordinates n f hf he ?_⟩
  intro x
  obtain ⟨i, hi⟩ := hder x
  let q : ComplexPoint (g3_power A n) → OnePoint ℂ := fun y ↦
    s0_sphere_projective_homeomorph.symm (Point.map (g3_proj A n i) y)
  have hq : ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) ω q :=
    s0_sphere_projective_inverse_holomorphic.comp
      (spec_contMDiff_pointMap_aux (g3_power A n) A n 1 (g3_proj A n i))
  have hqf : q ∘ f = (F i : C → OnePoint ℂ) := by
    funext z
    have hp : Point.map (g3_proj A n i) (f z) =
        s0_sphere_projective_homeomorph (F i z) := by
      rw [← s0_power_point_homeomorph_projection]
      exact congrFun ((s0_power_point_homeomorph A n).apply_symm_apply _) i
    change s0_sphere_projective_homeomorph.symm (Point.map (g3_proj A n i) (f z)) = F i z
    rw [hp, Homeomorph.symm_apply_apply]
  exact ⟨q, hq, by rw [hqf]; exact hi⟩

#print axioms s0_sphere_coordinates_analytic_image
end HodgeLean.Foundations.Program
