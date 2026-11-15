import HodgeLean.Foundations.Program.SchoenSelectedGeometrySphereImage
import HodgeLean.Foundations.ChowProjective

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
/-- Separating and unramified meromorphic coordinates embed a compact curve with algebraic image
in a smooth integral projective scheme.
Source: Chow, On compact complex analytic varieties, Amer. J. Math. 71 (1949), 893–914. -/
theorem s0_projective_carrier_of_sphere_coordinates
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C] [CompactSpace C]
    (T : Finset (b4c_MeroFun ℂ C))
    (hsep : ∀ x y : C, (∀ F ∈ T, F x = F y) → x = y)
    (hder : ∀ x : C, ∃ F ∈ T, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) F x ≠ 0) :
    ∃ X : Over (Spec ↧ℂ),
      ∃ (_ : IsIntegral X.left) (_ : Smooth X.hom) (_ : IsProjective X.hom),
      ∃ (f : C → ComplexPoint X) (Z : Set X.left),
        IsClosedEmbedding f ∧
        ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ) ω f ∧
        IsClosed Z ∧ range f = (Point.underlying : ComplexPoint X → X.left) ⁻¹' Z := by
  classical
  let N := Fintype.card T
  let E := (Fintype.equivFin T).symm
  let F : Fin N → b4c_MeroFun ℂ C := fun i ↦ (E i).val
  have hsi : Function.Injective (fun x : C ↦ fun i ↦ F i x) := by
    intro x y h
    apply hsep x y
    intro a ha
    have he := congrFun h ((Fintype.equivFin T) ⟨a, ha⟩)
    simpa only [F, E, Equiv.symm_apply_apply] using he
  have hdi : ∀ x : C, ∃ i, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (F i) x ≠ 0 := by
    intro x
    obtain ⟨a, ha, hd⟩ := hder x
    refine ⟨(Fintype.equivFin T) ⟨a, ha⟩, ?_⟩
    have he : F ((Fintype.equivFin T) ⟨a, ha⟩) = a :=
      congrArg Subtype.val ((Fintype.equivFin T).symm_apply_apply ⟨a, ha⟩)
    rw [he]
    exact hd
  let A : Over (Spec ↧ℂ) := Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))
  letI : IsIntegral A.left := s0_complex_projective_integral 1
  letI : SmoothOfRelativeDimension 1 A.hom := s0_complex_projective_relative_dimension 1
  letI : Smooth A.hom := SmoothOfRelativeDimension.smooth 1 A.hom
  letI : IsProjective A.hom := s0_projective_space_projective 1 (Spec ↧ℂ)
  let X := g3_power A N
  letI : SmoothOfRelativeDimension N X.hom := by
    simpa only [Nat.mul_one] using spec_g3_smoothOfRelativeDimension_power A 1 N
  let f : C → ComplexPoint X := fun x ↦ (s0_power_point_homeomorph A N).symm
    (fun i ↦ s0_sphere_projective_homeomorph (F i x))
  obtain ⟨he, hf, ha⟩ := s0_sphere_coordinates_analytic_image N F hsi hdi
  have hd : TopologicalSpace.dim X.left = N := SmoothOfRelativeDimension.dim_eq X.hom N
  have ht : ∀ (d : ℕ) (_ : d = N) (hs : SmoothOfRelativeDimension d X.hom),
      letI := hs
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin d → ℂ) ω f ∧
        IsClosedAnalytic (Fin d → ℂ) (range f) := by
    intro d h hs
    subst d
    exact ⟨hf, ha⟩
  obtain ⟨hf', ha'⟩ := ht (TopologicalSpace.dim X.left) hd inferInstance
  obtain ⟨Z, hZ, hcar⟩ := chowG_setLevel X (range f) ha'
  exact ⟨X, inferInstance, inferInstance, inferInstance, f, Z, he, hf', hZ, hcar⟩

#print axioms s0_projective_carrier_of_sphere_coordinates
end HodgeLean.Foundations.Program
