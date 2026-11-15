import HodgeLean.Foundations.Program.SchoenDegreeOneCoordinates

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Degree-one generators construct an actual projective presentation for an additive-subgroup grading. -/
def s2_degreeOneProjectivePresentation {R A : Type} [CommRing R] [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] [Algebra R (𝒜 0)]
    (hscalar : Function.Bijective (algebraMap R (𝒜 0)))
    (n : ℕ) (v : Fin (n + 1) → A) (hv : ∀ i, v i ∈ 𝒜 1)
    (hgen : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤) :
    ProjectiveSpace.Presentation
      (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))) := by
  let f := s2_integralGradedCoordinates 𝒜 v hv
  let hf := s2_integralCoordinates_irrelevant 𝒜 v hv hgen
  let j₀ := b54_relativeProj f hf
  have hj₀ : IsClosedImmersion j₀ := by
    apply b54_relativeProj_isClosedImmersion f hf X (isHomogeneous_X _)
      (b54_polynomial_irrelevant_le_variables _ _)
    simpa [f, s2_integralGradedCoordinates] using hgen
  let c := Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))
  have : IsIso (CommRingCat.ofHom (algebraMap R (𝒜 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hscalar
  have hc : IsIso c := by dsimp [c]; infer_instance
  let e : pullback (terminal.from (Spec (.of (𝒜 0))))
      (terminal.from (Proj (homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ)))) ⟶
      ProjectiveSpace (Fin (n + 1)) (Spec (.of R)) :=
    pullback.map _ _ _ _ c (𝟙 _) (𝟙 _) (by simp) (by simp)
  have : IsIso e := by dsimp [e, c]; infer_instance
  let j := j₀ ≫ e
  have : IsClosedImmersion j := by dsimp [j]; infer_instance
  refine ⟨n, j, ?_⟩
  simp [j, j₀, e, c, b54_relativeProj, ProjectiveSpace.toBase, Category.assoc]

/-- Degree-one generators over the actual coefficient ring give a projective structure morphism. -/
theorem s2_projective_of_degree_one {R A : Type} [CommRing R] [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] [Algebra R (𝒜 0)]
    (hscalar : Function.Bijective (algebraMap R (𝒜 0)))
    (n : ℕ) (v : Fin (n + 1) → A) (hv : ∀ i, v i ∈ 𝒜 1)
    (hgen : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤) :
    IsProjective (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))) :=
  ⟨⟨s2_degreeOneProjectivePresentation 𝒜 hscalar n v hv hgen⟩⟩

end HodgeLean.Foundations.Program
