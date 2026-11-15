import HodgeLean.Foundations.Program.SchoenSubalgebraProjectivity
import HodgeLean.Foundations.Program.SchoenDegreeSubalgebraGenerators

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory
namespace HodgeLean.Foundations.Program

/-- The actual degree-generated Proj has a projective presentation over the ambient degree-zero ring. -/
theorem s2_degreeSubalgebra_projective {A ι : Type} [CommRing A] [Fintype ι]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (v : ι → A) (d : ι → ℕ)
    (hd : ∀ i, 0 < d i) (hv : ∀ i, v i ∈ 𝒜 (d i))
    (hgen : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤) (M : ℕ) (hM : 0 < M) :
    letI := s2_degreeSubalgebraGrading 𝒜 M
    IsProjective (Proj.toSpecZero
      (s2_subringGradedPiece 𝒜 (s2_degreeSubalgebra 𝒜 M).toSubring) ≫
      Spec.map (CommRingCat.ofHom
        (s2_subalgebraDegreeZeroEquiv 𝒜 (s2_degreeSubalgebra 𝒜 M)).toRingHom)) := by
  letI := s2_degreeSubalgebraGrading 𝒜 M
  obtain ⟨n, w, hw, hgenw⟩ := s2_degreeSubalgebra_finite_generators 𝒜 v d hd hv hgen M
  exact s2_subalgebra_projective_of_commonDegree 𝒜 (s2_degreeSubalgebra 𝒜 M) M hM n w hw hgenw

end HodgeLean.Foundations.Program
