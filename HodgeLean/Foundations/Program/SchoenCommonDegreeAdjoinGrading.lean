import HodgeLean.Foundations.Program.SchoenHomogeneousDegreeSupport
import HodgeLean.Foundations.Program.SchoenRescaledGrading
import HodgeLean.Foundations.Program.SchoenFixedRingGrading

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The actual subalgebra generated in one positive degree carries a grading in which
that degree is one. -/
def s2_commonDegreeAdjoinGrading {A ι : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (D : ℕ) (hD : 0 < D) (v : ι → A)
    (hv : ∀ i, v i ∈ 𝒜 D) :
    GradedRing (fun n => s2_subringGradedPiece 𝒜
      (Algebra.adjoin (𝒜 0) (Set.range v)).toSubring (D * n)) := by
  let R := (Algebra.adjoin (𝒜 0) (Set.range v)).toSubring
  have hs : ∀ a ∈ Set.range v, ∃ n, a ∈ 𝒜 n := by
    rintro _ ⟨i, rfl⟩
    exact ⟨D, hv i⟩
  letI := s2_homogeneousAdjoinGrading 𝒜 (Set.range v) hs
  apply s2_rescaledGrading (s2_subringGradedPiece 𝒜 R) D hD
  intro a n hn
  apply Subtype.ext
  change (s2_subringGradedInclusion 𝒜 R)
    (DirectSum.decompose (s2_subringGradedPiece 𝒜 R) a n) = 0
  rw [(s2_subringGradedInclusion 𝒜 R).map_directSumDecompose]
  exact s2_commonDegreeAdjoin_components_vanish 𝒜 D v hv a.val a.property n hn

end HodgeLean.Foundations.Program
