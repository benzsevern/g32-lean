import HodgeLean.Foundations.Program.SchoenDegreeSubalgebraIrrelevant
import HodgeLean.Foundations.Program.SchoenProjRadicalCharts
import Mathlib.AlgebraicGeometry.Morphisms.Affine

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory
namespace HodgeLean.Foundations.Program

/-- Matching homogeneous pieces induce the actual degree-subalgebra Proj morphism. -/
def s2_degreeSubalgebraProjMap {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (M : ℕ) (hM : 0 < M)
    (hfull : ∀ k : ℕ, ∀ a : A, a ∈ 𝒜 (k * M) → a ∈ s2_degreeSubalgebra 𝒜 M) :
    letI := s2_degreeSubalgebraGrading 𝒜 M
    Proj 𝒜 ⟶ Proj (s2_subringGradedPiece 𝒜 (s2_degreeSubalgebra 𝒜 M).toSubring) := by
  letI := s2_degreeSubalgebraGrading 𝒜 M
  exact S2RadicalProj.map _ 𝒜
    (s2_subringGradedInclusion 𝒜 (s2_degreeSubalgebra 𝒜 M).toSubring)
    (s2_degreeSubalgebra_irrelevant_le_radical 𝒜 M hM hfull)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual matching degree-subalgebra Proj morphism is an isomorphism for a domain. -/
theorem s2_degreeSubalgebraProjMap_isIso {A : Type} [CommRing A] [IsDomain A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (M : ℕ) (hM : 0 < M)
    (hfull : ∀ k : ℕ, ∀ a : A, a ∈ 𝒜 (k * M) → a ∈ s2_degreeSubalgebra 𝒜 M) :
    letI := s2_degreeSubalgebraGrading 𝒜 M
    IsIso (s2_degreeSubalgebraProjMap 𝒜 M hM hfull) := by
  let R := s2_degreeSubalgebra 𝒜 M
  let ℬ := s2_subringGradedPiece 𝒜 R.toSubring
  letI : GradedRing ℬ := s2_degreeSubalgebraGrading 𝒜 M
  apply IsZariskiLocalAtTarget.of_openCover (P := .isomorphisms _)
    (Proj.affineOpenCover ℬ).openCover
  intro c
  have H := (S2RadicalProj.away_isPullback ℬ 𝒜
    (s2_subringGradedInclusion 𝒜 R.toSubring)
    (s2_degreeSubalgebra_irrelevant_le_radical 𝒜 M hM hfull)
    c.1.property c.2.val c.2.property).flip
  haveI : IsIso (CommRingCat.ofHom (HomogeneousLocalization.Away.map
      (s2_subringGradedInclusion 𝒜 R.toSubring) c.2.val)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (s2_degreeSubalgebraAwayMap_bijective 𝒜 M hfull c.2.val c.2.property)
  change IsIso (CategoryTheory.Limits.pullback.snd (s2_degreeSubalgebraProjMap 𝒜 M hM hfull)
    (Proj.awayι ℬ c.2.val c.2.property c.1.property))
  dsimp only [s2_degreeSubalgebraProjMap]
  rw [← H.isoPullback_inv_snd]
  infer_instance

end HodgeLean.Foundations.Program
