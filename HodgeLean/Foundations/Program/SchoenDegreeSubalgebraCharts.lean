import HodgeLean.Foundations.Program.SchoenSubringChartInjection
import HodgeLean.Foundations.Program.SchoenDegreeSubalgebra
import HodgeLean.Foundations.Program.SchoenFixedRingGrading
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open HomogeneousLocalization
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- If the degree-generated subalgebra contains all matching homogeneous pieces, its chart maps are surjective. -/
theorem s2_degreeSubalgebraAwayMap_surjective {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (M : ℕ)
    (hfull : ∀ k : ℕ, ∀ a : A, a ∈ 𝒜 (k * M) → a ∈ s2_degreeSubalgebra 𝒜 M)
    (f : s2_degreeSubalgebra 𝒜 M) {d : ℕ} (hf : (f : A) ∈ 𝒜 d) (hfne : (f : A) ≠ 0) :
    letI := s2_degreeSubalgebraGrading 𝒜 M
    Function.Surjective (Away.map
      (s2_subringGradedInclusion 𝒜 (s2_degreeSubalgebra 𝒜 M).toSubring) f) := by
  let R := s2_degreeSubalgebra 𝒜 M
  let ℬ := s2_subringGradedPiece 𝒜 R.toSubring
  letI : GradedRing ℬ := s2_degreeSubalgebraGrading 𝒜 M
  obtain ⟨r, hr⟩ := s2_degreeSubalgebra_degree_dvd 𝒜 M f.property hf hfne
  intro z
  obtain ⟨k, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf z
  have hamem : a ∈ R := by
    apply hfull (k * r) a
    convert ha using 1
    rw [smul_eq_mul, hr]
    ac_rfl
  let b : R := ⟨a, hamem⟩
  have hb : b ∈ ℬ (k • d) := ha
  refine ⟨Away.mk ℬ hf k b hb, ?_⟩
  rw [Away.map_mk]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual matching degree-subalgebra chart map is bijective, including the zero chart. -/
theorem s2_degreeSubalgebraAwayMap_bijective {A : Type} [CommRing A] [IsDomain A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (M : ℕ)
    (hfull : ∀ k : ℕ, ∀ a : A, a ∈ 𝒜 (k * M) → a ∈ s2_degreeSubalgebra 𝒜 M)
    (f : s2_degreeSubalgebra 𝒜 M) {d : ℕ} (hf : (f : A) ∈ 𝒜 d) :
    letI := s2_degreeSubalgebraGrading 𝒜 M
    Function.Bijective (Away.map
      (s2_subringGradedInclusion 𝒜 (s2_degreeSubalgebra 𝒜 M).toSubring) f) := by
  let R := s2_degreeSubalgebra 𝒜 M
  let ℬ := s2_subringGradedPiece 𝒜 R.toSubring
  letI : GradedRing ℬ := s2_degreeSubalgebraGrading 𝒜 M
  by_cases hfne : (f : A) = 0
  · have hf0 : f = 0 := Subtype.ext hfne
    subst f
    haveI : Subsingleton (Away ℬ (0 : R)) :=
      HomogeneousLocalization.subsingleton ℬ ⟨1, by simp only [pow_one]⟩
    haveI : Subsingleton (Away 𝒜
        ((s2_subringGradedInclusion 𝒜 R.toSubring) (0 : R))) :=
      HomogeneousLocalization.subsingleton 𝒜 ⟨1, by simp only [pow_one, map_zero]⟩
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun z => ⟨0, Subsingleton.elim _ _⟩⟩
  · exact ⟨s2_subringAwayMap_injective 𝒜 R.toSubring f hfne,
      s2_degreeSubalgebraAwayMap_surjective 𝒜 M hfull f hf hfne⟩

end HodgeLean.Foundations.Program
