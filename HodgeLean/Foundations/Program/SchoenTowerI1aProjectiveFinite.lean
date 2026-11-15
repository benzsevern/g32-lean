import HodgeLean.Foundations.Program.SchoenTowerI1aHomogeneousAvoidance

import HodgeLean.Foundations.Program.SchoenTowerI1aHomogeneousAvoidanceLo
/-! # Finite projective point sets in affine charts
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Passing to maximal members extends homogeneous avoidance to a finite prime family.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.11, homogeneous construction. -/
theorem s2v_i1alo_homogeneous_finite_avoidance
    (A σ : Type) [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (s : Finset (HomogeneousIdeal 𝒜))
    (hP : ∀ I ∈ s, I.toIdeal.IsPrime)
    (hpos : ∀ I ∈ s, ∃ d : ℕ, 0 < d ∧ ∃ b : A, b ∈ 𝒜 d ∧ b ∉ I) :
    ∃ d : ℕ, 0 < d ∧ ∃ f : A, f ∈ 𝒜 d ∧ ∀ I ∈ s, f ∉ I := by
  classical
  let M := {I : s // Maximal (fun J : HomogeneousIdeal 𝒜 => J ∈ s) I.val}
  letI : Fintype M := Fintype.ofFinite M
  let P : M → HomogeneousIdeal 𝒜 := fun I => I.val.val
  have hP' (i : M) : (P i).toIdeal.IsPrime := hP _ i.val.property
  have hpos' (i : M) : ∃ d : ℕ, 0 < d ∧ ∃ b : A, b ∈ 𝒜 d ∧ b ∉ P i :=
    hpos _ i.val.property
  have hanti : ∀ i j : M, i ≠ j → ¬ P j ≤ P i := by
    intro i j hij hji
    have hij' := j.property.2 i.val.property hji
    exact hij (Subtype.ext (Subtype.ext (le_antisymm hij' hji)))
  obtain ⟨d, hd, f, hf, havoid⟩ :=
    s2v_i1alo_homogeneous_antichain_avoidance A σ M 𝒜 P hP' hanti hpos'
  refine ⟨d, hd, f, hf, ?_⟩
  intro I hI hfI
  obtain ⟨J, hIJ, hJ⟩ := s.exists_le_maximal hI
  let j : M := ⟨⟨J, hJ.1⟩, hJ⟩
  exact havoid j (hIJ hfI)

/-- A finite projective point set avoids one homogeneous element of positive degree.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.11, homogeneous construction. -/
theorem s2v_i1alo_projective_finite_homogeneous
    (A σ : Type) [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (s : Finset (ProjectiveSpectrum 𝒜)) :
    ∃ d : ℕ, 0 < d ∧ ∃ f : A, f ∈ 𝒜 d ∧ ∀ p ∈ s, f ∉ p.asHomogeneousIdeal := by
  classical
  let ideals := s.image ProjectiveSpectrum.asHomogeneousIdeal
  have hP : ∀ I ∈ ideals, I.toIdeal.IsPrime := by
    intro I hI
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hI
    exact p.isPrime
  have hpos : ∀ I ∈ ideals, ∃ d : ℕ, 0 < d ∧ ∃ b : A, b ∈ 𝒜 d ∧ b ∉ I := by
    intro I hI
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hI
    exact s2v_i1alo_positive_homogeneous_witness A σ 𝒜 p
  obtain ⟨d, hd, f, hf, havoid⟩ := s2v_i1alo_homogeneous_finite_avoidance A σ 𝒜 ideals hP hpos
  exact ⟨d, hd, f, hf, fun p hp => havoid _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)⟩

end HodgeLean.Foundations.Program
