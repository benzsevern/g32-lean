import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import HodgeLean.Foundations.Program.SchoenHomogeneousCommonDegree

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Positive homogeneous algebra generators generate the irrelevant ideal. -/
theorem s2_irrelevant_le_span_homogeneous_generators {A ι : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (v : ι → A)
    (hhom : ∀ i, ∃ d : ℕ, 0 < d ∧ v i ∈ 𝒜 d)
    (hgen : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (Set.range v) := by
  intro x hx
  have hx0 : GradedRing.projZeroRingHom 𝒜 x = 0 := hx
  suffices x - GradedRing.projZeroRingHom 𝒜 x ∈ Ideal.span (Set.range v) by
    simpa [hx0] using this
  clear hx hx0
  have hmem : x ∈ Algebra.adjoin (𝒜 0) (Set.range v) := by rw [hgen]; trivial
  induction hmem using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨d, hd, hv⟩ := hhom i
    rw [GradedRing.projZeroRingHom_apply, DirectSum.decompose_of_mem_ne 𝒜 hv hd.ne', sub_zero]
    exact Ideal.subset_span (Set.mem_range_self i)
  | algebraMap c =>
    have hc : GradedRing.projZeroRingHom 𝒜 (algebraMap (𝒜 0) A c) = algebraMap (𝒜 0) A c :=
      DirectSum.decompose_of_mem_same 𝒜 c.property
    rw [hc, sub_self]
    exact Ideal.zero_mem _
  | add x y _ _ hx hy =>
    simpa only [map_add, add_sub_add_comm] using Ideal.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    convert Ideal.add_mem _ (Ideal.mul_mem_left _ x hy)
      (Ideal.mul_mem_right (GradedRing.projZeroRingHom 𝒜 y) _ hx) using 1
    rw [map_mul]
    ring

/-- Powers of positive homogeneous generators control the irrelevant ideal up to radical. -/
theorem s2_irrelevant_le_radical_span_generatorPowers {A ι : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (v : ι → A)
    (hhom : ∀ i, ∃ d : ℕ, 0 < d ∧ v i ∈ 𝒜 d)
    (hgen : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤) (e : ι → ℕ) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      (Ideal.span (Set.range fun i => v i ^ e i)).radical := by
  apply (s2_irrelevant_le_span_homogeneous_generators 𝒜 v hhom hgen).trans
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact ⟨e i, Ideal.subset_span (Set.mem_range_self i)⟩

end HodgeLean.Foundations.Program
