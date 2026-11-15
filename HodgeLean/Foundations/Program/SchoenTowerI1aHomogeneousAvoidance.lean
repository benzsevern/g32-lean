import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.Order.Preorder.Finite

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_homogeneous_difference
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {I J : Ideal A} (hI : I.IsHomogeneous 𝒜) (hJ : J.IsHomogeneous 𝒜)
    (h : ¬ I ≤ J) : ∃ (d : ℕ) (f : A), f ∈ 𝒜 d ∧ f ∈ I ∧ f ∉ J := by
  obtain ⟨f, hfI, hfJ⟩ := SetLike.not_le_iff_exists.mp h
  have hn : ¬ ∀ d, (DirectSum.decompose 𝒜 f d : A) ∈ J :=
    fun h => hfJ (hJ.mem_iff.mpr h)
  obtain ⟨d, hd⟩ := not_forall.mp hn
  exact ⟨d, _, SetLike.coe_mem _, hI.mem_iff.mp hfI d, hd⟩

lemma s2v_i1ahi_homogeneous_product_separator
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (P : Ideal A) (hP : P.IsPrime) (hPh : P.IsHomogeneous 𝒜)
    (hpos : ∃ (d : ℕ) (f : A), 0 < d ∧ f ∈ 𝒜 d ∧ f ∉ P)
    (s : Finset (Ideal A)) (hh : ∀ J ∈ s, J.IsHomogeneous 𝒜)
    (hne : ∀ J ∈ s, ¬ J ≤ P) :
    ∃ (d : ℕ) (f : A), 0 < d ∧ f ∈ 𝒜 d ∧ f ∉ P ∧ ∀ J ∈ s, f ∈ J := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨d, f, hd, hf, hn⟩ := hpos
    exact ⟨d, f, hd, hf, hn, by simp only [Finset.notMem_empty, false_implies, implies_true]⟩
  | @insert J s hJs ih =>
    obtain ⟨d, f, hd, hf, hfn, hfs⟩ := ih
      (fun K hK => hh K (Finset.mem_insert_of_mem hK))
      (fun K hK => hne K (Finset.mem_insert_of_mem hK))
    obtain ⟨e, g, hg, hgJ, hgn⟩ := s2v_i1ahi_homogeneous_difference 𝒜
      (hh J (Finset.mem_insert_self _ _)) hPh (hne J (Finset.mem_insert_self _ _))
    refine ⟨d + e, f * g, by omega, SetLike.mul_mem_graded hf hg,
      fun h => (hP.mem_or_mem h).elim hfn hgn, ?_⟩
    intro K hK
    rcases Finset.mem_insert.mp hK with rfl | hK
    · exact K.mul_mem_left f hgJ
    · exact K.mul_mem_right g (hfs K hK)

lemma s2v_i1ahi_homogeneous_sum_separator
    {A σ ι : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (s : Finset ι) (P : ι → Ideal A) (hP : ∀ i ∈ s, (P i).IsPrime)
    (d : ι → ℕ) (f : ι → A)
    (hd : ∀ i ∈ s, 0 < d i) (hf : ∀ i ∈ s, f i ∈ 𝒜 (d i))
    (hn : ∀ i ∈ s, f i ∉ P i)
    (hc : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i ∈ P j) :
    ∃ (D : ℕ) (F : A), 0 < D ∧ F ∈ 𝒜 D ∧ ∀ i ∈ s, F ∉ P i := by
  classical
  let e (i : ι) := ∏ j ∈ s.erase i, d j
  let D := ∏ j ∈ s, d j
  have hepos (i : ι) : 0 < e i :=
    Finset.prod_pos (fun j hj => hd j (Finset.mem_of_mem_erase hj))
  have hedeg (i : ι) (hi : i ∈ s) : e i * d i = D := Finset.prod_erase_mul s d hi
  have hpow (i : ι) (hi : i ∈ s) : (f i) ^ e i ∈ 𝒜 D := by
    have h := SetLike.pow_mem_graded (e i) (hf i hi)
    simpa only [nsmul_eq_mul, Nat.cast_id, hedeg i hi] using h
  refine ⟨D, ∑ i ∈ s, (f i) ^ e i, Finset.prod_pos hd, ?_, ?_⟩
  · exact sum_mem hpow
  · intro i hi hsum
    have hrest : ∑ j ∈ s.erase i, (f j) ^ e j ∈ P i := by
      apply (P i).sum_mem
      intro j hj
      exact (P i).pow_mem_of_mem (hc j (Finset.mem_of_mem_erase hj) i hi
        (Finset.ne_of_mem_erase hj)) (e j) (hepos j)
    have heq := Finset.sum_erase_add s (fun j => (f j) ^ e j) hi
    rw [← heq] at hsum
    have hterm : (f i) ^ e i ∈ P i := by
      simpa only [add_sub_cancel_left] using (P i).sub_mem hsum hrest
    exact hn i hi (((hP i hi).pow_mem_iff_mem (e i) (hepos i)).mp hterm)

end HodgeLean.Foundations.Program
