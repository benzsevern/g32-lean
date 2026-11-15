import HodgeLean.Foundations.Program.SchoenTowerI1aHomogeneousAvoidance

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_finite_homogeneous_prime_avoidance
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (s : Finset (Ideal A)) (hh : ∀ P ∈ s, P.IsHomogeneous 𝒜)
    (hp : ∀ P ∈ s, P.IsPrime)
    (hpos : ∀ P ∈ s, ∃ (d : ℕ) (f : A), 0 < d ∧ f ∈ 𝒜 d ∧ f ∉ P) :
    ∃ (D : ℕ) (F : A), 0 < D ∧ F ∈ 𝒜 D ∧ ∀ P ∈ s, F ∉ P := by
  classical
  let t := s.filter (Maximal (· ∈ s))
  have ht (P : t) : P.val ∈ s := (Finset.mem_filter.mp P.property).1
  have hsep (P : t) : ∃ (d : ℕ) (f : A),
      0 < d ∧ f ∈ 𝒜 d ∧ f ∉ P.val ∧ ∀ J ∈ t.erase P.val, f ∈ J := by
    apply s2v_i1ahi_homogeneous_product_separator 𝒜 P.val (hp _ (ht P))
      (hh _ (ht P)) (hpos _ (ht P)) (t.erase P.val)
    · intro J hJ
      exact hh J (Finset.mem_filter.mp (Finset.mem_of_mem_erase hJ)).1
    · intro J hJ hJP
      have hmJ := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hJ)).2
      have hPJ := hmJ.2 (ht P) hJP
      exact Finset.ne_of_mem_erase hJ (le_antisymm hJP hPJ)
  choose d f hd hf hn hc using hsep
  obtain ⟨D, F, hD, hF, hFn⟩ := s2v_i1ahi_homogeneous_sum_separator 𝒜
    (Finset.univ : Finset t) (fun P => P.val) (fun P _ => hp _ (ht P)) d f
    (fun P _ => hd P) (fun P _ => hf P) (fun P _ => hn P)
    (fun P _ J _ hPJ => hc P J.val (Finset.mem_erase.mpr
      ⟨fun he => hPJ (Subtype.ext he.symm), J.property⟩))
  refine ⟨D, F, hD, hF, ?_⟩
  intro P hP hFP
  obtain ⟨J, hPJ, hJ⟩ := s.exists_le_maximal hP
  let j : t := ⟨J, Finset.mem_filter.mpr ⟨hJ.1, hJ⟩⟩
  exact hFn j (Finset.mem_univ _) (hPJ hFP)

end HodgeLean.Foundations.Program
