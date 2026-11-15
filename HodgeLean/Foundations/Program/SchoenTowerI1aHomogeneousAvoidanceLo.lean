import HodgeLean.Foundations.Program.SchoenTowerI1aPreDefs
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.Order.Preorder.Finite

/-! # Homogeneous separators for finite projective point sets
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A strict difference of homogeneous ideals has a homogeneous witness.
Source: Mathlib, Ideal.IsHomogeneous.mem_iff. -/
theorem s2v_i1alo_homogeneous_difference
    (A σ : Type) [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (I J : HomogeneousIdeal 𝒜) (h : ¬ I ≤ J) :
    ∃ (n : ℕ) (f : A), f ∈ 𝒜 n ∧ f ∈ I ∧ f ∉ J := by
  classical
  obtain ⟨f, hfI, hfJ⟩ := SetLike.not_le_iff_exists.mp h
  have hn : ∃ n, (DirectSum.decompose 𝒜 f n : A) ∉ J := by
    by_contra H
    push_neg at H
    exact hfJ (J.isHomogeneous.mem_iff.mpr H)
  obtain ⟨n, hn⟩ := hn
  exact ⟨n, _, SetLike.coe_mem _, I.isHomogeneous.mem_iff.mp hfI n, hn⟩

/-- A relevant homogeneous prime misses some homogeneous element of positive degree.
Source: Mathlib, HomogeneousIdeal.irrelevant_eq_iSup. -/
theorem s2v_i1alo_positive_homogeneous_witness
    (A σ : Type) [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (p : ProjectiveSpectrum 𝒜) :
    ∃ (n : ℕ), 0 < n ∧ ∃ f : A, f ∈ 𝒜 n ∧ f ∉ p.asHomogeneousIdeal := by
  classical
  by_contra H
  push_neg at H
  apply p.not_irrelevant_le
  have hle : (HomogeneousIdeal.irrelevant 𝒜).toAddSubmonoid ≤ p.asHomogeneousIdeal.toAddSubmonoid := by
    rw [HomogeneousIdeal.irrelevant_eq_iSup]
    exact iSup₂_le fun n hn f hf => H n hn f hf
  exact fun f hf => hle hf

/-- A finite antichain of homogeneous primes has a homogeneous element isolating each prime.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.11, homogeneous construction. -/
theorem s2v_i1alo_homogeneous_isolating_element
    (A σ ι : Type) [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] [Fintype ι]
    (P : ι → HomogeneousIdeal 𝒜) (hP : ∀ i, (P i).toIdeal.IsPrime)
    (hanti : ∀ i j, i ≠ j → ¬ P j ≤ P i)
    (i : ι) (d : ℕ) (hd : 0 < d) (b : A) (hb : b ∈ 𝒜 d) (hbP : b ∉ P i) :
    ∃ (n : ℕ), 0 < n ∧ ∃ f : A, f ∈ 𝒜 n ∧ f ∉ P i ∧ ∀ j, j ≠ i → f ∈ P j := by
  classical
  let J := {j : ι // j ≠ i}
  have hw (j : J) := s2v_i1alo_homogeneous_difference A σ 𝒜 (P j.val) (P i)
    (hanti i j.val (Ne.symm j.property))
  choose n u hu using hw
  let f := b * ∏ j : J, u j
  refine ⟨d + ∑ j : J, n j, by omega, f, ?_, ?_, ?_⟩
  · exact SetLike.mul_mem_graded hb
      (SetLike.prod_mem_graded 𝒜 n u (F := Finset.univ) (fun j _ => (hu j).1))
  · intro hf
    rcases (hP i).mem_or_mem hf with h | h
    · exact hbP h
    · obtain ⟨j, _, hj⟩ := (hP i).prod_mem_iff.mp h
      exact (hu j).2.2 hj
  · intro j hji
    apply (P j).toIdeal.mul_mem_left b
    apply (hP j).prod_mem_iff.mpr
    exact ⟨⟨j, hji⟩, Finset.mem_univ _, (hu ⟨j, hji⟩).2.1⟩

/-- Positive homogeneous witnesses for an antichain combine in one positive degree.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.11, homogeneous construction. -/
theorem s2v_i1alo_homogeneous_antichain_avoidance
    (A σ ι : Type) [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] [Fintype ι]
    (P : ι → HomogeneousIdeal 𝒜) (hP : ∀ i, (P i).toIdeal.IsPrime)
    (hanti : ∀ i j, i ≠ j → ¬ P j ≤ P i)
    (hpos : ∀ i, ∃ d : ℕ, 0 < d ∧ ∃ b : A, b ∈ 𝒜 d ∧ b ∉ P i) :
    ∃ d : ℕ, 0 < d ∧ ∃ f : A, f ∈ 𝒜 d ∧ ∀ i, f ∉ P i := by
  classical
  have hs (i : ι) : ∃ n : ℕ, 0 < n ∧ ∃ u : A,
      u ∈ 𝒜 n ∧ u ∉ P i ∧ ∀ j, j ≠ i → u ∈ P j := by
    obtain ⟨d, hd, b, hb, hbP⟩ := hpos i
    exact s2v_i1alo_homogeneous_isolating_element A σ ι 𝒜 P hP hanti i d hd b hb hbP
  choose d hd using hs
  choose u hu using fun i => (hd i).2
  let N := ∏ i, d i
  have hN : 0 < N := Finset.prod_pos (fun i _ => (hd i).1)
  have hdiv (i : ι) : d i ∣ N := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  have hepos (i : ι) : 0 < N / d i := Nat.div_pos (Nat.le_of_dvd hN (hdiv i)) (hd i).1
  have hpow (i : ι) : u i ^ (N / d i) ∈ 𝒜 N := by
    simpa only [nsmul_eq_mul, Nat.cast_id, Nat.div_mul_cancel (hdiv i)] using
      SetLike.pow_mem_graded (N / d i) (hu i).1
  refine ⟨N, hN, ∑ i, u i ^ (N / d i), sum_mem (fun i _ => hpow i), ?_⟩
  intro i hf
  have hrest : (∑ j ∈ Finset.univ.erase i, u j ^ (N / d j)) ∈ (P i).toIdeal := by
    apply (P i).toIdeal.sum_mem
    intro j hj
    exact (P i).toIdeal.pow_mem_of_mem
      ((hu j).2.2 i (Ne.symm (Finset.mem_erase.mp hj).1)) _ (hepos j)
  have hterm : u i ^ (N / d i) ∈ (P i).toIdeal := by
    apply ((P i).toIdeal.add_mem_iff_left hrest).mp
    rw [Finset.add_sum_erase Finset.univ (fun j : ι => u j ^ (N / d j)) (Finset.mem_univ i)]
    exact hf
  exact (hu i).2.1 ((hP i).mem_of_pow_mem _ hterm)

end HodgeLean.Foundations.Program
