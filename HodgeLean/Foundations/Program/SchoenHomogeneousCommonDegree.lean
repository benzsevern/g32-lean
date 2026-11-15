import HodgeLean.Foundations.Program.SchoenGradedFiniteType

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Finitely many positive degrees have a positive common multiple with positive quotients. -/
theorem s2_positive_common_degree {ι : Type} [Fintype ι] (d : ι → ℕ)
    (hd : ∀ i, 0 < d i) :
    ∃ D : ℕ, 0 < D ∧ ∃ e : ι → ℕ, (∀ i, 0 < e i) ∧ ∀ i, e i * d i = D := by
  classical
  let D := ∏ i, d i
  have hD : 0 < D := Finset.prod_pos fun i _ => hd i
  have hdiv (i : ι) : d i ∣ D := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  refine ⟨D, hD, fun i => D / d i, ?_, ?_⟩
  · intro i
    exact Nat.div_pos (Nat.le_of_dvd hD (hdiv i)) (hd i)
  · intro i
    exact Nat.div_mul_cancel (hdiv i)

/-- Positive powers place a finite family of positive homogeneous elements in one degree. -/
theorem s2_homogeneous_common_degree {A ι : Type} [CommRing A] [Fintype ι]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (v : ι → A)
    (hhom : ∀ i, ∃ d : ℕ, 0 < d ∧ v i ∈ 𝒜 d) :
    ∃ D : ℕ, 0 < D ∧ ∃ e : ι → ℕ, (∀ i, 0 < e i) ∧
      ∀ i, v i ^ e i ∈ 𝒜 D := by
  choose d hd hv using hhom
  obtain ⟨D, hD, e, he, hdegree⟩ := s2_positive_common_degree d hd
  refine ⟨D, hD, e, he, fun i => ?_⟩
  simpa only [smul_eq_mul, hdegree i] using SetLike.pow_mem_graded (e i) (hv i)

end HodgeLean.Foundations.Program
