import HodgeLean.Foundations.Program.SchoenCycleElementaryIdealPowers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- The mixed elementary coefficient ideal contains a power of the actual indexed root-origin ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_sigma_origin_power_le_coefficient_ideal (b : ℕ) (m : Fin b → ℕ) :
    ∃ k : ℕ, idealOfVars (Σ a, Fin (m a)) ℂ ^ k ≤
      Ideal.span (Set.range (fun v : Σ a, Fin (m a) =>
        rename (Sigma.mk v.1) (esymm (Fin (m v.1)) ℂ (v.2.val + 1)))) := by
  classical
  let J : Ideal (MvPolynomial (Σ a, Fin (m a)) ℂ) :=
    Ideal.span (Set.range (fun v : Σ a, Fin (m a) =>
      rename (Sigma.mk v.1) (esymm (Fin (m v.1)) ℂ (v.2.val + 1))))
  apply Ideal.exists_pow_le_of_le_radical_of_fg _ (idealOfVars_fg _ ℂ)
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨a, i⟩, rfl⟩
  let f : MvPolynomial (Fin (m a)) ℂ →ₐ[ℂ] MvPolynomial (Σ a, Fin (m a)) ℂ := rename (fun i : Fin (m a) => (⟨a, i⟩ : Σ a, Fin (m a)))
  let L : Ideal (MvPolynomial (Fin (m a)) ℂ) :=
    Ideal.span (Set.range (fun j : Fin (m a) => esymm (Fin (m a)) ℂ (j.val + 1)))
  have hle : L.map f.toRingHom ≤ J := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Ideal.subset_span ⟨⟨a, j⟩, rfl⟩
  refine ⟨m a, ?_⟩
  have h := hle (Ideal.mem_map_of_mem f.toRingHom (s2e_variable_power_mem_elementary_ideal (m a) i))
  change f (X i ^ m a) ∈ J at h
  rw [map_pow] at h
  change rename (fun i : Fin (m a) => (⟨a, i⟩ : Σ a, Fin (m a))) (X i) ^ m a ∈ J at h
  rw [rename_X] at h
  exact h

end HodgeLean.Foundations.Program
