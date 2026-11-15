import HodgeLean.Foundations.Program.G32WeilLineAssemblyGenerators
import HodgeLean.Foundations.Program.G32WeilLineAssemblyFiniteRank
import HodgeLean.Foundations.Program.G32WeilLineAssemblyRank

/-! Five reflection generators give `dim τ ≤ 5 r`, where `r` is the rank of
`τ(r₁) - 1`. The first twelve entries of the class datum contribute `12 r`.
Thus every nontrivial simple representation has positive Chevalley–Weil count.
The regular representation then detects a positive term for any supplier character.
-/

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory HodgeLean.Papers HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

theorem g32c_cw_positive (σ : FDRep ℂ g32p_G) [Simple σ]
    (hnt : ∃ g, σ.ρ g ≠ 1) : 0 < g32p_cwMult σ := by
  let r := Module.finrank ℂ (LinearMap.range (σ.ρ (b4b_generators 0) - 1))
  have hsecond : Module.finrank ℂ (LinearMap.range (σ.ρ (b4b_generators 1) - 1)) = r := by
    rw [← g32c_second_reflection_conjugate]
    rw [g32c_rank_conjugate, g32c_rank_inverse]
  have he : ∀ i : Fin 5,
      Module.finrank ℂ (LinearMap.range (σ.ρ (g32c_reflections i) - 1)) = r := by
    intro i
    fin_cases i
    · rfl
    · exact hsecond
    · exact g32c_rank_conjugate σ.ρ _ _
    · exact g32c_rank_conjugate σ.ρ _ _
    · exact g32c_rank_conjugate σ.ρ _ _
  have hd : Module.finrank ℂ σ ≤ 5 * r := by
    have h := g32c_rank_bound σ.ρ g32c_reflections (fun v hv =>
      g32c_fixed_eq_zero σ hnt v (g32c_fixed_by_reflections σ.ρ v hv))
    simpa only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h
  have hdpos : 0 < Module.finrank ℂ σ := by
    by_contra h
    have hz : Module.finrank ℂ σ = 0 := by omega
    haveI : Subsingleton σ := Module.finrank_zero_iff.mp hz
    obtain ⟨g, hg⟩ := hnt
    exact hg (LinearMap.ext fun v => Subsingleton.elim _ _)
  have hrpos : 0 < r := by omega
  let t := Module.finrank ℂ (LinearMap.range (σ.ρ ((b4b_generators 2)^2) - 1))
  have hsum : (∑ j : Fin 13,
      (Module.finrank ℂ (LinearMap.range (σ.ρ (g32p_classDatum j) - 1)) : ℤ)) =
      12 * (r : ℤ) + t := by
    have hf : (fun j : Fin 13 =>
        (Module.finrank ℂ (LinearMap.range (σ.ρ (g32p_classDatum j) - 1)) : ℤ)) =
        ![(r : ℤ),r,r,r,r,r,
          Module.finrank ℂ (LinearMap.range (σ.ρ (b4b_generators 1) - 1)),
          Module.finrank ℂ (LinearMap.range (σ.ρ (b4b_generators 1) - 1)),
          Module.finrank ℂ (LinearMap.range (σ.ρ (b4b_generators 1) - 1)),
          Module.finrank ℂ (LinearMap.range (σ.ρ (b4b_generators 1) - 1)),
          Module.finrank ℂ (LinearMap.range (σ.ρ (b4b_generators 1) - 1)),
          Module.finrank ℂ (LinearMap.range (σ.ρ (b4b_generators 1) - 1)),t] := by
      funext j
      fin_cases j <;> try rfl
      change (Module.finrank ℂ (LinearMap.range (σ.ρ (g32p_classDatum 12) - 1)) : ℤ) = t
      have hlast : g32p_classDatum 12 = (b4b_generators 2)^2 := by
        apply Subtype.ext
        change g32X g32h_omega * g32X g32h_omega = (g32X g32h_omega)^2
        rw [pow_two]
      exact congrArg (fun g : g32p_G =>
        (Module.finrank ℂ (LinearMap.range (σ.ρ g - 1)) : ℤ)) hlast
    rw [hf]
    simp only [hsecond]
    norm_num [Fin.sum_univ_succ]
    ring
  rw [g32p_cwMult, hsum]
  have hd' : (Module.finrank ℂ σ : ℤ) ≤ 5 * (r : ℤ) := by exact_mod_cast hd
  have hr' : 0 < (r : ℤ) := by exact_mod_cast hrpos
  have ht : 0 ≤ (t : ℤ) := Int.natCast_nonneg t
  omega

theorem g32c_supplier_cw_positive (S : g32p_Supplier)
    {I : Type} [Fintype I] (σ : I → FDRep ℂ g32p_G)
    (hσ : ∀ i, Simple (σ i))
    (hdist : ∀ i j, Nonempty (σ i ≅ σ j) → i = j)
    (hcov : ∀ τ : FDRep ℂ g32p_G, Simple τ → ∃ i, Nonempty (τ ≅ σ i)) :
    0 < ∑ i, (papersMult S.H (σ i) (g32rep_chi S) : ℤ) * g32p_cwMult (σ i) := by
  classical
  have hrank := g32c_regular_eigen_pos S.H (g32rep_chi S)
  rw [g32c_eigen_rank_sum σ g32c_regular hσ hdist hcov] at hrank
  obtain ⟨i, hi⟩ := Finset.sum_pos_iff.mp hrank
  have himult : 0 < papersMult S.H (σ i) (g32rep_chi S) := by
    have hp := hi.2
    by_contra hn
    have hz : papersMult S.H (σ i) (g32rep_chi S) = 0 := by omega
    rw [hz, zero_mul] at hp
    omega
  have hnontriv (j : I) (hj : 0 < papersMult S.H (σ j) (g32rep_chi S)) :
      ∃ g, (σ j).ρ g ≠ 1 := by
    by_contra hn
    have ht : ∀ g, (σ j).ρ g = 1 := by simpa only [not_exists, not_not] using hn
    have hz := g32c_trivial_eigen_bot S (σ j) ht
    have hdim := rfd_finrank_eigen_eq_papersMult (σ j) S.H (g32rep_chi S)
    rw [hz, finrank_bot] at hdim
    omega
  refine Finset.sum_pos' ?_ ⟨i, Finset.mem_univ i, ?_⟩
  · intro j _
    by_cases hj : 0 < papersMult S.H (σ j) (g32rep_chi S)
    · haveI := hσ j
      exact le_of_lt (mul_pos (show (0 : ℤ) < (papersMult S.H (σ j) (g32rep_chi S) : ℤ) by exact_mod_cast hj)
        (g32c_cw_positive (σ j) (hnontriv j hj)))
    · have hz : papersMult S.H (σ j) (g32rep_chi S) = 0 := by omega
      rw [hz, Nat.cast_zero, zero_mul]
  · haveI := hσ i
    exact mul_pos (show (0 : ℤ) < (papersMult S.H (σ i) (g32rep_chi S) : ℤ) by exact_mod_cast himult) (g32c_cw_positive (σ i) (hnontriv i himult))

end HodgeLean.Foundations.Program
