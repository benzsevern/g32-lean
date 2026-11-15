import HodgeLean.Papers.G34SupplyDefs
import HodgeLean.Papers.PapersSupply
import HodgeLean.Papers.PapersMore

/-! # G34 Theorem A, stage 3: the Brauer/Schoen supply, open proof obligations -/

noncomputable section

open CategoryTheory

namespace HodgeLean.Papers

theorem g34s_generator_sq_aux (i : Fin 10) :
    skelg34_generator i * skelg34_generator i = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact Submodule.reflection_involutive ((ℂ ∙ skelg34_root i)ᗮ) x

theorem g34s_tuple_prod_aux : skelg34_tuple.prod = 1 := by
  have hs (i : Fin 10) : skelg34_generator i * skelg34_generator i = 1 :=
    g34s_generator_sq_aux i
  unfold skelg34_tuple
  induction List.finRange 10 with
  | nil => simp
  | cons i l ih => simp [hs i, ih]

theorem g34s_tuple_real_aux :
    ∀ g ∈ skelg34_tuple, ∃ w : skelg34_group, w * g * w⁻¹ = g⁻¹ := by
  intro g hg
  change g ∈ (List.finRange 10).flatMap
    (fun i => [skelg34_generator i, skelg34_generator i]) at hg
  simp at hg
  obtain ⟨i, rfl⟩ := hg
  refine ⟨1, ?_⟩
  simp [inv_eq_of_mul_eq_one_right (g34s_generator_sq_aux i)]

theorem g34s_supplier_admissible_aux [Finite skelg34_group] (S : skelg34_Supplier)
    (hh : 0 < (2 * skelg34_genus S.H skelg34_tuple - 2 +
      (papersExpsList S.H S.eps skelg34_tuple).length : ℤ)) :
    SupplierAdmissible S.m (skelg34_genus S.H skelg34_tuple)
      (papersExpsList S.H S.eps skelg34_tuple) := by
  have hm := S.hm
  letI : NeZero S.m := ⟨by omega⟩
  exact papers_g34_exps_tuple_admissible S.H S.eps skelg34_tuple
    g34s_tuple_real_aux g34s_tuple_prod_aux _ hh

theorem g34s_a_sigma_aux {k : Type*} [Field k] [CharZero k] [IsAlgClosed k] {G : Type*}
    [Group G] [Fintype G] {ι κ : Type*} [DecidableEq ι] (τ τbar : ι → FDRep k G)
    (η : κ → FDRep k G) (σ : FDRep k G) (i₀ : ι) (hσ : Simple σ) (hτ : ∀ i, Simple (τ i))
    (hτbar : ∀ i, Simple (τbar i)) (hστ : ∀ i, Nonempty (σ ≅ τ i) ↔ i = i₀)
    (hστbar : ∀ i, IsEmpty (σ ≅ τbar i)) :
    (papersACF τ τbar η σ.character).1 = Pi.single i₀ 1 := by
  letI := hσ
  funext i
  letI := hτ i
  letI := hτbar i
  simp only [papersACF, papersInner]
  rw [Fintype.card_eq_nat_card, FDRep.char_orthonormal, FDRep.char_orthonormal]
  simp [hστ i, hστbar i, Pi.single_apply]

open Classical in
theorem g34s_brauer_free_aux {k : Type*} [Field k] [CharZero k] {G : Type*} [Group G]
    [Fintype G] {ι κ : Type*} (τ τbar : ι → FDRep k G) (η : κ → FDRep k G) (σ : FDRep k G)
    (hbar : ∀ i g, (τbar i).character g = (τ i).character g⁻¹) {N : ℕ}
    (Hs : Fin N → Subgroup G) [∀ i, Fintype (Hs i)] (lam : (i : Fin N) → Hs i →* kˣ)
    (n : Fin N → ℤ)
    (hbrauer : ∀ g, σ.character g =
      ∑ i, (n i : k) * papersIndCF (Hs i) (papersLinChar (lam i)) g) :
    (papersACF τ τbar η σ.character).1 =
      ∑ i ∈ Finset.univ.filter (fun i => lam i ^ 2 ≠ 1),
        (n i : k) • (fun i' => ((papersA τ τbar η (Hs i) (lam i)).1 i' : k)) := by
  have h := congrArg Prod.fst (papers_g34_a_brauer τ τbar η σ Hs lam n hbrauer)
  simp only [Prod.fst_sum, Prod.smul_fst] at h
  rw [h, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split
  · rfl
  · simp only [not_ne_iff] at *
    rw [papers_g34_order_two_free τ τbar η hbar (Hs i) (lam i) ‹_›]
    have hz : (fun i' => ((0 : ι → ℤ) i' : k)) = 0 := by
      funext i'
      simp
    rw [hz, smul_zero]

open Classical in
theorem g34s_brauer_identity_aux {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {G : Type*} [Group G] [Fintype G] {ι κ : Type*} [DecidableEq ι] (τ τbar : ι → FDRep k G)
    (η : κ → FDRep k G) (σ : FDRep k G) (i₀ : ι) (hσ : Simple σ) (hτ : ∀ i, Simple (τ i))
    (hτbar : ∀ i, Simple (τbar i)) (hστ : ∀ i, Nonempty (σ ≅ τ i) ↔ i = i₀)
    (hστbar : ∀ i, IsEmpty (σ ≅ τbar i))
    (hbar : ∀ i g, (τbar i).character g = (τ i).character g⁻¹) {N : ℕ}
    (Hs : Fin N → Subgroup G) [∀ i, Fintype (Hs i)] (lam : (i : Fin N) → Hs i →* kˣ)
    (n : Fin N → ℤ)
    (hbrauer : ∀ g, σ.character g =
      ∑ i, (n i : k) * papersIndCF (Hs i) (papersLinChar (lam i)) g) :
    (Pi.single i₀ 1 : ι → k) =
      ∑ i ∈ Finset.univ.filter (fun i => lam i ^ 2 ≠ 1),
        (n i : k) • (fun i' => ((papersA τ τbar η (Hs i) (lam i)).1 i' : k)) := by
  rw [← g34s_a_sigma_aux τ τbar η σ i₀ hσ hτ hτbar hστ hστbar]
  exact g34s_brauer_free_aux τ τbar η σ hbar Hs lam n hbrauer

theorem g34s_example_supplier_aux :
    (39191040 : ℕ) = 2 ^ 9 * 3 ^ 7 * 5 * 7 ∧ (2 * 3 ^ 7 : ℕ) = 4374 ∧
      8 * (39191040 : ℤ) = 4374 * (2 * 35841 - 2) ∧ (2 * 35841 - 2 : ℤ) = 71680 ∧
      SupplierAdmissible 3 35841 [] := by
  norm_num [SupplierAdmissible]
  exact ⟨[], by simp, by simp⟩

theorem g34s_half_exponent_no_prime_aux (m p : ℕ) (hm : 4 ∣ m) (hp : p.Prime) (hpm : p ∣ m) :
    p ∣ m / 2 := by
  rw [Nat.dvd_div_iff_mul_dvd (by omega)]
  rcases hp.eq_two_or_odd with rfl | hpodd
  · exact hm
  · have hcop : Nat.Coprime 2 p := by
      rw [Nat.coprime_two_left]
      exact ⟨p / 2, by omega⟩
    exact hcop.mul_dvd_of_dvd_of_dvd (dvd_trans (by decide : 2 ∣ 4) hm) hpm

end HodgeLean.Papers
