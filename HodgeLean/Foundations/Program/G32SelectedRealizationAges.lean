import HodgeLean.Foundations.Program.G32SelectedRealizationCyclotomic

noncomputable section
namespace HodgeLean.Foundations.Program

theorem g32y_complementary_residue_sum {m : ℕ} [NeZero m]
    (u : (ZMod m)ˣ) (a b : ZMod m) (ha : a ≠ 0) (hab : a + b = 0) :
    ((((u : ZMod m) * a).val : ℚ) / m) + ((((u : ZMod m) * b).val : ℚ) / m) = 1 := by
  have hx : (u : ZMod m) * a ≠ 0 := by
    intro h
    apply ha
    have hh := congrArg (fun z : ZMod m ↦ (↑(u⁻¹) : ZMod m) * z) h
    simpa [← mul_assoc] using hh
  have hy : (u : ZMod m) * b = -((u : ZMod m) * a) := by
    have hh : (u : ZMod m) * a + (u : ZMod m) * b = 0 := by
      rw [← mul_add, hab, mul_zero]
    linear_combination hh
  letI : NeZero ((u : ZMod m) * a) := ⟨hx⟩
  have hs : ((u : ZMod m) * a).val + ((u : ZMod m) * b).val = m := by
    rw [hy, ZMod.val_neg_of_ne_zero]
    exact Nat.add_sub_of_le (ZMod.val_lt _).le
  have hsQ : (((u : ZMod m) * a).val : ℚ) + (((u : ZMod m) * b).val : ℚ) = m := by
    exact_mod_cast hs
  rw [← add_div, hsQ, div_self]
  exact_mod_cast NeZero.ne m

theorem g32y_paired_list_sum {A : Type*} (w : A → ℚ) (L : List (A × A))
    (h : ∀ p ∈ L, w p.1 + w p.2 = 1) :
    ((L.flatMap fun p ↦ [p.1, p.2]).map w).sum = L.length := by
  revert h
  induction L with
  | nil => intro _; rfl
  | cons p L ih =>
    intro h
    have hp := h p (by simp only [List.mem_cons, true_or])
    have ht : ∀ q ∈ L, w q.1 + w q.2 = 1 := fun q hq ↦ h q (List.mem_cons_of_mem _ hq)
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.length_cons,
      Nat.cast_add, Nat.cast_one]
    rw [hp, ih ht]
    ring

theorem g32y_simple_residue_sum {m : ℕ} [NeZero m]
    (α : List ℕ) (hα : ∀ a ∈ α, (a : ZMod m) ≠ 0)
    (hs : HodgeLean.Papers.IsSimpleExps m α) (u : (ZMod m)ˣ) :
    2 * (α.map fun a : ℕ ↦ ((((u : ZMod m) * (a : ZMod m)).val : ℚ) / m)).sum = α.length := by
  obtain ⟨L, hperm, hL⟩ := hs
  let w : ℕ → ℚ := fun a ↦ (((u : ZMod m) * (a : ZMod m)).val : ℚ) / m
  have hpair (p : ℕ × ℕ) (hp : p ∈ L) : w p.1 + w p.2 = 1 := by
    have h1 : p.1 ∈ α := hperm.mem_iff.mp
      (List.mem_flatMap.mpr ⟨p, hp, by simp only [List.mem_cons, true_or]⟩)
    have hab : (p.1 : ZMod m) + (p.2 : ZMod m) = 0 := by
      rw [← Nat.cast_add]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero (hL p hp))
    exact g32y_complementary_residue_sum u _ _ (hα _ h1) hab
  have hsum : (α.map w).sum = (L.length : ℚ) := by
    rw [← (hperm.map w).sum_eq]
    exact g32y_paired_list_sum w L hpair
  have hlen (l : List (ℕ × ℕ)) : (l.flatMap fun p ↦ [p.1, p.2]).length = 2 * l.length := by
    induction l with
    | nil => rfl
    | cons p l ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
      omega
  have hlenQ : (α.length : ℚ) = 2 * (L.length : ℚ) := by
    exact_mod_cast hperm.length_eq.symm.trans (hlen L)
  change 2 * (α.map w).sum = (α.length : ℚ)
  rw [hsum, hlenQ]

end HodgeLean.Foundations.Program
