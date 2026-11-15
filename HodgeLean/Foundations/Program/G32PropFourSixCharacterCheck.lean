import HodgeLean.Foundations.Program.G32PropFourSixDeterminantRep
import HodgeLean.Foundations.Program.HurwitzPrymRexG32Core

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

-- Integer arithmetic for a character pairing, with conjugation already applied
-- to the one-dimensional character in the supplied entries.
def g32p_pairingSum : List (ℕ × HurwitzPrymRex_Zw × HurwitzPrymRex_Zw) → HurwitzPrymRex_Zw
  | [] => ⟨0, 0⟩
  | (n, a, b) :: xs => HurwitzPrymRex_Zw.add
      (HurwitzPrymRex_Zw.mul ⟨n, 0⟩ (HurwitzPrymRex_Zw.mul a b))
      (g32p_pairingSum xs)

def g32p_pairingCheck (order multiplicity : ℕ)
    (xs : List (ℕ × HurwitzPrymRex_Zw × HurwitzPrymRex_Zw)) : Bool :=
  decide (g32p_pairingSum xs = ⟨order * multiplicity, 0⟩)

theorem g32p_pairingSum_eval (xs : List (ℕ × HurwitzPrymRex_Zw × HurwitzPrymRex_Zw)) :
    HurwitzPrymRex_ev g32h_omega (g32p_pairingSum xs) =
      (xs.map (fun x => (x.1 : ℂ) * HurwitzPrymRex_ev g32h_omega x.2.1 *
        HurwitzPrymRex_ev g32h_omega x.2.2)).sum := by
  induction xs with
  | nil => simp [g32p_pairingSum, HurwitzPrymRex_ev]
  | cons x xs ih =>
    rcases x with ⟨n, a, b⟩
    simp only [g32p_pairingSum, HurwitzPrymRex_ev_add,
      HurwitzPrymRex_ev_mul g32h_omega_sq_add, List.map_cons, List.sum_cons, ih]
    simp [HurwitzPrymRex_ev, mul_assoc]

theorem g32p_pairingCheck_sound (order multiplicity : ℕ)
    (xs : List (ℕ × HurwitzPrymRex_Zw × HurwitzPrymRex_Zw))
    (h : g32p_pairingCheck order multiplicity xs = true) :
    (xs.map (fun x => (x.1 : ℂ) * HurwitzPrymRex_ev g32h_omega x.2.1 *
      HurwitzPrymRex_ev g32h_omega x.2.2)).sum = (order : ℂ) * multiplicity := by
  have he : g32p_pairingSum xs = ⟨order * multiplicity, 0⟩ := of_decide_eq_true h
  rw [← g32p_pairingSum_eval, he]
  simp [HurwitzPrymRex_ev]

theorem g32p_pairingCheck_mult {G : Type*} [Group G]
    (H : Subgroup G) [Fintype H] (V : FDRep ℂ G) (χ : H →* ℂˣ)
    (multiplicity : ℕ)
    (xs : List (ℕ × HurwitzPrymRex_Zw × HurwitzPrymRex_Zw))
    (hsum : (∑ h : H, V.character h * (χ h⁻¹ : ℂ)) =
      (xs.map (fun x => (x.1 : ℂ) * HurwitzPrymRex_ev g32h_omega x.2.1 *
        HurwitzPrymRex_ev g32h_omega x.2.2)).sum)
    (hcheck : g32p_pairingCheck (Fintype.card H) multiplicity xs = true) :
    papersMult H V χ = multiplicity := by
  apply Nat.cast_injective (R := ℂ)
  rw [← papers_g32_mult_eq_inner]
  change (Fintype.card H : ℂ)⁻¹ * (∑ h : H, V.character h * (χ h⁻¹ : ℂ)) = _
  rw [hsum, g32p_pairingCheck_sound _ _ _ hcheck]
  have hn : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

end HodgeLean.Foundations.Program
