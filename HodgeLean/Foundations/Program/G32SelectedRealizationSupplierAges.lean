import HodgeLean.Foundations.Program.G32SelectedRealizationAges
import HodgeLean.Papers.PapersSupplyProofs

noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem g32y_supplier_residue_sum {G : Type*} [Group G] [Finite G]
    {m : ℕ} [NeZero m] (H : Subgroup G) (χ : H →* Multiplicative (ZMod m))
    (gs : List G) (hs : IsSimpleExps m (papersExpsList H χ gs)) (u : (ZMod m)ˣ) :
    2 * ((papersExpsList H χ gs).map fun a : ℕ ↦
      ((((u : ZMod m) * (a : ZMod m)).val : ℚ) / m)).sum =
        (papersExpsList H χ gs).length := by
  apply g32y_simple_residue_sum _ _ hs u
  intro a ha
  rw [papersExpsList, Multiset.mem_toList, Multiset.mem_map] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  simpa only [ZMod.natCast_zmod_val] using papersExpsTuple_ne_zero H χ gs b hb

theorem g32y_simple_exponent_length_even {m : ℕ} {α : List ℕ}
    (hs : IsSimpleExps m α) : Even α.length := by
  obtain ⟨L, hp, _⟩ := hs
  have hl (l : List (ℕ × ℕ)) :
      (l.flatMap fun p ↦ [p.1, p.2]).length = l.length + l.length := by
    induction l with
    | nil => rfl
    | cons p l ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
      omega
  exact ⟨L.length, hp.length_eq.symm.trans (hl L)⟩

end HodgeLean.Foundations.Program
