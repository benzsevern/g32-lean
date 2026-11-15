import Mathlib

noncomputable section
open Set
namespace HodgeLean.Foundations.Program

theorem rf7_sum_quotient_stabilizer_card {G U B : Type} [Group G] [MulAction G U]
    (h : B → G) (b : B) (q : G ⧸ Subgroup.zpowers (h b)) :
    Nat.card (MulAction.stabilizer G
      (Sum.inr ⟨b, q⟩ : U ⊕ Σ a : B, G ⧸ Subgroup.zpowers (h a))) = orderOf (h b) := by
  have hs : MulAction.stabilizer G
      (Sum.inr ⟨b, q⟩ : U ⊕ Σ a : B, G ⧸ Subgroup.zpowers (h a)) = MulAction.stabilizer G q := by
    ext g
    change (Sum.inr ⟨b, g • q⟩ : U ⊕ Σ a : B, G ⧸ Subgroup.zpowers (h a)) = Sum.inr ⟨b, q⟩ ↔ g • q = q
    simp
  rw [hs]
  induction q using Quotient.inductionOn with
  | h g =>
    have hg : (QuotientGroup.mk g : G ⧸ Subgroup.zpowers (h b)) = g • ((1 : G) : G ⧸ Subgroup.zpowers (h b)) := by simp
    have hc := Nat.card_congr (MulAction.stabilizerEquivStabilizer hg).toEquiv
    rw [MulAction.stabilizer_quotient, Nat.card_zpowers] at hc
    exact hc.symm

end HodgeLean.Foundations.Program
