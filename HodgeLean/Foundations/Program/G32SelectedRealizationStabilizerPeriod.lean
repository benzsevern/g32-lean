import HodgeLean.Foundations.Program.G32SelectedRealizationStabilizerCoset
import Mathlib.Data.ZMod.QuotientGroup

noncomputable section
namespace HodgeLean.Foundations.Program

theorem g32y_stabilizer_period_card {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (H : Subgroup G) (x : X) (g : G)
    (hg : MulAction.stabilizer G x = Subgroup.zpowers g) (a : G) :
    orderOf g = Function.minimalPeriod (g • ·) (a : G ⧸ H) *
      Nat.card (MulAction.stabilizer H (a⁻¹ • x)) := by
  have horb : Nat.card (MulAction.orbit (Subgroup.zpowers g) (a : G ⧸ H)) =
      Function.minimalPeriod (g • ·) (a : G ⧸ H) := by
    rw [Nat.card_congr (MulAction.orbitZPowersEquiv g (a : G ⧸ H)), Nat.card_zmod]
  have hstab := Nat.card_congr (g32y_stabilizer_coset_equiv H x g hg a)
  have hprod := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup (Subgroup.zpowers g) (a : G ⧸ H))
  rw [Nat.card_prod, horb, ← hstab, Nat.card_zpowers] at hprod
  exact hprod.symm

end HodgeLean.Foundations.Program
