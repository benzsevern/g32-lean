import HodgeLean.Foundations.Program.G32SelectedRealizationProjector
import Mathlib.GroupTheory.GroupAction.Quotient

noncomputable section
namespace HodgeLean.Foundations.Program

theorem g32y_weighted_orbit_sum {H X : Type*} [Group H] [Fintype H] [Fintype X]
    [MulAction H X] (F : X → ℝ) (hF : ∀ (h : H) (x : X), F (h • x) = F x) :
    letI : Fintype (Quotient (MulAction.orbitRel H X)) := Fintype.ofFinite _
    ∑ x : X, (Nat.card (MulAction.stabilizer H x) : ℝ) / Nat.card H * F x =
      ∑ q : Quotient (MulAction.orbitRel H X), F q.out := by
  classical
  let Ω := Quotient (MulAction.orbitRel H X)
  letI : Fintype Ω := Fintype.ofFinite Ω
  let q : X → Ω := Quotient.mk''
  let value : Ω → ℝ := fun z ↦ (Nat.card (MulAction.stabilizer H z.out) : ℝ) /
    Nat.card H * F z.out
  have hval (x : X) : (Nat.card (MulAction.stabilizer H x) : ℝ) / Nat.card H * F x =
      value (q x) := by
    have hr : MulAction.orbitRel H X x (q x).out :=
      Quotient.exact (Quotient.out_eq' (q x)).symm
    have hs := Nat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel hr).toEquiv
    have hx : F x = F (q x).out := by
      obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hr
      exact (congrArg F hh.symm).trans (hF h _)
    dsimp only [value]
    rw [hs, hx]
  simp_rw [hval]
  rw [← Fintype.sum_fiberwise' q value]
  apply Finset.sum_congr rfl
  intro z _
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  let e : {x : X // q x = z} ≃ MulAction.orbit H z.out :=
    Equiv.subtypeEquivRight fun x ↦ by
      change (Quotient.mk'' x : Ω) = z ↔ x ∈ MulAction.orbit H z.out
      calc
        _ ↔ (Quotient.mk'' x : Ω) = Quotient.mk'' z.out := by rw [Quotient.out_eq']
        _ ↔ x ∈ MulAction.orbit H z.out := Quotient.eq''
  have hc : (Fintype.card {x : X // q x = z} : ℝ) *
      (Nat.card (MulAction.stabilizer H z.out) : ℝ) = Nat.card H := by
    have hh := MulAction.card_orbit_mul_card_stabilizer_eq_card_group H z.out
    rw [← Fintype.card_congr e] at hh
    simpa only [Nat.card_eq_fintype_card, Nat.cast_mul] using congrArg (Nat.cast : ℕ → ℝ) hh
  have hn : (Nat.card H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  dsimp only [value]
  field_simp [hn]
  linear_combination hc * F z.out

end HodgeLean.Foundations.Program
