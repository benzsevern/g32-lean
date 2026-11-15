import HodgeLean.Foundations.Program.G32Native.PELNormalLieIdealStep
import HodgeLean.Foundations.Program.G32Native.PELInfiniteTangent
import HodgeLean.Foundations.Program.G32Native.PELMatrixTangentLie

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}

/-- An algebraic subgroup normalized by the ambient group determines a
Lie ideal by intersecting tangent spaces. -/
def pelNormalTangentIdeal (G H : MatrixAlgGroup k n)
    (hnormal : ∀ g ∈ G.carrier, ∀ h ∈ H.carrier, g⁻¹ * h * g ∈ H.carrier) :
    LieIdeal k (pelMatrixTangentLie G) where
  toSubmodule := (g1_lieAlgebra H).comap (pelMatrixTangentLie G).incl.toLinearMap
  lie_mem {X Y} hY := pel_normal_subgroup_lie_ideal_aux G H hnormal X.val Y.val X.property hY

/-- Simplicity and an infinite normalized algebraic intersection give
containment of the ambient identity component. -/
theorem pel_normal_contains_of_simple_tangent (G H : MatrixAlgGroup k n)
    [LieAlgebra.IsSimple k (pelMatrixTangentLie G)]
    (hnormal : ∀ g ∈ G.carrier, ∀ h ∈ H.carrier, g⁻¹ * h * g ∈ H.carrier)
    (hinfinite : ((g1_inter G H).carrier : Set (Matrix.GeneralLinearGroup (Fin n) k)).Infinite) :
    g1_identityComponent G ⊆ (H.carrier : Set (Matrix.GeneralLinearGroup (Fin n) k)) := by
  let J := pelNormalTangentIdeal G H hnormal
  have hJ : J ≠ ⊥ := by
    intro hbot
    apply pel_lie_ne_bot_of_infinite (g1_inter G H) hinfinite
    apply le_antisymm _ bot_le
    intro Y hY
    have hYG : Y ∈ g1_lieAlgebra G := g1_lie_mono (g1_inter G H) G inf_le_left hY
    have hYH : Y ∈ g1_lieAlgebra H := g1_lie_mono (g1_inter G H) H inf_le_right hY
    have hm : (⟨Y, hYG⟩ : pelMatrixTangentLie G) ∈ J := hYH
    rw [hbot, LieSubmodule.mem_bot] at hm
    exact congrArg Subtype.val hm
  have htop : J = ⊤ := (LieAlgebra.IsSimple.eq_bot_or_eq_top J).resolve_left hJ
  apply pel_identityComponent_subset_of_lie_le G H
  intro Y hY
  have hm : (⟨Y, hY⟩ : pelMatrixTangentLie G) ∈ J := by
    rw [htop]
    trivial
  exact hm

end HodgeLean.Foundations.Program.GeneralTypeIII
