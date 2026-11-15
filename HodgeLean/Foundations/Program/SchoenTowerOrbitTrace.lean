import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

namespace HodgeLean.Foundations.Program

/-- Summing over a transitive finite group orbit counts each factor by the stabilizer order. -/
theorem s2t_transitive_orbit_sum {G ι B : Type*} [Group G] [Fintype G]
    [Fintype ι] [MulAction G ι] [AddCommMonoid B] (i₀ : ι)
    [Fintype (MulAction.stabilizer G i₀)]
    (htrans : ∀ i : ι, ∃ g : G, g • i₀ = i) (e : ι → B) :
    ∑ g : G, e (g • i₀) =
      Fintype.card (MulAction.stabilizer G i₀) • ∑ i : ι, e i := by
  classical
  have hcard (i : ι) : Fintype.card {g : G // g • i₀ = i} =
      Fintype.card (MulAction.stabilizer G i₀) := by
    obtain ⟨g, hg⟩ := htrans i
    let E : MulAction.stabilizer G i₀ ≃ {h : G // h • i₀ = i} :=
      { toFun := fun h => ⟨g * h.val, by rw [mul_smul, h.property]; exact hg⟩
        invFun := fun a => ⟨g⁻¹ * a.val, by
          change (g⁻¹ * a.val) • i₀ = i₀
          rw [mul_smul, a.property, ← hg, inv_smul_smul]⟩
        left_inv := fun h => by
          apply Subtype.ext
          change g⁻¹ * (g * h.val) = h.val
          exact inv_mul_cancel_left g h.val
        right_inv := fun a => by
          apply Subtype.ext
          change g * (g⁻¹ * a.val) = a.val
          exact mul_inv_cancel_left g a.val }
    exact Fintype.card_congr E.symm
  rw [← Fintype.sum_fiberwise' (fun g : G => g • i₀) e]
  simp only [Finset.sum_const, Finset.card_univ, hcard]
  rw [Finset.smul_sum]

end HodgeLean.Foundations.Program
