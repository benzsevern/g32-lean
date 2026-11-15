import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Continuous linear band coordinates with height first and base coordinates following it. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_band_coordinate_equiv (n : ℕ) :
    ∃ e : (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)),
      (∀ p, e p 0 = p.2) ∧ (∀ p i, e p i.succ = p.1 i) ∧
      (∀ z, (e.symm z).2 = z 0) ∧ (∀ z i, (e.symm z).1 i = z i.succ) := by
  let e : (EuclideanSpace ℝ (Fin n) × ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    { toFun := fun p => WithLp.toLp 2 (Fin.cons p.2 (fun i => p.1 i))
      invFun := fun z => (WithLp.toLp 2 (fun i : Fin n => z i.succ), z 0)
      left_inv := by
        intro p
        apply Prod.ext
        · ext i
          rfl
        · rfl
      right_inv := by
        intro z
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      map_add' := by
        intro p q
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      map_smul' := by
        intro a p
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl }
  exact ⟨e.toContinuousLinearEquiv, fun _ => rfl, fun _ _ => rfl,
    fun _ => rfl, fun _ _ => rfl⟩

end HodgeLean.Foundations.Program
