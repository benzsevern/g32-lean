import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Tactic.FunProp

/-! The ambient band and the band over the carrier subtype have the same topology. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_ambient_band_homeomorph {E : Type*} [TopologicalSpace E]
    (A : Set E) (l u : E → ℝ) :
    ∃ e : {p : E × ℝ | p.1 ∈ A ∧ l p.1 ≤ p.2 ∧ p.2 ≤ u p.1} ≃ₜ
        {p : A × ℝ | p.2 ∈ Set.Icc (l p.1.val) (u p.1.val)},
      (∀ p, (e p).val.1.val = p.val.1 ∧ (e p).val.2 = p.val.2) ∧
      (∀ p, (e.symm p).val = (p.val.1.val, p.val.2)) := by
  let e : {p : E × ℝ | p.1 ∈ A ∧ l p.1 ≤ p.2 ∧ p.2 ≤ u p.1} ≃ₜ
      {p : A × ℝ | p.2 ∈ Set.Icc (l p.1.val) (u p.1.val)} :=
    { toFun := fun p => ⟨(⟨p.val.1, p.property.1⟩, p.val.2), p.property.2⟩
      invFun := fun p => ⟨(p.val.1.val, p.val.2), p.val.1.property, p.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact ⟨e, (fun _ => ⟨rfl, rfl⟩), (fun _ => rfl)⟩

end HodgeLean.Foundations.Program
