import HodgeLean.Foundations.Program.RigidStartingSystemScott
import HodgeLean.Foundations.Program.RigidStartingSystemLocalIntertwiners
import HodgeLean.Foundations.Program.RigidStartingSystemIntertwiners
import HodgeLean.Foundations.Program.RigidStartingSystemHomDual

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program

theorem b65r_nonzero_intertwiner {n r : ℕ}
    (T S : Fin r → (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hT : (List.ofFn T).prod = 1) (hS : (List.ofFn S).prod = 1)
    (hidx : b65r_index (fun i ↦ (T i).val) = 2)
    (hloc : ∀ i, ∃ C : (Matrix (Fin n) (Fin n) ℂ)ˣ, C*T i*C⁻¹ = S i) :
    (∃ X : Matrix (Fin n) (Fin n) ℂ, X ≠ 0 ∧ ∀ i, (S i).val*X = X*(T i).val) ∨
    (∃ Y : Matrix (Fin n) (Fin n) ℂ, Y ≠ 0 ∧ ∀ i, (T i).val*Y = Y*(S i).val) := by
  classical
  by_cases hleft : ∃ X : Matrix (Fin n) (Fin n) ℂ, X ≠ 0 ∧ ∀ i, (S i).val*X = X*(T i).val
  · exact Or.inl hleft
  by_cases hright : ∃ Y : Matrix (Fin n) (Fin n) ℂ, Y ≠ 0 ∧ ∀ i, (T i).val*Y = Y*(S i).val
  · exact Or.inr hright
  exfalso
  let F := fun i ↦ b65r_homAction (S i) (T i)
  have hfix (X : Matrix (Fin n) (Fin n) ℂ) (hx : ∀ i, F i X = X) : X = 0 := by
    by_contra hX
    apply hleft
    refine ⟨X,hX,?_⟩
    intro i
    have he := hx i
    change (S i).val*X*((T i)⁻¹).val = X at he
    have hh := congrArg (fun Z ↦ Z*(T i).val) he
    simpa only [mul_assoc, Units.inv_mul, mul_one] using hh
  have hdual (f : Module.Dual ℂ (Matrix (Fin n) (Fin n) ℂ))
      (hf : ∀ i, f.comp (F i) = f) : f = 0 := by
    let Y := (b65r_traceDualEquiv n).symm f
    have heq : b65r_traceDual n Y = f := (b65r_traceDualEquiv n).apply_symm_apply f
    have hy : ∀ i, (b65r_traceDual n Y).comp (b65r_homAction (S i) (T i)) =
        b65r_traceDual n Y := by rw [heq]; exact hf
    have hint := b65r_dual_fixed_intertwiner T S Y hy
    have hY : Y = 0 := by
      by_contra hY
      exact hright ⟨Y,hY,hint⟩
    rw [← heq,hY,map_zero]
  have hbound := b65r_scott_bound F (b65r_homAction_prod T S hT hS) hfix hdual
  let N := Module.finrank ℂ (Matrix (Fin n) (Fin n) ℂ)
  change 2*N ≤ ∑ i : Fin r, Module.finrank ℂ (LinearMap.range (b65r_difference F i)) at hbound
  have hker (i : Fin r) : Module.finrank ℂ (LinearMap.ker (b65r_difference F i)) =
      Module.finrank ℂ (b65r_centralizer (T i).val) := by
    exact (b65r_localCentralizerEquiv (T i) (S i) (Classical.choose (hloc i))
      (Classical.choose_spec (hloc i))).finrank_eq.symm
  have hrank :
      (∑ i : Fin r, Module.finrank ℂ (LinearMap.range (b65r_difference F i))) +
      (∑ i : Fin r, Module.finrank ℂ (b65r_centralizer (T i).val)) = r*N := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _i : Fin r, N := by
        apply Finset.sum_congr rfl
        intro i _
        have he := (b65r_difference F i).finrank_range_add_finrank_ker
        rw [hker i] at he
        exact he
      _ = _ := by simp
  have hN : N = n^2 := by
    change Module.finrank ℂ (Fin n → Fin n → ℂ) = n^2
    simp [Module.finrank_pi_fintype, pow_two]
  have hNZ : (N : ℤ) = (n : ℤ)^2 := by exact_mod_cast hN
  dsimp only [b65r_index] at hidx
  rw [← hNZ] at hidx
  have hB : (2 : ℤ)*(N : ℤ) ≤
      ∑ i : Fin r, (Module.finrank ℂ (LinearMap.range (b65r_difference F i)) : ℤ) := by
    exact_mod_cast hbound
  have hR :
      (∑ i : Fin r, (Module.finrank ℂ (LinearMap.range (b65r_difference F i)) : ℤ)) +
      (∑ i : Fin r, (Module.finrank ℂ (b65r_centralizer (T i).val) : ℤ)) = (r : ℤ)*(N : ℤ) := by
    exact_mod_cast hrank
  nlinarith

theorem b65r_simultaneous_conjugacy {n r : ℕ}
    (T S : Fin r → (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hT : (List.ofFn T).prod = 1) (hS : (List.ofFn S).prod = 1)
    (hirr : ∀ W : Submodule ℂ (Fin n → ℂ),
      (∀ i v, v ∈ W → (T i).val.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hidx : b65r_index (fun i ↦ (T i).val) = 2)
    (hloc : ∀ i, ∃ C : (Matrix (Fin n) (Fin n) ℂ)ˣ, C*T i*C⁻¹ = S i) :
    ∃ C : (Matrix (Fin n) (Fin n) ℂ)ˣ, ∀ i, C*T i*C⁻¹ = S i := by
  rcases b65r_nonzero_intertwiner T S hT hS hidx hloc with ⟨X,hX,hint⟩ | ⟨Y,hY,hint⟩
  · have hu := b65r_intertwiner_isUnit (fun i ↦ (T i).val) (fun i ↦ (S i).val) hirr X hX hint
    let C := hu.unit
    have hC : C.val = X := hu.unit_spec
    refine ⟨C,?_⟩
    intro i
    have he : (S i).val*C.val = C.val*(T i).val := by rw [hC]; exact hint i
    apply Units.ext
    change C.val*(T i).val*(C⁻¹).val = (S i).val
    rw [← he]
    simp [mul_assoc]
  · have hu := b65r_reverse_intertwiner_isUnit (fun i ↦ (T i).val) (fun i ↦ (S i).val)
      hirr Y hY hint
    let D := hu.unit
    have hD : D.val = Y := hu.unit_spec
    refine ⟨D⁻¹,?_⟩
    intro i
    have he : T i*D = D*S i := by
      apply Units.ext
      change (T i).val*D.val = D.val*(S i).val
      rw [hD]
      exact hint i
    rw [inv_inv, mul_assoc, he, ← mul_assoc, inv_mul_cancel, one_mul]

end HodgeLean.Foundations.Program
