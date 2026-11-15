import HodgeLean.Foundations.Program.G32ContractionTwoDefs
import HodgeLean.Foundations.Program.G32ContractionProductDegree
import HodgeLean.Foundations.Symplectic

noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

theorem g32c_ofFn_prod_mul {R : Type*} [Monoid R] {r : ℕ}
    (x y : Fin r → R) (hc : ∀ i j, Commute (x i) (y j)) :
    (List.ofFn x).prod * (List.ofFn y).prod = (List.ofFn fun j => x j * y j).prod := by
  induction r with
  | zero => simp only [List.ofFn_zero, List.prod_nil, one_mul]
  | succ r ih =>
      simp only [List.ofFn_succ, List.prod_cons]
      rw [← ih (fun j => x j.succ) (fun j => y j.succ) (fun i j => hc i.succ j.succ)]
      have ht : Commute (List.ofFn fun j : Fin r => x j.succ).prod (y 0) := by
        apply Commute.list_prod_left
        intro z hz
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
        exact hc j.succ 0
      calc
        (x 0 * (List.ofFn fun j : Fin r => x j.succ).prod) *
            (y 0 * (List.ofFn fun j : Fin r => y j.succ).prod) =
          x 0 * ((List.ofFn fun j : Fin r => x j.succ).prod * y 0) *
            (List.ofFn fun j : Fin r => y j.succ).prod := by simp only [mul_assoc]
        _ = _ := by rw [ht.eq]; simp only [mul_assoc]

theorem g32c_prodAbs_mul_even {r : ℕ} (N : Fin r → Type*)
    [∀ j, AddCommGroup (N j)] [∀ j, Module ℂ (N j)] (a b : Fin r → ℕ)
    (x : ∀ j, ⋀[ℂ]^(2 * a j) (N j)) (y : ∀ j, ⋀[ℂ]^(2 * b j) (N j)) :
    g32c_prodAbs (fun j => (x j : ExteriorAlgebra ℂ (N j))) *
      g32c_prodAbs (fun j => (y j : ExteriorAlgebra ℂ (N j))) =
    g32c_prodAbs (fun j => (x j : ExteriorAlgebra ℂ (N j)) * (y j : ExteriorAlgebra ℂ (N j))) := by
  unfold g32c_prodAbs
  simp only [map_mul]
  apply g32c_ofFn_prod_mul
  intro i j
  let hx := exteriorPower.map (2 * a i) (LinearMap.single ℂ N i) (x i)
  let hy := exteriorPower.map (2 * b j) (LinearMap.single ℂ N j) (y j)
  have hh := Symplectic.commute_of_even hx hy
  simpa only [hx, hy, exteriorPower.coe_map] using hh


theorem g32c_gammaAbs_prodAbs {M : Type*} [AddCommGroup M] [Module ℂ M] {r : ℕ}
    {N : Fin r → Type*} [∀ j, AddCommGroup (N j)] [∀ j, Module ℂ (N j)]
    (w : ExteriorAlgebra ℂ M) (Z : ∀ j, ExteriorAlgebra ℂ (N j)) :
    g32c_gammaAbs w Z = ExteriorAlgebra.map (LinearMap.inl ℂ M (∀ j, N j)) w *
      ExteriorAlgebra.map (LinearMap.inr ℂ M (∀ j, N j)) (g32c_prodAbs Z) := by
  unfold g32c_gammaAbs g32c_prodAbs
  rw [map_list_prod, List.map_ofFn]
  congr 1
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  change ExteriorAlgebra.map (LinearMap.inr ℂ M (∀ j, N j) ∘ₗ
    LinearMap.single ℂ N j) (Z j) =
      ExteriorAlgebra.map (LinearMap.inr ℂ M (∀ j, N j))
        (ExteriorAlgebra.map (LinearMap.single ℂ N j) (Z j))
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]

end HodgeLean.Foundations.Program
