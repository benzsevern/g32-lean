import HodgeLean.Foundations.Program.G32ContractionExteriorProduct
import Mathlib.LinearAlgebra.ExteriorPower.Basic

noncomputable section
set_option maxHeartbeats 200000

namespace HodgeLean.Foundations.Program

theorem g32c_orderedProduct_mem {K : Type*} [Field K] {r : ℕ}
    (N : Fin r → Type*) [∀ j, AddCommGroup (N j)] [∀ j, Module K (N j)]
    (n : Fin r → ℕ) (x : ∀ j, ⋀[K]^(n j) (N j)) :
    (List.ofFn fun j => ExteriorAlgebra.map (LinearMap.single K N j)
      (x j : ExteriorAlgebra K (N j))).prod ∈ ⋀[K]^(∑ j, n j) (∀ j, N j) := by
  have hm (j : Fin r) : ExteriorAlgebra.map (LinearMap.single K N j)
      (x j : ExteriorAlgebra K (N j)) ∈ ⋀[K]^(n j) (∀ j, N j) := by
    have h := LinearMap.congr_fun (exteriorPower.subtype_comp_map_eq (n := n j)
      (LinearMap.single K N j)) (x j)
    exact h ▸ (exteriorPower.map (n j) (LinearMap.single K N j) (x j)).property
  have h := SetLike.list_prod_ofFn_mem_graded (A := fun i : ℕ => ⋀[K]^i (∀ j, N j))
    n (fun j => ExteriorAlgebra.map (LinearMap.single K N j)
      (x j : ExteriorAlgebra K (N j))) hm
  simpa only [List.sum_ofFn] using h

end HodgeLean.Foundations.Program
