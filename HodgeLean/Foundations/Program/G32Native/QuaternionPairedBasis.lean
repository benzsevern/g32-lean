import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Tactic.FinCases

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.QuaternionGraph
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Product indexing for two copies of one finite frame. -/
def frameIndexEquiv (n : ℕ) : (Fin n ⊕ Fin n) ≃ Fin n × Fin 2 where
  toFun := Sum.elim (fun i => (i,0)) (fun i => (i,1))
  invFun p := if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
  left_inv x := by cases x <;> simp
  right_inv p := by rcases p with ⟨i,k⟩; fin_cases k <;> simp

/-- A basis on one summand and an equivalence to its complement give paired frames. -/
def pairedBasis {n : ℕ} (E F : Submodule K V) (hEF : IsCompl E F)
    (b : Module.Basis (Fin n) K E) (e : E ≃ₗ[K] F) :
    Module.Basis (Fin n × Fin 2) K V :=
  ((b.prod (b.map e)).map (Submodule.prodEquivOfIsCompl E F hEF)).reindex (frameIndexEquiv n)

/-- The first paired frame is the original basis. -/
theorem pairedBasis_zero {n : ℕ} (E F : Submodule K V) (hEF : IsCompl E F)
    (b : Module.Basis (Fin n) K E) (e : E ≃ₗ[K] F) (i : Fin n) :
    pairedBasis E F hEF b e (i,0) = (b i : V) := by
  simp [pairedBasis, Module.Basis.reindex_apply, frameIndexEquiv,
    Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']

/-- The second paired frame is the image under the retained complement equivalence. -/
theorem pairedBasis_one {n : ℕ} (E F : Submodule K V) (hEF : IsCompl E F)
    (b : Module.Basis (Fin n) K E) (e : E ≃ₗ[K] F) (i : Fin n) :
    pairedBasis E F hEF b e (i,1) = (e (b i) : V) := by
  simp [pairedBasis, Module.Basis.reindex_apply, frameIndexEquiv,
    Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']

#print axioms pairedBasis
end HodgeLean.Foundations.Program.QuaternionGraph
