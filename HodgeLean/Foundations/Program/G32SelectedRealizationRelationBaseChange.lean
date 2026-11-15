import HodgeLean.Foundations.Program.G32SelectedRealizationCommonKernelBaseChange
import HodgeLean.Foundations.Program.G32SelectedRealizationAevalBaseChange

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem g32y_relation_baseChange {H U : Type*} [Finite H]
    [AddCommGroup U] [Module ℚ U] (T : H → Module.End ℚ U)
    (s₁ s₂ : Set H) (p : Polynomial ℚ) :
    let W : Submodule ℚ U :=
      (⨅ (h : H) (_ : h ∈ s₁), LinearMap.eqLocus (T h) LinearMap.id) ⊓
        ⨅ (h : H) (_ : h ∈ s₂), LinearMap.ker (Polynomial.aeval (T h) p)
    LinearMap.range (W.subtype.baseChange ℂ) =
      (⨅ (h : H) (_ : h ∈ s₁), LinearMap.eqLocus ((T h).baseChange ℂ) LinearMap.id) ⊓
        ⨅ (h : H) (_ : h ∈ s₂), LinearMap.ker
          (Polynomial.aeval ((T h).baseChange ℂ) (p.map (algebraMap ℚ ℂ))) := by
  classical
  let I := {h : H // h ∈ s₁} ⊕ {h : H // h ∈ s₂}
  letI : Fintype I := Fintype.ofFinite I
  let A : I → Module.End ℚ U := fun i ↦ match i with
    | .inl h => T h - LinearMap.id
    | .inr h => Polynomial.aeval (T h) p
  have hW : (⨅ i, LinearMap.ker (A i)) =
      (⨅ (h : H) (_ : h ∈ s₁), LinearMap.eqLocus (T h) LinearMap.id) ⊓
        ⨅ (h : H) (_ : h ∈ s₂), LinearMap.ker (Polynomial.aeval (T h) p) := by
    ext v
    simp [I, A, Submodule.mem_iInf, Sum.forall, Subtype.forall, LinearMap.mem_ker,
      LinearMap.mem_eqLocus, sub_eq_zero]
  have hC : (⨅ i, LinearMap.ker ((A i).baseChange ℂ)) =
      (⨅ (h : H) (_ : h ∈ s₁), LinearMap.eqLocus ((T h).baseChange ℂ) LinearMap.id) ⊓
        ⨅ (h : H) (_ : h ∈ s₂), LinearMap.ker
          (Polynomial.aeval ((T h).baseChange ℂ) (p.map (algebraMap ℚ ℂ))) := by
    ext v
    simp [I, A, Submodule.mem_iInf, Sum.forall, Subtype.forall, LinearMap.mem_ker,
      LinearMap.mem_eqLocus, sub_eq_zero, LinearMap.baseChange_sub,
      LinearMap.baseChange_id, g32y_aeval_baseChange]
  have hh := g32y_baseChange_common_kernel A
  rw [hW, hC] at hh
  exact hh

end HodgeLean.Foundations.Program
