import HodgeLean.Foundations.Program.G32Native.PELGenericGroupLie

noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations
variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

/-- A rational operator commutes with a rational space exactly when its
complexification commutes with the whole complex span.
Source: Bourbaki, Algebra, Chapter II, §5 (extension of scalars). -/
theorem commutes_complexSpan_iff (L : Submodule ℚ (Module.End ℚ V)) (T : Module.End ℚ V) :
    (∀ X ∈ L, X * T = T * X) ↔
      ∀ X ∈ complexSpan L, X * T.baseChange ℂ = T.baseChange ℂ * X := by
  constructor
  · intro h X hX
    induction hX using Submodule.span_induction with
    | mem X hX =>
      obtain ⟨Y, hY, rfl⟩ := hX
      simpa only [Module.End.mul_eq_comp, LinearMap.baseChange_comp] using
        congrArg (fun Z : Module.End ℚ V => Z.baseChange ℂ) (h Y hY)
    | zero => simp only [zero_mul, mul_zero]
    | add X Y hX hY ihX ihY =>
      rw [add_mul, mul_add, ihX, ihY]
    | smul z X hX ih =>
      simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ih]
  · intro h X hX
    apply LinearMap.baseChangeHom_injective (R := ℚ) (S := ℂ) (M := V) (N := V)
    change (X * T).baseChange ℂ = (T * X).baseChange ℂ
    simpa only [Module.End.mul_eq_comp, LinearMap.baseChange_comp] using
      h (X.baseChange ℂ) (Submodule.subset_span ⟨X, hX, rfl⟩)

/-- A rational commutant is determined by the actual algebraic Hodge group's
complex tangent in any rational basis. This is a criterion on matrices and
uses no genericity hypothesis.
Source: Deligne, Hodge cycles on abelian varieties, §3;
Borel, Linear Algebraic Groups, second edition, §3.5. -/
theorem commutant_iff_group_tangent
    (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)
    {n : ℕ} (b : Module.Basis (Fin n) ℚ V) (T : Module.End ℚ V) :
    T ∈ Subalgebra.centralizer ℚ
      (hodgeLieAlgebra H hH : Set (Module.End ℚ V)) ↔
      ∀ M ∈ g1_lieOfSet (g2_hodgeGroup H hH b),
        M * (LinearMap.toMatrix b b T).map (algebraMap ℚ ℂ) =
          (LinearMap.toMatrix b b T).map (algebraMap ℚ ℂ) * M := by
  rw [g2_lie_hodgeGroup]
  have hc := commutes_complexSpan_iff (hodgeLieAlgebra H hH).toSubmodule T
  rw [Subalgebra.mem_centralizer_iff]
  constructor
  · intro h M hM
    obtain ⟨X, hX, rfl⟩ := hM
    have he := congrArg (LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ b)
      (Algebra.TensorProduct.basis ℂ b)) (hc.mp (fun X hX => h X hX) X hX)
    simpa only [LinearMap.toMatrix_mul, LinearMap.toMatrix_baseChange,
      LinearEquiv.coe_coe] using he
  · intro h X hX
    apply hc.mpr _ X hX
    intro Y hY
    apply (LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ b)
      (Algebra.TensorProduct.basis ℂ b)).injective
    simpa only [LinearMap.toMatrix_mul, LinearMap.toMatrix_baseChange,
      LinearEquiv.coe_coe] using h _ ⟨Y, hY, rfl⟩

#print axioms commutes_complexSpan_iff
#print axioms commutant_iff_group_tangent
end HodgeLean.Foundations.Program.GeneralTypeIII
