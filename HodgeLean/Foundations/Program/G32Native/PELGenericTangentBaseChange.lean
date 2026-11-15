import HodgeLean.Foundations.Program.G32Native.PELIsometryTangent
import HodgeLean.Foundations.Abdulali.SkewCentralizerBaseChange

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations HodgeLean.Foundations.Abdulali

private theorem skew_matrix_iff {V : Type*} [AddCommGroup V] [Module ℂ V]
    {n : ℕ} (b : Module.Basis (Fin n) ℂ V) (E : LinearMap.BilinForm ℂ V)
    (X : Module.End ℂ V) :
    (LinearMap.toMatrix b b X).transpose * LinearMap.toMatrix₂ b b E +
      LinearMap.toMatrix₂ b b E * LinearMap.toMatrix b b X = 0 ↔
      ∀ x y, E (X x) y + E x (X y) = 0 := by
  have hm : LinearMap.toMatrix₂ b b
      (E.compl₁₂ X LinearMap.id + E.compl₁₂ LinearMap.id X) =
      (LinearMap.toMatrix b b X).transpose * LinearMap.toMatrix₂ b b E +
      LinearMap.toMatrix₂ b b E * LinearMap.toMatrix b b X := by
    simp only [map_add, LinearMap.toMatrix₂_compl₁₂ b b b b,
      LinearMap.toMatrix_id, Matrix.transpose_one, mul_one, one_mul]
  rw [← hm, map_eq_zero_iff _ (LinearMap.toMatrix₂ b b).injective]
  constructor
  · intro h x y
    exact LinearMap.congr_fun₂ h x y
  · intro h
    ext x y
    exact h x y

/-- The tangent formula for the connected PEL group in a rational marking,
with precisely the finite-family complex span used by the type-III adapter.
No group equality, tangent equality, or rational Lie equality is assumed.
Source: Borel, Linear Algebraic Groups, second edition, §§3.5, 3.11;
Abdulali, Annals 155 (2002), §§3.1–3.3 (scalar extension of the centralizer). -/
theorem pelGenericGroup_tangent {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] {n k : ℕ} (b : Module.Basis (Fin n) ℚ V)
    (E : LinearMap.BilinForm ℚ V) (F : Fin k → Module.End ℚ V) :
    g1_lieOfSet (pelGenericGroup
      (LinearMap.toMatrix₂ (Algebra.TensorProduct.basis ℂ b)
        (Algebra.TensorProduct.basis ℂ b) (E.baseChange ℂ))
      (Set.range fun i => LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ b)
        (Algebra.TensorProduct.basis ℂ b) ((F i).baseChange ℂ))) =
    (complexSpan (skewCentralizerOfFamily E F)).map
      (LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ b)
        (Algebra.TensorProduct.basis ℂ b)).toLinearMap := by
  let c := Algebra.TensorProduct.basis ℂ b
  ext M
  constructor
  · intro hM
    let X := Matrix.toLin c c M
    have hm : LinearMap.toMatrix c c X = M := LinearMap.toMatrix_toLin c c M
    have hc := (lie_pelGenericGroup _ _ M).mp hM
    refine ⟨X, (skewCentralizerOfFamily_baseChange E F X).mpr ⟨?_, ?_⟩, hm⟩
    · apply (skew_matrix_iff c (E.baseChange ℂ) X).mp
      rw [hm]
      exact hc.1
    · intro i
      apply (LinearMap.toMatrix c c).injective
      rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, hm]
      exact hc.2 _ ⟨i, rfl⟩
  · rintro ⟨X, hX, rfl⟩
    obtain ⟨hs, hc⟩ := (skewCentralizerOfFamily_baseChange E F X).mp hX
    apply (lie_pelGenericGroup _ _ _).mpr
    refine ⟨(skew_matrix_iff c (E.baseChange ℂ) X).mpr hs, ?_⟩
    rintro _ ⟨i, rfl⟩
    simpa only [c, LinearMap.toMatrix_mul, LinearEquiv.coe_coe] using congrArg (LinearMap.toMatrix c c) (hc i)

#print axioms skew_matrix_iff
#print axioms pelGenericGroup_tangent
end HodgeLean.Foundations.Program.GeneralTypeIII
