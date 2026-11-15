import HodgeLean.Foundations.Program.RigidStartingSystemHomAction

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program

def b65r_localCentralizerEquiv {n : ℕ}
    (T S C : (Matrix (Fin n) (Fin n) ℂ)ˣ) (hc : C*T*C⁻¹ = S) :
    b65r_centralizer T.val ≃ₗ[ℂ] LinearMap.ker (b65r_homAction S T - LinearMap.id) := by
  have hsc : S.val*C.val = C.val*T.val := by
    have h : S*C = C*T := by rw [← hc]; simp [mul_assoc]
    exact congrArg Units.val h
  have hcs : T.val*(C⁻¹).val = (C⁻¹).val*S.val := by
    have h : T*C⁻¹ = C⁻¹*S := by rw [← hc]; simp [mul_assoc]
    exact congrArg Units.val h
  exact {
    toFun X := ⟨C.val*X.val, by
      change S.val*(C.val*X.val)*(T⁻¹).val-C.val*X.val = 0
      have hx : T.val*X.val = X.val*T.val := X.property
      rw [← mul_assoc S.val C.val X.val, hsc, mul_assoc C.val T.val X.val, hx]
      simp [mul_assoc]⟩
    invFun Y := ⟨(C⁻¹).val*Y.val, by
      change T.val*((C⁻¹).val*Y.val) = ((C⁻¹).val*Y.val)*T.val
      have hy : S.val*Y.val*(T⁻¹).val = Y.val := by
        apply sub_eq_zero.mp
        exact Y.property
      have hy' : S.val*Y.val = Y.val*T.val := by
        have h := congrArg (fun Z ↦ Z*T.val) hy
        simpa only [mul_assoc, Units.inv_mul, mul_one] using h
      rw [← mul_assoc, hcs, mul_assoc, hy', mul_assoc]⟩
    left_inv X := by apply Subtype.ext; simp [mul_assoc]
    right_inv Y := by apply Subtype.ext; simp [mul_assoc]
    map_add' X Y := by apply Subtype.ext; exact mul_add _ _ _
    map_smul' c X := by apply Subtype.ext; exact mul_smul_comm _ _ _ }

end HodgeLean.Foundations.Program
