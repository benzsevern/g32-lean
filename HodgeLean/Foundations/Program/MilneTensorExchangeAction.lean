import HodgeLean.Foundations.Program.MilneTensorExchangeCoordinates
import HodgeLean.Foundations.Program.MilneTensorGLMultiplicity

noncomputable section
namespace HodgeLean.Foundations.Program

def m1b_exchangeMultiplicityAction (d a b : ℕ)
    (X : Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d) (Fin d) ℂ) :
    Module.End ℂ ((Fin a → Fin d → ℂ) × (Fin b → Fin d → ℂ)) :=
  (m1b_copies a X.1.toLin').prodMap (m1b_copies b X.2.toLin')

def m1b_exchangeModuleEquiv (d a b : ℕ) :
    ((Fin a → Fin d → ℂ) × (Fin b → Fin d → ℂ)) ≃ₗ[ℂ]
      ((Fin a → Fin d → ℂ) × (Fin b → Module.Dual ℂ (Fin d → ℂ))) :=
  (LinearEquiv.refl ℂ (Fin a → Fin d → ℂ)).prodCongr
    (m1b_copiesEquiv (m1b_coordinateDual d) b)

theorem m1b_exchangeMultiplicity_conj (d a b : ℕ)
    (U : (Matrix (Fin d) (Fin d) ℂ)ˣ) :
    (m1b_exchangeModuleEquiv d a b).conj
      (m1b_exchangeMultiplicityAction d a b (U.val, U.inv.transpose)) =
      m1b_vectorDualMultiplicityAction a b
        (Units.map (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ]
          Module.End ℂ (Fin d → ℂ)).toMonoidHom U) := by
  apply LinearMap.ext
  intro v
  apply Prod.ext
  · funext j
    rfl
  · funext j
    change m1b_coordinateDual d (U.inv.transpose.mulVec ((m1b_coordinateDual d).symm (v.2 j))) =
      U.inv.toLin'.dualMap (v.2 j)
    rw [m1b_coordinateDual_transpose, LinearEquiv.apply_symm_apply]

end HodgeLean.Foundations.Program
