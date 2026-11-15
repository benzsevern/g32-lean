import HodgeLean.Foundations.Program.MilneTensorPiRepresentation

noncomputable section
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def m1b_copiesAlgHom (r : ℕ) : Module.End ℂ V →ₐ[ℂ] Module.End ℂ (Fin r → V) where
  toFun := m1b_copies r
  map_one' := by ext v j; rfl
  map_mul' := by intros; ext v j; rfl
  map_zero' := by ext v j; rfl
  map_add' := by intros; ext v j; rfl
  commutes' := by intro z; ext v j; rfl

def m1b_matrixCopiesRepresentation (d m : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Module.End ℂ (Fin m → Fin d → ℂ) :=
  (m1b_copiesAlgHom m).comp (Matrix.toLinAlgEquiv' :
    Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin d → ℂ)).toAlgHom

end HodgeLean.Foundations.Program
