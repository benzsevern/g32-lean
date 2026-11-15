import HodgeLean.Foundations.Program.MilneTensorPairingChange

noncomputable section
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

def m1b_formDualEquiv (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate) :
    V ≃ₗ[ℂ] Module.Dual ℂ V :=
  LinearEquiv.ofInjectiveOfFinrankEq B
    (LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp hB.1)) (by simp)

def m1b_pairingChangeEquiv (B C : LinearMap.BilinForm ℂ V)
    (hB : B.Nondegenerate) (hC : C.Nondegenerate) : V ≃ₗ[ℂ] V :=
  (m1b_formDualEquiv B hB).trans (m1b_formDualEquiv C hC).symm

theorem m1b_pairingChangeEquiv_apply (B C : LinearMap.BilinForm ℂ V)
    (hB : B.Nondegenerate) (hC : C.Nondegenerate) (x y : V) :
    C (m1b_pairingChangeEquiv B C hB hC x) y = B x y := by
  change m1b_formDualEquiv C hC
    ((m1b_formDualEquiv C hC).symm (m1b_formDualEquiv B hB x)) y = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end HodgeLean.Foundations.Program
