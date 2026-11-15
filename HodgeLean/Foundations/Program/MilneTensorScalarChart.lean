import HodgeLean.Foundations.Program.MilneTensorSplitPolynomial

noncomputable section
namespace HodgeLean.Foundations.Program
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

def m1b_scalarShearEquiv (b : W →ₗ[ℂ] ℂ) : (ℂ × W) ≃ₗ[ℂ] (ℂ × W) where
  toFun v := (v.1 + b v.2, v.2)
  invFun v := (v.1 - b v.2, v.2)
  map_add' := by
    rintro ⟨x, u⟩ ⟨y, v⟩
    simp only [Prod.mk_add_mk, map_add]
    congr 1; ring
  map_smul' := by
    rintro c ⟨x, y⟩
    simp only [Prod.smul_mk, map_smul, smul_add, RingHom.id_apply]
  left_inv x := by simp only [add_sub_cancel_right, Prod.mk.eta]
  right_inv x := by simp only [sub_add_cancel, Prod.mk.eta]

def m1b_scalarChartEquiv (t : ℂˣ) (b : W →ₗ[ℂ] ℂ) (e : W ≃ₗ[ℂ] W) :
    (ℂ × W) ≃ₗ[ℂ] (ℂ × W) :=
  (m1b_scalarShearEquiv b).trans ((LinearEquiv.smulOfUnit t).prodCongr e.symm)

theorem m1b_scalar_chart_pairing (B : LinearMap.BilinForm ℂ W)
    (t : ℂˣ) (b : W →ₗ[ℂ] ℂ) (e : W ≃ₗ[ℂ] W) (x y : ℂ × W) :
    m1b_prodBilin (LinearMap.mul ℂ ℂ) B
      (m1b_scalarChartEquiv t b e x) (m1b_scalarChartEquiv t b e y) =
      t.val ^ 2 * x.1 * y.1 + t.val ^ 2 * x.1 * b y.2 +
        t.val ^ 2 * y.1 * b x.2 + t.val ^ 2 * b x.2 * b y.2 +
          m1b_formTransport B e x.2 y.2 := by
  change (t.val * (x.1 + b x.2)) * (t.val * (y.1 + b y.2)) +
    B (e.symm x.2) (e.symm y.2) = _
  change _ = t.val ^ 2 * x.1 * y.1 + t.val ^ 2 * x.1 * b y.2 +
    t.val ^ 2 * y.1 * b x.2 + t.val ^ 2 * b x.2 * b y.2 +
      B (e.symm x.2) (e.symm y.2)
  ring

end HodgeLean.Foundations.Program
