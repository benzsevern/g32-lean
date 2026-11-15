import HodgeLean.Foundations.Program.RigidStartingSystemFibreGeometry

noncomputable section
namespace HodgeLean.Foundations.Program

def b65r_branchCentres : Fin 4 → ℂ := ![0,3,1,-2]

def b65r_branchIndices : Fin 4 → Fin 4 := ![2,2,3,3]

def b65r_branchOrders : Fin 4 → ℕ := ![2,4,3,3]

def b65r_branchMaps (i : Fin 4) (z : ℂ) : ℂ :=
  ![b65r_phi z,b65r_phi z,(b65r_phi z)⁻¹,(b65r_phi z)⁻¹] i

def b65r_branchFactors (i : Fin 4) (z : ℂ) : ℂ :=
  ![(z-3)^4/((z-1)^3*(z+2)^3),
    z^2/((z-1)^3*(z+2)^3),
    (z+2)^3/(z^2*(z-3)^4),
    (z-1)^3/(z^2*(z-3)^4)] i

theorem b65r_branch_factor (i : Fin 4) (z : ℂ) :
    b65r_branchMaps i z = (z-b65r_branchCentres i)^(b65r_branchOrders i)*
      b65r_branchFactors i z := by
  fin_cases i <;>
    norm_num [b65r_branchMaps,b65r_branchCentres,b65r_branchOrders,b65r_branchFactors,
      b65r_phi,inv_div,div_eq_mul_inv] <;> ring

theorem b65r_branch_factor_analytic (i : Fin 4) :
    AnalyticAt ℂ (b65r_branchFactors i) (b65r_branchCentres i) := by
  fin_cases i
  · exact ((analyticAt_id.sub analyticAt_const).pow 4).div
      (((analyticAt_id.sub analyticAt_const).pow 3).mul
        ((analyticAt_id.add analyticAt_const).pow 3)) (by norm_num [b65r_branchCentres])
  · exact (analyticAt_id.pow 2).div
      (((analyticAt_id.sub analyticAt_const).pow 3).mul
        ((analyticAt_id.add analyticAt_const).pow 3)) (by norm_num [b65r_branchCentres])
  · exact ((analyticAt_id.add analyticAt_const).pow 3).div
      ((analyticAt_id.pow 2).mul ((analyticAt_id.sub analyticAt_const).pow 4))
      (by norm_num [b65r_branchCentres])
  · exact ((analyticAt_id.sub analyticAt_const).pow 3).div
      ((analyticAt_id.pow 2).mul ((analyticAt_id.sub analyticAt_const).pow 4))
      (by norm_num [b65r_branchCentres])

theorem b65r_branch_factor_ne (i : Fin 4) :
    b65r_branchFactors i (b65r_branchCentres i) ≠ 0 := by
  fin_cases i <;> norm_num [b65r_branchFactors,b65r_branchCentres]

theorem b65r_branch_map_analytic (i : Fin 4) :
    AnalyticAt ℂ (b65r_branchMaps i) (b65r_branchCentres i) := by
  fin_cases i
  · exact b65r_phi_analyticAt 0 (by norm_num) (by norm_num)
  · exact b65r_phi_analyticAt 3 (by norm_num) (by norm_num)
  · exact b65r_inversePhi_analyticAt 1 (by norm_num) (by norm_num)
  · exact b65r_inversePhi_analyticAt (-2) (by norm_num) (by norm_num)

theorem b65r_branch_order_pos (i : Fin 4) : 0 < b65r_branchOrders i := by
  fin_cases i <;> norm_num [b65r_branchOrders]

end HodgeLean.Foundations.Program
