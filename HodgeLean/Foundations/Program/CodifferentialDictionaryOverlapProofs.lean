import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
open Filter Topology
namespace HodgeLean.Foundations.Program

theorem b66d_lift_overlap
    (F G T : ((Fin 10 → ℂ) × ℂ) → ℂ)
    (F' G' T' : ((Fin 10 → ℂ) × ℂ) →L[ℂ] ℂ)
    (u : (Fin 10 → ℂ) × ℂ) (h : Fin 10 → ℂ)
    (hF : HasFDerivAt F F' u) (hG : HasFDerivAt G G' (u.1, T u))
    (hT : HasFDerivAt T T' u)
    (hsource : F =ᶠ[𝓝 u] fun q => G (q.1, T q))
    (hFz : F' (0, 1) ≠ 0) (hGz : G' (0, 1) ≠ 0) :
    T' (h, 0) = T' (0, 1) * (F' (h, 0) / F' (0, 1)) -
      G' (h, 0) / G' (0, 1) := by
  have hc := hG.comp u ((hasFDerivAt_fst (p := u)).prodMk hT)
  have hd := hF.unique (hc.congr_of_eventuallyEq hsource)
  have hsplit (v : Fin 10 → ℂ) (z : ℂ) :
      G' (v, z) = G' (v, 0) + z * G' (0, 1) := by
    rw [show (v, z) = (v, 0) + z • (0, 1) by simp,
      map_add, map_smul, smul_eq_mul]
  have hp : F' (h, 0) = G' (h, 0) + T' (h, 0) * G' (0, 1) := by
    rw [hd]
    exact hsplit _ _
  have hv : F' (0, 1) = T' (0, 1) * G' (0, 1) := by
    rw [hd]
    change G' (0, T' (0, 1)) = _
    rw [hsplit, show G' (0, 0) = 0 from map_zero G', zero_add]
  field_simp [hFz, hGz]
  rw [hp, hv]
  ring

end HodgeLean.Foundations.Program
