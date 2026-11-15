import HodgeLean.Foundations.Program.SchoenCyclePushDefs
import HodgeLean.Adapters.CyclePushforwardProduct

/-! Component generic points in the support of rational orbit cycles. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

theorem s4_orbit_support {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) (d : W ⟶ W) (m : ℕ) (a : Fin m → ℚ)
    {x : W.left} (hx : x ∈ (s2e_rationalOrbitCycle ι d m a).support) :
    ∃ t : Fin m, (ι ≫ (End.of d ^ t.val).asHom).left (genericPoint Q.left) = x := by
  classical
  by_contra hn
  push_neg at hn
  apply hx
  change (s2e_rationalOrbitCycle ι d m a) x = 0
  simp only [s2e_rationalOrbitCycle, Function.locallyFinsuppWithin.coe_sum,
    Finset.sum_apply, Function.locallyFinsuppWithin.mapRange_apply,
    s2e_componentCycle, Function.locallyFinsuppWithin.single_apply]
  exact Finset.sum_eq_zero fun t _ => by rw [if_neg (hn t).symm]; exact mul_zero _

theorem s4_pushed_orbit_support {Q W V : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) (d : W ⟶ W) (m : ℕ) (a : Fin m → ℚ)
    (φ : W ⟶ V) [QuasiCompact φ.left] {x : V.left}
    (hx : x ∈ (a1p_pushforward φ.left (s2e_rationalOrbitCycle ι d m a)).support) :
    ∃ t : Fin m,
      φ.left ((ι ≫ (End.of d ^ t.val).asHom).left (genericPoint Q.left)) = x := by
  classical
  let s : Finset W.left := Finset.univ.image
    (fun t : Fin m => (ι ≫ (End.of d ^ t.val).asHom).left (genericPoint Q.left))
  have hs : (s2e_rationalOrbitCycle ι d m a).support ⊆ s := by
    intro y hy
    obtain ⟨t, rfl⟩ := s4_orbit_support ι d m a hy
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
  have hi := a1x_pushforward_support φ.left (s2e_rationalOrbitCycle ι d m a) s hs hx
  obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hi
  obtain ⟨t, _, hty⟩ := Finset.mem_image.mp hy
  exact ⟨t, (congrArg φ.left hty).trans hyx⟩

end HodgeLean.Foundations.Program
