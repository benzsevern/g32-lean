import HodgeLean.Foundations.Program.RelativeFrameOperatorCutoffCore
import HodgeLean.Foundations.Program.RelativeFrameOperatorResidue

set_option maxHeartbeats 400000
noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

def rf4_poleMultiplierFun (n : ℕ) (ε u : ℂ) : ℂ := u⁻¹ * (1 - ε * u ^ (-(n : ℤ)))⁻¹

theorem rf4_poleMultiplier_differentiableAt {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r)
    {ε : ℂ} (hε : ‖ε‖ < r) {u : ℂ} (hu : u ∈ rf4_closedAnnulus n r) :
    DifferentiableAt ℂ (rf4_poleMultiplierFun n ε) u := by
  have hu0 := rf4_closedAnnulus_ne_zero hn hr hu
  have hA := Complex.slitPlane_ne_zero (rf4_slit hn hr hε hu)
  exact ((differentiableAt_id (𝕜 := ℂ)).inv hu0).mul
    (((differentiableAt_const _).sub ((differentiableAt_const _).mul
      (differentiableAt_zpow.mpr (Or.inl hu0)))).inv hA)

def rf4_poleMultiplier (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) (ε : ℂ)
    (hε : ‖ε‖ < r) : b63r_bddHol (b63r_annulus n r) :=
  rf4_bddOn (rf4_closedAnnulus_isCompact hn r) (rf4_annulus_subset_closed n r)
    (rf4_poleMultiplierFun n ε)
    (fun _ hu ↦ (rf4_poleMultiplier_differentiableAt hn hr hε hu).continuousAt.continuousWithinAt)
    (fun _ hu ↦ (rf4_poleMultiplier_differentiableAt hn hr hε
      (rf4_annulus_subset_closed n r hu)).differentiableWithinAt)

theorem rf4_poleMultiplier_pullback (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r)
    (ε : ℂ) (hε : ‖ε‖ < r) (u : b63r_annulus n r) :
    (rf4_rootMap n ε u)⁻¹ * deriv (rf4_rootMap n ε) u = rf4_poleMultiplierFun n ε u := by
  have hu0 := rf4_closedAnnulus_ne_zero hn hr (rf4_annulus_subset_closed n r u.property)
  have hA := Complex.slitPlane_ne_zero (rf4_slit hn hr hε
    (rf4_annulus_subset_closed n r u.property))
  have hpow : (1 - ε * (u : ℂ) ^ (-(n : ℤ))) ^ (n : ℂ)⁻¹ ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hA)
  rw [(rf4_sector_pullback n hn r hr 0 ε hε u u.property (fun _ _ ↦ 0)).2.1.deriv]
  rw [rf4_rootMap, Complex.cpow_sub _ _ hA, Complex.cpow_one]
  unfold rf4_poleMultiplierFun
  field_simp
  exact div_self (by simpa only [one_div] using hpow)

end HodgeLean.Foundations.Program
