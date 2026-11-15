import HodgeLean.Foundations.Program.G32Native.AbelCollisionFirstVariation
import HodgeLean.Foundations.Program.G32Native.AbelCollisionRoots
import Mathlib.Analysis.Calculus.Deriv.Pi

/-! # Directional derivatives in monic coefficient coordinates -/
noncomputable section
set_option maxHeartbeats 400000
open Filter
open scoped BigOperators Topology
namespace HodgeLean.Foundations.Program.G32Native

/-- The scalar collision formula computes the actual derivative on a coefficient basis vector. -/
theorem monic_coordinate_first_variation {m n : ℕ} (hn : 0 < n)
    (j : Fin m) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    (f : (Fin m → ℂ) → ℂ) (H : ℂ → ℂ)
    (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hf : DifferentiableAt ℂ f 0) (hH : HasFPowerSeriesAt H p 0)
    (c : ℂ) (he : ∀ᶠ t in 𝓝 (0 : ℂ),
      f (Pi.single j (-(t ^ n))) = (∑ i : Fin n, H (ζ ^ i.val * t)) + c) :
    fderiv ℂ f 0 (Pi.single j 1) = -(n : ℂ) * p.coeff n := by
  classical
  let G : ℂ → ℂ := fun z => f (Pi.single j z)
  have hd : HasDerivAt G (fderiv ℂ f 0 (Pi.single j 1)) 0 := by
    have hdf : HasFDerivAt f (fderiv ℂ f 0) (Pi.single j (0 : ℂ)) := by
      simpa only [Pi.single_zero] using hf.hasFDerivAt
    exact hdf.comp_hasDerivAt 0 (hasDerivAt_single j 0)
  have hm : ∀ k, 0 < k → k < n → ∑ i : Fin n, (ζ ^ i.val) ^ k = 0 :=
    fun _ hk hkn => collision_root_lower_moment hζ hk hkn
  exact hd.deriv.symm.trans (monic_root_path_first_variation hn (fun i : Fin n => ζ ^ i.val)
    (collision_root_top_moment hζ) hm G H p hd.differentiableAt hH c he)

#print axioms monic_coordinate_first_variation
end HodgeLean.Foundations.Program.G32Native
