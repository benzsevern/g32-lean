import HodgeLean.Foundations.Program.ComponentTransportNormalizedPathAffine
import Mathlib.Analysis.Complex.Convex

/-! # Affine sphere isotopies -/
noncomputable section
open Set Topology
namespace HodgeLean.Foundations.Program

/-- Every invertible complex affine map is joined to the identity by an affine sphere motion.
Source: Mathlib `Complex` path connected unit group; `rtc_affine_family_continuous`. -/
theorem rtc_affine_isotopy (a b : ℂ) (ha : a ≠ 0) :
    ∃ D : C(unitInterval × OnePoint ℂ, OnePoint ℂ),
      (∀ t, Function.Bijective (fun z ↦ D (t, z))) ∧
      (∀ z, D (0, z) = z) ∧
      (∀ z, D (1, z) = OnePoint.map (fun w ↦ a * w + b) z) ∧
      (∀ t, D (t, OnePoint.infty) = OnePoint.infty) := by
  let α : Path (1 : ℂˣ) (Units.mk0 a ha) := PathConnectedSpace.somePath _ _
  let A : C(unitInterval, ℂ) := ⟨fun t ↦ (α t : ℂ),
    Units.continuous_val.comp α.continuous⟩
  let B : C(unitInterval, ℂ) := ⟨fun t ↦ (t : ℝ) * b,
    (Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const⟩
  have hA (t : unitInterval) : A t ≠ 0 := Units.ne_zero (α t)
  let D : C(unitInterval × OnePoint ℂ, OnePoint ℂ) :=
    ⟨fun q ↦ OnePoint.map (fun w ↦ A q.1 * w + B q.1) q.2,
      rtc_affine_family_continuous A B hA⟩
  have hA0 : A 0 = 1 := congrArg (fun u : ℂˣ ↦ (u : ℂ)) α.source
  have hA1 : A 1 = a := congrArg (fun u : ℂˣ ↦ (u : ℂ)) α.target
  have hB0 : B 0 = 0 := by simp [B]
  have hB1 : B 1 = b := by simp [B]
  refine ⟨D, ?_, ?_, ?_, fun _ ↦ rfl⟩
  · intro t
    change Function.Bijective (OnePoint.map (fun w ↦ A t * w + B t))
    apply b65x_map_bijective
    exact ((Homeomorph.mulLeft₀ (A t) (hA t)).trans (Homeomorph.addRight (B t))).bijective
  · intro z
    change OnePoint.map (fun w ↦ A 0 * w + B 0) z = z
    rw [hA0, hB0]
    induction z using OnePoint.rec with
    | infty => rfl
    | coe z => simp only [OnePoint.map_some, one_mul, add_zero]
  · intro z
    change OnePoint.map (fun w ↦ A 1 * w + B 1) z = _
    rw [hA1, hB1]

end HodgeLean.Foundations.Program
