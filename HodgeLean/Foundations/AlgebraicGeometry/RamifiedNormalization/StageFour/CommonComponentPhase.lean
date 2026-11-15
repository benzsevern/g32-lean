import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ClassifiedSphereProjection
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.BinomialPhaseNormalization
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.Defs

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A single base-coordinate dilation retains the literal specified projection phase on all actual component points and both support endpoints. -/
theorem common_component_phase
    (m α : ℕ) (F S : Over (Spec ↧ℂ)) (P : F ⟶ S)
    (vE : ComplexPoint S ≃ₜ OnePoint ℂ)
    (j : ZMod (Nat.gcd m α) → (projectiveLine ⟶ F))
    (G : ComplexPoint F ≃ ZMod (Nat.gcd m α) × OnePoint ℂ)
    (hj : ∀ l z, G (Point.map (j l) z) = (l, lineCoordinate z))
    {TA : Type} (U : Set (ComplexPoint F)) (H : TA ≃ U)
    (E : TA ≃ ZMod (Nat.gcd m α) × ℂ)
    (hG : ∀ a, G (H a).val = ((E a).1, ((E a).2 : OnePoint ℂ)))
    (κ ζ : ℂ) (hκ : κ ≠ 0) (B : ℤ)
    (hU : ∀ z, z ∈ U ↔ vE (Point.map P z) ≠ (∞ : OnePoint ℂ))
    (hv : ∀ a, vE (Point.map P (H a).val) =
      (((κ * (ζ ^ (m / Nat.gcd m α)) ^ (E a).1.val) ^ (-B) *
        (E a).2 ^ (m / Nat.gcd m α) : ℂ) : OnePoint ℂ)) :
    ∃ v : ComplexPoint S ≃ₜ OnePoint ℂ,
      (∀ l z, v (Point.map P (Point.map (j l) (lineCoordinate.symm z))) =
        projection m α (ζ ^ B) (l, z)) ∧
      (∀ z, v z = ((0 : ℂ) : OnePoint ℂ) ↔ vE z = ((0 : ℂ) : OnePoint ℂ)) ∧
      (∀ z, v z = (∞ : OnePoint ℂ) ↔ vE z = (∞ : OnePoint ℂ)) := by
  let n := m / Nat.gcd m α
  let scale := κ ^ B
  have hscale : scale ≠ 0 := zpow_ne_zero _ hκ
  let v := vE.trans (Homeomorph.onePointCongr (Homeomorph.mulLeft₀ scale hscale))
  have hpower := classified_sphere_power_projection U H E G
    (fun z => vE (Point.map P z)) (fun l => (κ * (ζ ^ n) ^ l.val) ^ (-B)) n hG hU hv
  refine ⟨v, ?_, ?_, ?_⟩
  · intro l z
    have hh := hpower (Point.map (j l) (lineCoordinate.symm z))
    rw [hj, lineCoordinate.apply_symm_apply] at hh
    change (Homeomorph.onePointCongr (Homeomorph.mulLeft₀ scale hscale))
      (vE (Point.map P (Point.map (j l) (lineCoordinate.symm z)))) = _
    rw [hh]
    cases z with
    | infty => rfl
    | coe z =>
      change ((scale * ((κ * (ζ ^ n) ^ l.val) ^ (-B) * z ^ n) : ℂ) : OnePoint ℂ) =
        (((ζ ^ B) ^ (-((n * l.val : ℕ) : ℤ)) * z ^ n : ℂ) : OnePoint ℂ)
      rw [← mul_assoc]
      exact congrArg (fun a : ℂ => ((a * z ^ n : ℂ) : OnePoint ℂ))
        (binomial_phase_normalization κ ζ hκ B n l.val)
  · intro z
    change (Homeomorph.onePointCongr (Homeomorph.mulLeft₀ scale hscale)) (vE z) =
      ((0 : ℂ) : OnePoint ℂ) ↔ vE z = ((0 : ℂ) : OnePoint ℂ)
    cases vE z with
    | infty => simp
    | coe w =>
      change ((scale * w : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ) ↔
        (w : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ)
      simp only [OnePoint.coe_injective.eq_iff, mul_eq_zero, hscale, false_or]
  · intro z
    change (Homeomorph.onePointCongr (Homeomorph.mulLeft₀ scale hscale)) (vE z) =
      (∞ : OnePoint ℂ) ↔ vE z = (∞ : OnePoint ℂ)
    cases vE z with
    | infty => rfl
    | coe w =>
      change ((scale * w : ℂ) : OnePoint ℂ) = (∞ : OnePoint ℂ) ↔ (w : OnePoint ℂ) = (∞ : OnePoint ℂ)
      simp only [OnePoint.coe_ne_infty]

end AlgebraicGeometry.RamifiedNormalization.StageFour
