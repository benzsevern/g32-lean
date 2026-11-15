import HodgeLean.Foundations.BundleThom.ProductMatrixPairHelpers

/-! # Homotopies for base-dependent complex normal maps

A jointly continuous invertible matrix interpolation acts on both spaces of the actual complement pair.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- A supplied jointly continuous interpolation of invertible matrices gives an actual homotopy of normal pair maps.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, local orientation comparison. -/
def i1_productMatrixNormalHomotopy {B : Type} [TopologicalSpace B] (k : ℕ)
    (A₀ A₁ : B → Matrix (Fin k) (Fin k) ℂ) (h₀ : Continuous A₀) (h₁ : Continuous A₁)
    (hd₀ : ∀ b, (A₀ b).det ≠ 0) (hd₁ : ∀ b, (A₁ b).det ≠ 0)
    (H : unitInterval × B → Matrix (Fin k) (Fin k) ℂ) (hH : Continuous H)
    (hdH : ∀ p, (H p).det ≠ 0) (hstart : ∀ b, H (0, b) = A₀ b)
    (hend : ∀ b, H (1, b) = A₁ b) :
    TopPair.Homotopy (i1_productMatrixNormalMap k A₀ h₀ hd₀)
      (i1_productMatrixNormalMap k A₁ h₁ hd₁) where
  fst := {
    toFun := fun p => (H (p.1, p.2.1)).mulVec p.2.2
    continuous_toFun := (hH.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).matrix_mulVec
      (continuous_snd.comp continuous_snd)
    map_zero_left := fun p => by change (H (0, p.1)).mulVec p.2 = _; rw [hstart]; rfl
    map_one_left := fun p => by change (H (1, p.1)).mulVec p.2 = _; rw [hend]; rfl }
  snd := {
    toFun := fun p => ⟨(H (p.1, p.2.1.1)).mulVec p.2.1.2, by
      intro hz
      apply p.2.2
      apply (H (p.1, p.2.1.1)).mulVec_injective_of_det_ne_zero (hdH _)
      simpa using hz⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact (hH.comp (continuous_fst.prodMk
        (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)))).matrix_mulVec
          (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))
    map_zero_left := fun p => by
      apply Subtype.ext
      change (H (0, p.1.1)).mulVec p.1.2 = _
      rw [hstart]
      rfl
    map_one_left := fun p => by
      apply Subtype.ext
      change (H (1, p.1.1)).mulVec p.1.2 = _
      rw [hend]
      rfl }
  w := rfl

end HodgeLean.Foundations.BundleThom
