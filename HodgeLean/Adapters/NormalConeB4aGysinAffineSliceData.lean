import HodgeLean.Adapters.NormalConeB4aGysinAffineStalk
import HodgeLean.Adapters.NormalConeB4aGysinSliceEquiv

noncomputable section
namespace HodgeLean.Adapters
open AlgebraicGeometry

/-- Regularity and exact quotient lengths of affine section germs agree
with those of the localized affine coordinate functions. -/
theorem a3b4a_gysin_affine_slice_data
    {X : Scheme.{0}} (U : X.Opens) (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    {n : ℕ} (g : Fin n → Γ(X, U)) :
    let p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    let L := Localization.AtPrime p
    let gs := List.ofFn (fun j => X.presheaf.germ U x hx (g j))
    let gl := List.ofFn (fun j => algebraMap Γ(X, U) L (g j))
    (RingTheory.Sequence.IsRegular (X.presheaf.stalk x) gs ↔
      RingTheory.Sequence.IsRegular L gl) ∧
    Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸ Ideal.ofList gs) =
      Module.length L (L ⧸ Ideal.ofList gl) := by
  obtain ⟨e, he⟩ := a3b4a_gysin_affine_stalk_equiv U hU x hx
  let gs := List.ofFn (fun j => X.presheaf.germ U x hx (g j))
  let L := Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  have hmap : gs.map e = List.ofFn (fun j => algebraMap Γ(X, U) L (g j)) := by
    rw [List.map_ofFn]
    congr 1
    funext j
    exact he (g j)
  have hcompat : List.Forall₂ (fun (r : X.presheaf.stalk x) (s : L) =>
      ∀ y, e (r • y) = s • e y) gs (gs.map e) := by
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro r _ y
    exact e.map_mul r y
  have hregular := AddEquiv.isRegular_congr (e := e.toAddEquiv) hcompat
  have hlength := a3b4a_gysin_slice_length_ringEquiv e gs
  rw [hmap] at hregular hlength
  exact ⟨hregular, hlength⟩

end HodgeLean.Adapters
