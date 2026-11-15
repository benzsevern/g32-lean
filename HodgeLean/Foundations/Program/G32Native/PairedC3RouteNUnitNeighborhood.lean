import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNNormalizedEquation

/-! # Normalization by an ambient unit on a neighborhood of the slice -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A coefficient invertible on the slice becomes an ambient unit after
shrinking the affine open, while retaining its entire inverse image on the slice.
Source: Hartshorne, Algebraic Geometry, II.2 and II.3, principal opens. -/
theorem paired_c3_normalizing_unit_neighborhood
    {Q X : Scheme} (i : Q ⟶ X) (U : X.affineOpens) (a : Γ(X, U))
    (ha : IsUnit ((i.app U.1).hom a)) :
    ∃ (V : X.affineOpens) (hVU : V ≤ U),
      IsUnit ((X.presheaf.map (homOfLE (X := X.Opens) hVU).op).hom a) ∧
        i ⁻¹ᵁ V.1 = i ⁻¹ᵁ U.1 := by
  refine ⟨X.affineBasicOpen a, X.affineBasicOpen_le a, ?_, ?_⟩
  · exact X.toRingedSpace.isUnit_res_basicOpen a
  · change i ⁻¹ᵁ X.basicOpen a = i ⁻¹ᵁ U.1
    rw [Scheme.preimage_basicOpen, Scheme.basicOpen_of_isUnit _ ha]

end HodgeLean.Foundations.Program.G32Native
