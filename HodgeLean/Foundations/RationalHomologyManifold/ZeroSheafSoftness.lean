import HodgeLean.Foundations.RationalHomologyManifold.SoftSheafTransport

/-! Softness of actual zero sheaf terms in bounded truncations.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- A zero sheaf of abelian groups satisfies the existing softness condition.
Source: Bredon, Sheaf Theory, second edition, II.9; extension of the unique zero section.
HC no distance; AV milestone no distance.
-/
theorem isSoft_of_isZero_sheaf {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (hF : IsZero F) : IsSoft F := by
  intro K U hK hKU s
  have hs0 : s = 0 := by
    have h := ConcreteCategory.congr_hom
      (congrArg (fun φ => φ.hom.app (Opposite.op U))
        (hF.eq_of_src (𝟙 F) (0 : F ⟶ F))) s
    change s = 0 at h
    exact h
  refine ⟨U, le_rfl, hKU, 0, ?_⟩
  simp only [hs0, map_zero]

#print axioms isSoft_of_isZero_sheaf
end HodgeLean.Foundations.RationalHomologyManifold
