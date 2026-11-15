import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNSplittingMaps

/-! # Moving one specified negative summand to the first position -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Move the specified negative summand to the first position, retaining
all other summands in their recursive order. -/
def pairedC3NegativeSummandIso (k a : ℕ) :
    (b : ℕ) → Fin (b + 1) →
      (pairedC3SplitBundle k a (b + 1) ≅
        pairedC3NegativeLine k ⊞ pairedC3SplitBundle k a b)
  | 0, _ => biprod.braiding _ _
  | b + 1, i => Fin.lastCases (biprod.braiding _ _)
      (fun j => biprod.mapIso (pairedC3NegativeSummandIso k a b j) (Iso.refl _) ≪≫
        biprod.associator _ _ _) i

/-- The projection onto the specified negative summand. -/
def pairedC3NegativeProjection (k a b : ℕ) (i : Fin (b + 1)) :
    pairedC3SplitBundle k a (b + 1) ⟶ pairedC3NegativeLine k :=
  (pairedC3NegativeSummandIso k a b i).hom ≫ biprod.fst

/-- The last negative projection has its original recursive position. -/
theorem paired_c3_negative_projection_last (k a b : ℕ) :
    pairedC3NegativeProjection k a b (Fin.last b) = biprod.snd := by
  cases b <;> simp only [pairedC3NegativeProjection, pairedC3NegativeSummandIso,
    Fin.lastCases_last, biprod.braiding_hom, biprod.lift_fst]

end HodgeLean.Foundations.Program.G32Native
