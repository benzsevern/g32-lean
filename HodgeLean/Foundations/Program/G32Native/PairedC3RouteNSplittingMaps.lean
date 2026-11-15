import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNObjects
import HodgeLean.Foundations.Program.G32Native.PairedC3HyperplaneUnitExact

/-! # The four geometric steps of the projective modification argument -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The inclusion of the original trivial summands into the recursive bundle. -/
def pairedC3TrivialInclusion (k a : ℕ) :
    (b : ℕ) → (SheafOfModules.free (Fin a) : (pairedC3Proj k).Modules) ⟶
      pairedC3SplitBundle k a b
  | 0 => 𝟙 _
  | b + 1 => pairedC3TrivialInclusion k a b ≫ biprod.inl

/-- The original trivial summands together with a chosen lifted section. -/
def pairedC3LiftMap (k a b : ℕ) (E : ShortComplex (pairedC3Proj k).Modules)
    (e₁ : E.X₁ ≅ pairedC3SplitBundle k a (b + 1))
    (s : SheafOfModules.unit (pairedC3Proj k).ringCatSheaf ⟶ E.X₂) :=
  biprod.desc (pairedC3TrivialInclusion k a (b + 1) ≫ e₁.inv ≫ E.f) s

/-- The zero-negative-summand inclusion retains the original free object.
The check rejects a zero map in place of the inclusion. -/
theorem paired_c3_trivial_inclusion_zero (k a : ℕ) :
    pairedC3TrivialInclusion k a 0 = 𝟙 _ := rfl

/-- The lifted map retains the original trivial directions.
The check rejects an index exchange between the two summands. -/
theorem paired_c3_lift_map_inl (k a b : ℕ)
    (E : ShortComplex (pairedC3Proj k).Modules)
    (e₁ : E.X₁ ≅ pairedC3SplitBundle k a (b + 1))
    (s : SheafOfModules.unit (pairedC3Proj k).ringCatSheaf ⟶ E.X₂) :
    biprod.inl ≫ pairedC3LiftMap k a b E e₁ s =
      pairedC3TrivialInclusion k a (b + 1) ≫ e₁.inv ≫ E.f := by
  exact biprod.inl_desc _ _

/-- The lifted map retains the chosen section with its original scale.
The check rejects replacing the section with a scalar multiple. -/
theorem paired_c3_lift_map_inr (k a b : ℕ)
    (E : ShortComplex (pairedC3Proj k).Modules)
    (e₁ : E.X₁ ≅ pairedC3SplitBundle k a (b + 1))
    (s : SheafOfModules.unit (pairedC3Proj k).ringCatSheaf ⟶ E.X₂) :
    biprod.inr ≫ pairedC3LiftMap k a b E e₁ s = s := by
  exact biprod.inr_desc _ _

end HodgeLean.Foundations.Program.G32Native
