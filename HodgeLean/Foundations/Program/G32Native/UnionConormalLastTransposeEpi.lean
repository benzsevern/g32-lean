import HodgeLean.Foundations.Program.G32Native.UnionConormalSupComparisonEpi
import HodgeLean.Foundations.Program.G32Native.UnionConormalMaps

/-! # Epimorphy of the actual last arrow after transposition -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual last union conormal arrow has epic transpose under the
supplied scheme-theoretic intersection equation. -/
lemma unionConormalLast_transpose_epi
    {V T₁ T₂ S : Scheme.{0}}
    (t₁ : T₁ ⟶ V) (t₂ : T₂ ⟶ V) (s₁ : S ⟶ T₁) (s₂ : S ⟶ T₂)
    [IsClosedImmersion t₁] [IsClosedImmersion t₂] [IsClosedImmersion s₂]
    (hs : s₁ ≫ t₁ = s₂ ≫ t₂)
    (hinter : (s₁ ≫ t₁).ker = t₁.ker ⊔ t₂.ker) :
    Epi (((Scheme.Modules.pullbackPushforwardAdjunction s₁).homEquiv _ _).symm
      (unionConormalLast t₁ t₂ s₁ s₂ hs)) := by
  rw [unionConormalLast_transpose]
  exact unionConormal_comparison_epi_of_sup t₁ s₂ t₂ s₁ hs (by rw [← hs]; exact hinter)

end HodgeLean.Foundations.Program.G32Native
