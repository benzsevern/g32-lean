import HodgeLean.Foundations.Program.G32Native.UnionConormalConormalUnitEpi
import HodgeLean.Foundations.Program.G32Native.UnionConormalLastTransposeEpi
import HodgeLean.Foundations.Program.G32Native.UnionConormalClosedTransposeEpi

/-! # Epimorphy of the actual global last union conormal arrow -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The supplied intersection equation makes the actual global last arrow epic. -/
lemma unionConormalLast_epi
    {V T₁ T₂ S : Scheme.{0}}
    (t₁ : T₁ ⟶ V) (t₂ : T₂ ⟶ V) (s₁ : S ⟶ T₁) (s₂ : S ⟶ T₂)
    [IsClosedImmersion t₁] [IsClosedImmersion t₂]
    [IsClosedImmersion s₁] [IsClosedImmersion s₂]
    (hs : s₁ ≫ t₁ = s₂ ≫ t₂)
    (hinter : (s₁ ≫ t₁).ker = t₁.ker ⊔ t₂.ker) :
    Epi (unionConormalLast t₁ t₂ s₁ s₂ hs) := by
  haveI := unionConormal_conormalUnit_epi t₁ s₁
  haveI : Epi (AlgebraicGeometry.Conormal.comparisonMap t₁ s₂ t₂ s₁ hs) := by
    simpa only [unionConormalLast_transpose] using
      (unionConormalLast_transpose_epi t₁ t₂ s₁ s₂ hs hinter)
  exact unionConormal_closedTranspose_epi_of_unit s₁ (s2c_conormal t₁)
    (s2c_conormal s₂) (AlgebraicGeometry.Conormal.comparisonMap t₁ s₂ t₂ s₁ hs)

end HodgeLean.Foundations.Program.G32Native
