import HodgeLean.Foundations.AlgebraicGeometry.ConormalComparisonMap

/-! # The natural maps of the union/intersection conormal sequence -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Restriction of the ambient conormal along a factorization of immersions. -/
def unionConormalFirst
    {V T T₁ : Scheme.{0}} (t : T ⟶ V) (t₁ : T₁ ⟶ V)
    (a : T₁ ⟶ T) (ha : a ≫ t = t₁) :
    (Scheme.Modules.pullback a).obj (s2c_conormal t) ⟶ s2c_conormal t₁ :=
  Conormal.comparisonMap t t₁ (𝟙 V) a (ha.trans (Category.comp_id t₁).symm)

/-- The intersection conormal map, transposed along the first component. -/
def unionConormalLast
    {V T₁ T₂ S : Scheme.{0}} (t₁ : T₁ ⟶ V) (t₂ : T₂ ⟶ V)
    (s₁ : S ⟶ T₁) (s₂ : S ⟶ T₂) (hs : s₁ ≫ t₁ = s₂ ≫ t₂) :
    s2c_conormal t₁ ⟶ (Scheme.Modules.pushforward s₁).obj (s2c_conormal s₂) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction s₁).homEquiv _ _)
    (Conormal.comparisonMap t₁ s₂ t₂ s₁ hs)

/-- Transposing the last map recovers the commuting-square comparison. -/
lemma unionConormalLast_transpose
    {V T₁ T₂ S : Scheme.{0}} (t₁ : T₁ ⟶ V) (t₂ : T₂ ⟶ V)
    (s₁ : S ⟶ T₁) (s₂ : S ⟶ T₂) (hs : s₁ ≫ t₁ = s₂ ≫ t₂) :
    ((Scheme.Modules.pullbackPushforwardAdjunction s₁).homEquiv _ _).symm
      (unionConormalLast t₁ t₂ s₁ s₂ hs) =
      Conormal.comparisonMap t₁ s₂ t₂ s₁ hs :=
  Equiv.symm_apply_apply _ _

end HodgeLean.Foundations.Program.G32Native
