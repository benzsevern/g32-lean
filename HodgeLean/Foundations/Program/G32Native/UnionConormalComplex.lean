import HodgeLean.Foundations.Program.G32Native.UnionConormalComparisonZero
import HodgeLean.Foundations.Program.G32Native.UnionConormalMaps
import HodgeLean.Foundations.Program.G32Native.UnionConormalUnionFactor
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # The natural global union conormal complex -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- The natural first and last maps compose to zero for a supplied closed union. -/
lemma unionConormal_comp_eq_zero
    {V T T₁ T₂ S : Scheme.{0}}
    (t : T ⟶ V) (t₁ : T₁ ⟶ V) (t₂ : T₂ ⟶ V)
    [IsClosedImmersion t]
    (a : T₁ ⟶ T) (s₁ : S ⟶ T₁) (s₂ : S ⟶ T₂)
    (ha : a ≫ t = t₁) (hs : s₁ ≫ t₁ = s₂ ≫ t₂)
    (hunion : t.ker = t₁.ker ⊓ t₂.ker) :
    unionConormalFirst t t₁ a ha ≫ unionConormalLast t₁ t₂ s₁ s₂ hs = 0 := by
  obtain ⟨b, hb⟩ := unionConormal_second_factor t t₁ t₂ hunion
  have hz := unionConormal_comparisonMap_comp_zero t t₁ s₂ (𝟙 V) t₂ a s₁
    (ha.trans (Category.comp_id t₁).symm) hs b
    ((Category.comp_id t₂).trans hb.symm)
  apply ((Scheme.Modules.pullbackPushforwardAdjunction s₁).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, unionConormalLast_transpose]
  change (Scheme.Modules.pullback s₁).map
      (comparisonMap t t₁ (𝟙 V) a (ha.trans (Category.comp_id t₁).symm)) ≫
    comparisonMap t₁ s₂ t₂ s₁ hs = _
  rw [hz]
  simp only [Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]

/-- The global short complex formed by the natural union conormal maps. -/
def unionConormalComplex
    {V T T₁ T₂ S : Scheme.{0}}
    (t : T ⟶ V) (t₁ : T₁ ⟶ V) (t₂ : T₂ ⟶ V)
    [IsClosedImmersion t]
    (a : T₁ ⟶ T) (s₁ : S ⟶ T₁) (s₂ : S ⟶ T₂)
    (ha : a ≫ t = t₁) (hs : s₁ ≫ t₁ = s₂ ≫ t₂)
    (hunion : t.ker = t₁.ker ⊓ t₂.ker) : ShortComplex T₁.Modules :=
  ShortComplex.mk (unionConormalFirst t t₁ a ha)
    (unionConormalLast t₁ t₂ s₁ s₂ hs)
    (unionConormal_comp_eq_zero t t₁ t₂ a s₁ s₂ ha hs hunion)

end HodgeLean.Foundations.Program.G32Native
