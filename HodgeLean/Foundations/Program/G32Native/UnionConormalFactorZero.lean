import HodgeLean.Foundations.AlgebraicGeometry.ConormalComparisonMap

/-! # Vanishing of ideal comparison along a factorization -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program AlgebraicGeometry.Conormal

/-- An ideal comparison vanishes when the ambient map factors through its zero scheme. -/
lemma unionConormal_idealPushforwardMap_factor_zero
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (b : W' ⟶ Q) (g : Q' ⟶ Q) (h : g ≫ i = i' ≫ (b ≫ i)) :
    idealPushforwardMap i i' (b ≫ i) g h = 0 := by
  apply (cancel_mono ((Scheme.Modules.pushforward (b ≫ i)).map
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit i'.toRingCatSheafHom)))).mp
  rw [idealPushforwardMap_inclusion, zero_comp, ← s2e_structureModule_map_comp b i]
  simp only [← Category.assoc, kernel.condition, zero_comp]

/-- Scalar extension preserves the vanishing along an ambient factorization. -/
lemma unionConormal_idealPullbackMap_factor_zero
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (b : W' ⟶ Q) (g : Q' ⟶ Q) (h : g ≫ i = i' ≫ (b ≫ i)) :
    idealPullbackMap i i' (b ≫ i) g h = 0 := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (b ≫ i)).homEquiv _ _).injective
  rw [idealPullbackMap, Equiv.apply_symm_apply,
    unionConormal_idealPushforwardMap_factor_zero]
  simp only [Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]

/-- The conormal comparison vanishes along an ambient factorization. -/
lemma unionConormal_comparisonMap_factor_zero
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (b : W' ⟶ Q) (g : Q' ⟶ Q) (h : g ≫ i = i' ≫ (b ≫ i)) :
    comparisonMap i i' (b ≫ i) g h = 0 := by
  unfold comparisonMap
  rw [unionConormal_idealPullbackMap_factor_zero, Functor.map_zero]
  simp only [comp_zero]

/-- The ideal vanishing criterion also applies to an equal ambient map. -/
lemma unionConormal_idealPullbackMap_factor_zero_of_eq
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (f : W' ⟶ W) (g : Q' ⟶ Q) (h : g ≫ i = i' ≫ f)
    (b : W' ⟶ Q) (hf : f = b ≫ i) :
    idealPullbackMap i i' f g h = 0 := by
  subst f
  exact unionConormal_idealPullbackMap_factor_zero i i' b g h

end HodgeLean.Foundations.Program.G32Native
