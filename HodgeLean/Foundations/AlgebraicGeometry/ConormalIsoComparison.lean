import HodgeLean.Foundations.AlgebraicGeometry.ConormalComparisonMap
import HodgeLean.Foundations.AlgebraicGeometry.ConormalComparisonComposition

/-! # Isomorphism transport for the natural ideal comparison
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.Program

namespace AlgebraicGeometry.Conormal

/-- The natural ideal map before scalar extension is invertible along scheme isomorphisms. -/
lemma idealPushforwardMap_isIso_of_isIso
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (f : W' ⟶ W) (g : Q' ⟶ Q) [IsIso f] [IsIso g]
    (h : g ≫ i = i' ≫ f) : IsIso (idealPushforwardMap i i' f g h) := by
  have : IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) :=
    s2e_structureModule_map_isIso f
  have : IsIso (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) :=
    s2e_structureModule_map_isIso g
  unfold idealPushforwardMap
  dsimp only
  infer_instance

/-- The natural scalar-extended ideal map is invertible along scheme isomorphisms. -/
lemma idealPullbackMap_isIso_of_isIso
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (f : W' ⟶ W) (g : Q' ⟶ Q) [IsIso f] [IsIso g]
    (h : g ≫ i = i' ≫ f) : IsIso (idealPullbackMap i i' f g h) := by
  have : IsIso (idealPushforwardMap i i' f g h) := idealPushforwardMap_isIso_of_isIso i i' f g h
  unfold idealPullbackMap
  rw [Adjunction.homEquiv_counit]
  infer_instance

/-- The natural ideal comparison depends only on the ambient map of a commuting square. -/
lemma idealPullbackMap_eq_of_ambient
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (f : W' ⟶ W) (g g' : Q' ⟶ Q)
    (h : g ≫ i = i' ≫ f) (h' : g' ≫ i = i' ≫ f) :
    idealPullbackMap i i' f g h = idealPullbackMap i i' f g' h' := by
  apply (cancel_mono (kernel.ι (SheafOfModules.unitToPushforwardObjUnit i'.toRingCatSheafHom))).mp
  rw [idealPullbackMap_inclusion, idealPullbackMap_inclusion]

/-- Equality of ambient maps preserves invertibility of the natural ideal comparisons. -/
lemma idealPullbackMap_isIso_congr
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (f f' : W' ⟶ W) (hf : f = f') (g g' : Q' ⟶ Q)
    (h : g ≫ i = i' ≫ f) (h' : g' ≫ i = i' ≫ f') :
    IsIso (idealPullbackMap i i' f g h) ↔ IsIso (idealPullbackMap i i' f' g' h') := by
  subst f'
  rw [idealPullbackMap_eq_of_ambient i i' f g g' h h']

end AlgebraicGeometry.Conormal
