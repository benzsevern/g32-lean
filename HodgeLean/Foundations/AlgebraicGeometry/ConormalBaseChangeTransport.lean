import HodgeLean.Foundations.AlgebraicGeometry.ConormalComparisonMap

/-! # Transport from ideal modules to conormal modules
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Conormal

/-- Transport an ideal-module isomorphism along a commuting square. -/
def sheafIsoOfIdealIso
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (f : W' ⟶ W) (g : Q' ⟶ Q) (h : g ≫ i = i' ≫ f)
    (e : (Scheme.Modules.pullback f).obj (idealModule i) ≅ idealModule i') :
    (Scheme.Modules.pullback g).obj (sheaf i) ≅ sheaf i' :=
  (Scheme.Modules.pullbackComp g i).app (idealModule i) ≪≫
    (Scheme.Modules.pullbackCongr h).app (idealModule i) ≪≫
    (Scheme.Modules.pullbackComp i' f).symm.app (idealModule i) ≪≫
    (Scheme.Modules.pullback i').mapIso e

/-- The conormal comparison is invertible whenever the ideal comparison is. -/
lemma comparisonMap_isIso_of_idealPullbackMap_isIso
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (f : W' ⟶ W) (g : Q' ⟶ Q) (h : g ≫ i = i' ≫ f)
    [IsIso (idealPullbackMap i i' f g h)] :
    IsIso (comparisonMap i i' f g h) := by
  unfold comparisonMap
  haveI : IsIso ((Scheme.Modules.pullback i').map (idealPullbackMap i i' f g h)) :=
    Functor.map_isIso _ _
  infer_instance

end AlgebraicGeometry.Conormal
