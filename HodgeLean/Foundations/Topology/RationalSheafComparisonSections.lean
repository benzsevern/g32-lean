import HodgeLean.Foundations.Topology.RationalSheafComparisonResolution

/-! Global sections and the inverse-image constant identifications.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace HodgeLean.Topology.RationalSheafComparison

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
def globalInverseImageUnit {X Y : TopCat.{0}} (f : X ⟶ Y) :
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y ⟶
      TopCat.Sheaf.pullback AddCommGrpCat.{0} f ⋙
        TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X where
  app I := ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app I).hom.app (op ⊤)
  naturality {I J} g := by
    exact congrArg (fun k => k.hom.app (op ⊤))
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.naturality g)

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem constantHomEquiv_pullback {X Y : TopCat.{0}} (f : X ⟶ Y) (A : AddCommGrpCat.{0})
    (I : TopCat.Sheaf AddCommGrpCat.{0} Y)
    (g : (TopCat.Sheaf.constantFunctor Y).obj A ⟶ I) :
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop).homEquiv _ _
      ((pullbackConstantsIso f A).inv ≫ (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map g) =
    (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat isTerminalTop).homEquiv _ _ g ≫
      (globalInverseImageUnit f).app I := by
  let ay := constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat isTerminalTop
  let ax := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f
  let ac : (TopCat.Sheaf.constantFunctor Y ⋙ TopCat.Sheaf.pullback AddCommGrpCat.{0} f) ⊣
      TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X := ay.comp adj
  have hu : ac.unit.app A ≫
      (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).map
        (pullbackConstantsIso f A).hom = ax.unit.app A :=
    ac.unit_leftAdjointUniq_hom_app ax A
  have hn : adj.homEquiv _ _ ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map g) =
      g ≫ adj.unit.app I := by
    rw [Adjunction.homEquiv_unit, Adjunction.unit_naturality]
  calc
    _ = ac.homEquiv _ _ ((pullbackConstantsIso f A).hom ≫
        (pullbackConstantsIso f A).inv ≫ (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map g) := by
      change ax.homEquiv _ _ _ = _
      simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
      rw [← hu]
      simp only [Category.assoc]
      rfl
    _ = ac.homEquiv _ _ ((TopCat.Sheaf.pullback AddCommGrpCat.{0} f).map g) := by
      rw [Iso.hom_inv_id_assoc]
    _ = _ := by
      change ay.homEquiv _ _ (adj.homEquiv _ _ _) = _
      rw [hn, Adjunction.homEquiv_naturality_right]
      rfl

end HodgeLean.Topology.RationalSheafComparison
