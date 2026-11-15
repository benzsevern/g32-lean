import HodgeLean.Foundations.BundleResolution.ModulePullbackIsoHelpers
import HodgeLean.Foundations.BundleResolution.ModuleUnitPullbackHelpers

/-! # Descent of actual module sections along scheme isomorphisms

The canonical unit comparison and the actual pullback equivalence transport every section.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution

theorem moduleSectionPullback_iso_bijective {X Y : Scheme.{0}}
    (e : X ≅ Y) (M : Y.Modules) :
    Function.Bijective (i1_module_sectionPullback e.hom M) := by
  letI := i1_modulePullback_iso_isEquivalence e
  let F := Scheme.Modules.pullback e.hom
  let u := i1_module_unitPullbackIso e.hom
  constructor
  · intro s t h
    apply F.map_injective
    apply (cancel_epi u.inv).mp
    exact h
  · intro t
    let s := F.preimage (u.hom ≫ t)
    refine ⟨s, ?_⟩
    change u.inv ≫ F.map s = t
    rw [F.map_preimage, Iso.inv_hom_id_assoc]

theorem moduleSection_iso_transport_exists {X Y : Scheme.{0}}
    (e : X ≅ Y) (M : Y.Modules) (N : X.Modules)
    (a : (Scheme.Modules.pullback e.hom).obj M ≅ N)
    (t : SheafOfModules.unit.{0} X.ringCatSheaf ⟶ N) :
    ∃ s : SheafOfModules.unit.{0} Y.ringCatSheaf ⟶ M,
      i1_module_sectionPullback e.hom M s ≫ a.hom = t := by
  obtain ⟨s, hs⟩ := (moduleSectionPullback_iso_bijective e M).2 (t ≫ a.inv)
  refine ⟨s, ?_⟩
  rw [hs, Category.assoc, Iso.inv_hom_id, Category.comp_id]

#print axioms moduleSection_iso_transport_exists

#print axioms moduleSectionPullback_iso_bijective

end HodgeLean.Foundations.TubularEuler
