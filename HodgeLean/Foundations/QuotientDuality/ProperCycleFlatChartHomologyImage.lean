import HodgeLean.Foundations.QuotientDuality.ProperCycleCenteredChartPointValue
import HodgeLean.Foundations.QuotientDuality.ProperCycleFlatSupportPointPair
import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenPointExcisionMap
import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodCapNaturality

/-! # Actual component homology images in original flattened support coordinates
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual homology image whose original intrinsic chart class uses the literal tangential coordinates has the standard complex point value in the original flattened support chart.
Source: properCycle_centered_chart_point_value; properCycle_relative_homology_projection_naturality; properCycle_open_local_homology_iso_map.
HC no distance; AV milestone no distance. -/
lemma properCycle_flat_chart_homology_image
    (X Z : TopCat.{0}) [T1Space Z] (S : Set X) [T1Space (TopCat.of S)] (r : ℕ)
    (Y : TopCat.{0}) (e : OpenPartialHomeomorph X ((Fin r → ℂ) × Y)) (y0 : Y)
    (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y0)
    (f : Z ⟶ TopCat.of S) (hf : Function.Injective f)
    (c : OpenPartialHomeomorph Z (Fin r → ℂ))
    (hsub : ∀ u ∈ c.source, (f u).val ∈ e.source)
    (hval : ∀ u ∈ c.source, c u = (e (f u).val).1)
    (y : Z) (hy : y ∈ c.source) (hcenter : e (f y).val = (0, y0))
    (μ : Homology ℚ Z (2*r)) (hμ : localOrientation Z (2*r) μ y = localClassOfChart r c y hy) :
    let V : Opens (TopCat.of S) := ⟨{s : S | s.val ∈ e.source},
      e.open_source.preimage continuous_subtype_val⟩
    relativeHomologyMap ℚ (2*r)
      (properCycle_flat_support_point_pair X S e y0 hflat (f y) (hsub y hy) (congrArg Prod.fst hcenter))
      ((properCycle_open_local_homology_iso (TopCat.of S) V ⟨f y, hsub y hy⟩ (2*r)).inv.hom
        (localOrientation (TopCat.of S) (2*r) (homologyMap ℚ (2*r) f μ) (f y))) =
      standardComplexLocalClass ℚ r := by
  dsimp only
  let W : Opens Z := ⟨c.source, c.open_source⟩
  let V : Opens (TopCat.of S) := ⟨{s : S | s.val ∈ e.source},
    e.open_source.preimage continuous_subtype_val⟩
  let jZ : TopCat.of W ⟶ Z := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let jS : TopCat.of V ⟶ TopCat.of S := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let F : TopCat.of W ⟶ TopCat.of V :=
    TopCat.ofHom ⟨fun u => ⟨f u.val, hsub u.val u.property⟩,
      (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let pF := TopPair.ofSubsetHom F
    (show Set.MapsTo F ({⟨y, hy⟩} : Set W)ᶜ ({⟨f y, hsub y hy⟩} : Set V)ᶜ from by
      intro u hu he
      apply hu
      apply Subtype.ext
      exact hf (congrArg (fun v : V => v.val) he))
  let pZ := imagePointPairMap jZ Subtype.val_injective (⟨y, hy⟩ : W)
  let pS := imagePointPairMap jS Subtype.val_injective (⟨f y, hsub y hy⟩ : V)
  let p := imagePointPairMap f hf y
  let oZ := properCycle_open_local_homology_iso Z W ⟨y, hy⟩ (2*r)
  let oS := properCycle_open_local_homology_iso (TopCat.of S) V ⟨f y, hsub y hy⟩ (2*r)
  let v := oZ.inv.hom (localOrientation Z (2*r) μ y)
  have hp : pF ≫ pS = pZ ≫ p := by ext u : 2 <;> rfl
  have hm := congrArg (fun g => relativeHomologyMap ℚ (2*r) g v) hp
  simp only [relativeHomologyMap_comp, LinearMap.comp_apply] at hm
  have hz := LinearMap.congr_fun (properCycle_open_local_homology_iso_map Z W ⟨y, hy⟩ (2*r)) v
  have hs := properCycle_open_local_homology_iso_map (TopCat.of S) V ⟨f y, hsub y hy⟩ (2*r)
  have hn := properCycle_relative_homology_projection_naturality p (2*r) μ
  change relativeHomologyMap ℚ (2*r) p (localOrientation Z (2*r) μ y) =
    localOrientation (TopCat.of S) (2*r) (homologyMap ℚ (2*r) f μ) (f y) at hn
  have hv : relativeHomologyMap ℚ (2*r) pZ v = localOrientation Z (2*r) μ y :=
    hz.symm.trans (oZ.inv_hom_id_apply _)
  have hpoint : oS.inv.hom
      (localOrientation (TopCat.of S) (2*r) (homologyMap ℚ (2*r) f μ) (f y)) =
      relativeHomologyMap ℚ (2*r) pF v := by
    apply oS.toLinearEquiv.injective
    change oS.hom.hom (oS.inv.hom _) = oS.hom.hom _
    rw [oS.inv_hom_id_apply, hs]
    exact (hm.trans ((congrArg (relativeHomologyMap ℚ (2*r) p) hv).trans hn)).symm
  let g := properCycle_flat_support_point_pair X S e y0 hflat (f y) (hsub y hy)
    (congrArg Prod.fst hcenter)
  have hc : c y = 0 := (hval y hy).trans (congrArg Prod.fst hcenter)
  let C : TopCat.of W ⟶ TopCat.of (Fin r → ℂ) :=
    TopCat.ofHom ⟨fun u => c u.val, (c.continuousOn.mono (show (W : Set Z) ⊆ c.source from Set.Subset.rfl)).domRestrict⟩
  let pC := TopPair.ofSubsetHom C
    (show Set.MapsTo C ({⟨y, hy⟩} : Set W)ᶜ ({0} : Set (Fin r → ℂ))ᶜ from
      fun u hu he => hu (Subtype.ext (c.injOn u.property hy (he.trans hc.symm))))
  have hpc : pF ≫ g = pC := by
    ext u : 2
    · apply Subtype.ext
      exact (hval u.val.val u.val.property).symm
    · exact (hval u.val u.property).symm
  have hmc := congrArg (fun a => relativeHomologyMap ℚ (2*r) a v) hpc
  simp only [relativeHomologyMap_comp, LinearMap.comp_apply] at hmc
  rw [hpoint]
  change relativeHomologyMap ℚ (2*r) g (relativeHomologyMap ℚ (2*r) pF v) = _
  apply hmc.trans
  dsimp only [v]
  rw [hμ]
  exact properCycle_centered_chart_point_value Z r c y hy hc

end HodgeLean.Foundations.QuotientDuality
