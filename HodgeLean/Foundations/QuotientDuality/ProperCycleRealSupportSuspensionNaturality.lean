import HodgeLean.Foundations.QuotientDuality.ProperCycleRealSupportNaturality

/-! # Naturality of the actual signed real support suspension
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The specified signed support suspension is natural under the literal real-product map of a complement-preserving base map, through the original relative pair maps.
Source: Hatcher, Algebraic Topology, section 2.2; properCycle_real_support_transport_connecting; properCycle_real_support_left_transport; properCycle_real_support_right_transport; properCycle_real_support_projection_homology_naturality.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_support_suspension_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) (T : Set X) (U : Set Y)
    (h : Set.MapsTo f Tᶜ Uᶜ) (hT : IsClosed T) (hU : IsClosed U) (n : ℕ) :
    HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
        (properCycle_real_support_zero_pair_map f T U h)) (n+1) ≫
        (properCycle_real_support_suspension_iso Y U hU n).hom =
      (properCycle_real_support_suspension_iso X T hT n).hom ≫
        HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f h)) n := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n
  let RX := properCycle_real_support_right_iso X T hT (n+1)
  let RY := properCycle_real_support_right_iso Y U hU (n+1)
  let DX := properCycle_real_cap_target_connecting_iso X T hT n
  let DY := properCycle_real_cap_target_connecting_iso Y U hU n
  let LX := H.mapIso (properCycle_real_support_left_iso X T)
  let LY := H.mapIso (properCycle_real_support_left_iso Y U)
  let PX := properCycle_product_support_homology_iso ℝ X T n
  let PY := properCycle_product_support_homology_iso ℝ Y U n
  let I := HomologicalComplex.homologyMap (properCycle_real_support_sequence_map f T U h).τ₁ n
  let J := HomologicalComplex.homologyMap (properCycle_real_support_sequence_map f T U h).τ₃ (n+1)
  let MZ := HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
    (properCycle_real_support_zero_pair_map f T U h)) (n+1)
  let MN := HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
    (properCycle_real_support_normal_pair_map f T U h)) n
  let MB := HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f h)) n
  have hr := congrArg (fun m => HomologicalComplex.homologyMap m (n+1))
    (properCycle_real_support_right_transport f T U h)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hr
  rw [← properCycle_real_support_right_iso_homology Y U hU (n+1),
    ← properCycle_real_support_right_iso_homology X T hT (n+1)] at hr
  change J ≫ RY.hom = RX.hom ≫ MZ at hr
  have hl := congrArg (fun m => HomologicalComplex.homologyMap m n)
    (properCycle_real_support_left_transport f T U h)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hl
  change I ≫ LY.hom = LX.hom ≫ MN at hl
  have hd := properCycle_real_support_transport_connecting f T U h hT hU n
  change DX.hom ≫ I = J ≫ DY.hom at hd
  have hp := properCycle_real_support_projection_homology_naturality f T U h n
  change MN ≫ PY.hom = PX.hom ≫ MB at hp
  change MZ ≫ (RY.inv ≫ DY.hom ≫ LY.hom ≫ PY.hom) =
    (RX.inv ≫ DX.hom ≫ LX.hom ≫ PX.hom) ≫ MB
  apply (cancel_epi RX.hom).mp
  calc
    _ = (RX.hom ≫ MZ) ≫ RY.inv ≫ DY.hom ≫ LY.hom ≫ PY.hom := by simp only [Category.assoc]
    _ = (J ≫ RY.hom) ≫ RY.inv ≫ DY.hom ≫ LY.hom ≫ PY.hom := by rw [← hr]
    _ = J ≫ DY.hom ≫ LY.hom ≫ PY.hom := by simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = DX.hom ≫ I ≫ LY.hom ≫ PY.hom := by
      simpa only [Category.assoc] using congrArg (fun m => m ≫ LY.hom ≫ PY.hom) hd.symm
    _ = DX.hom ≫ LX.hom ≫ MN ≫ PY.hom := by
      simpa only [Category.assoc] using congrArg (fun m => DX.hom ≫ m ≫ PY.hom) hl
    _ = DX.hom ≫ LX.hom ≫ PX.hom ≫ MB := by
      simpa only [Category.assoc] using congrArg (fun m => DX.hom ≫ LX.hom ≫ m) hp
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id_assoc]

end HodgeLean.Foundations.QuotientDuality
