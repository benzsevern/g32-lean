import HodgeLean.Foundations.QuotientDuality.ProperCycleAffineConnectingLift

/-! # The actual connecting map on the specified affine two-half lift
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The image of the prescribed middle lift in the actual right quotient term. -/
def properCycle_affine_half_ray_right_chain (d : ℕ) :
    ModuleCat.of ℚ ℚ ⟶ (properCycle_affine_half_ray_sequence d).X₃.X (d+1) :=
  properCycle_affine_half_ray_middle_chain d ≫ (properCycle_affine_half_ray_sequence d).g.f (d+1)

/-- The specified two-half image is an actual cycle in the original right quotient. -/
theorem properCycle_affine_half_ray_right_boundary_zero (d : ℕ) :
    properCycle_affine_half_ray_right_chain d ≫
      (properCycle_affine_half_ray_sequence d).X₃.d (d+1) d = 0 := by
  rw [properCycle_affine_half_ray_right_chain, Category.assoc,
    (properCycle_affine_half_ray_sequence d).g.comm (d+1) d, ← Category.assoc,
    ← properCycle_affine_middle_boundary_lift]
  simp only [Category.assoc, ← HomologicalComplex.comp_f,
    (properCycle_affine_half_ray_sequence d).zero, HomologicalComplex.zero_f, comp_zero]

/-- The actual right cycle supplied by the original two-half lift. -/
def properCycle_affine_half_ray_right_cycle (d : ℕ) :
    ModuleCat.of ℚ ℚ ⟶ (properCycle_affine_half_ray_sequence d).X₃.cycles (d+1) :=
  (properCycle_affine_half_ray_sequence d).X₃.liftCycles
    (properCycle_affine_half_ray_right_chain d) d (by simp)
    (properCycle_affine_half_ray_right_boundary_zero d)

/-- The original connecting map on the specified lift gives the specified negative equatorial cycle class. -/
theorem properCycle_affine_half_ray_connecting_value (d : ℕ) :
    properCycle_affine_half_ray_right_cycle d ≫
        (properCycle_affine_half_ray_sequence d).X₃.homologyπ (d+1) ≫
          (properCycle_affine_half_ray_shortExact d).δ (d+1) d (by simp) =
      properCycle_affine_half_ray_left_cycle d ≫
        (properCycle_affine_half_ray_sequence d).X₁.homologyπ d := by
  have h := (properCycle_affine_half_ray_shortExact d).δ_eq (d+1) d (by simp)
    (properCycle_affine_half_ray_right_chain d)
    (properCycle_affine_half_ray_right_boundary_zero d)
    (properCycle_affine_half_ray_middle_chain d) rfl
    (properCycle_affine_half_ray_left_cycle d ≫ (properCycle_affine_half_ray_sequence d).X₁.iCycles d)
    (properCycle_affine_middle_boundary_lift d)
    ((ComplexShape.down ℕ).next d) rfl
  have he :
      (properCycle_affine_half_ray_sequence d).X₁.liftCycles
        (properCycle_affine_half_ray_left_cycle d ≫ (properCycle_affine_half_ray_sequence d).X₁.iCycles d)
        ((ComplexShape.down ℕ).next d) rfl (by
          rw [Category.assoc, HomologicalComplex.iCycles_d, comp_zero]) =
        properCycle_affine_half_ray_left_cycle d := by
    apply (cancel_mono ((properCycle_affine_half_ray_sequence d).X₁.iCycles d)).mp
    rw [HomologicalComplex.liftCycles_i]
  exact h.trans (congrArg (fun m => m ≫ (properCycle_affine_half_ray_sequence d).X₁.homologyπ d) he)

/-- The actual connecting image retains its negative coefficient under the specified original relative comparison. -/
theorem properCycle_affine_half_ray_connecting_original (d : ℕ) :
    properCycle_affine_half_ray_right_cycle d ≫
        (properCycle_affine_half_ray_sequence d).X₃.homologyπ (d+1) ≫
          (properCycle_affine_half_ray_shortExact d).δ (d+1) d (by simp) ≫
            HomologicalComplex.homologyMap (properCycle_affine_half_ray_left_iso d).hom d =
      -(properCycle_real_equator_face_cycle d ≫
        ((relativeChainFunctor ℚ).obj (properCycle_real_equator_pair d)).homologyπ d) := by
  have hc : HomologicalComplex.cyclesMap (properCycle_affine_half_ray_left_iso d).inv d ≫
      HomologicalComplex.cyclesMap (properCycle_affine_half_ray_left_iso d).hom d = 𝟙 _ := by
    rw [← HomologicalComplex.cyclesMap_comp, Iso.inv_hom_id, HomologicalComplex.cyclesMap_id]
  have hm :
      ((properCycle_real_equator_face_cycle d ≫
          HomologicalComplex.cyclesMap (properCycle_affine_half_ray_left_iso d).inv d) ≫
        (properCycle_affine_half_ray_sequence d).X₁.homologyπ d) ≫
          HomologicalComplex.homologyMap (properCycle_affine_half_ray_left_iso d).hom d =
        properCycle_real_equator_face_cycle d ≫
          ((relativeChainFunctor ℚ).obj (properCycle_real_equator_pair d)).homologyπ d := by
    simp only [Category.assoc, HomologicalComplex.homologyπ_naturality]
    simpa only [Category.assoc, Category.id_comp] using
      congrArg (fun m => properCycle_real_equator_face_cycle d ≫ m ≫
        ((relativeChainFunctor ℚ).obj (properCycle_real_equator_pair d)).homologyπ d) hc
  calc
    _ = (properCycle_affine_half_ray_left_cycle d ≫
        (properCycle_affine_half_ray_sequence d).X₁.homologyπ d) ≫
          HomologicalComplex.homologyMap (properCycle_affine_half_ray_left_iso d).hom d := by
      simpa only [Category.assoc] using congrArg
        (fun m => m ≫ HomologicalComplex.homologyMap (properCycle_affine_half_ray_left_iso d).hom d)
        (properCycle_affine_half_ray_connecting_value d)
    _ = _ := by
      simp only [properCycle_affine_half_ray_left_cycle, Preadditive.neg_comp]
      exact congrArg Neg.neg hm

/-- The original connecting image followed by actual tangential projection is minus the specified standard local class. -/
theorem properCycle_affine_half_ray_connecting_standard (d : ℕ) :
    relativeHomologyMap ℚ d (properCycle_real_equator_projection d)
      (((properCycle_affine_half_ray_right_cycle d ≫
        (properCycle_affine_half_ray_sequence d).X₃.homologyπ (d+1) ≫
          (properCycle_affine_half_ray_shortExact d).δ (d+1) d (by simp) ≫
            HomologicalComplex.homologyMap (properCycle_affine_half_ray_left_iso d).hom d).hom) 1) =
      -standardLocalClass ℚ d := by
  have h := ConcreteCategory.congr_hom (properCycle_affine_half_ray_connecting_original d) 1
  change _ = -(((properCycle_real_equator_face_cycle d ≫
    ((relativeChainFunctor ℚ).obj (properCycle_real_equator_pair d)).homologyπ d).hom) 1) at h
  refine (congrArg (relativeHomologyMap ℚ d (properCycle_real_equator_projection d)) h).trans ?_
  rw [map_neg, properCycle_real_equator_face_class_projection]

end HodgeLean.Foundations.QuotientDuality
