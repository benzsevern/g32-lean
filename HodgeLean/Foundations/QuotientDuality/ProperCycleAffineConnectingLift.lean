import HodgeLean.Foundations.QuotientDuality.ProperCycleAffineHalfRaySequence

/-! # The specified two-half lift in the actual quotient sequence
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original two halves lifted to the actual middle term with their prescribed signs. -/
def properCycle_affine_half_ray_middle_chain (d : ℕ) :
    ModuleCat.of ℚ ℚ ⟶ (properCycle_affine_half_ray_sequence d).X₂.X (d+1) :=
  ((-1 : ℤ) ^ (d+1) • properCycle_affine_lower_relative_chain d) ≫
    (properCycle_affine_half_ray_upper_iso d).inv.f (d+1) ≫
      (biprod.inl : _ ⟶
        properCycle_subcomplex_quotient (properCycle_affine_upper_half_subcomplex d) ⊞
        properCycle_subcomplex_quotient (properCycle_affine_lower_half_subcomplex d)).f (d+1) +
  properCycle_affine_upper_relative_chain d ≫
    (properCycle_affine_half_ray_lower_iso d).inv.f (d+1) ≫
      (biprod.inr : _ ⟶
        properCycle_subcomplex_quotient (properCycle_affine_upper_half_subcomplex d) ⊞
        properCycle_subcomplex_quotient (properCycle_affine_lower_half_subcomplex d)).f (d+1)

/-- Projection to the first actual relative pair recovers the prescribed signed lower chain. -/
theorem properCycle_affine_middle_chain_fst (d : ℕ) :
    properCycle_affine_half_ray_middle_chain d ≫
      (biprod.fst :
        properCycle_subcomplex_quotient (properCycle_affine_upper_half_subcomplex d) ⊞
        properCycle_subcomplex_quotient (properCycle_affine_lower_half_subcomplex d) ⟶ _).f (d+1) ≫
        (properCycle_affine_half_ray_upper_iso d).hom.f (d+1) =
    (-1 : ℤ) ^ (d+1) • properCycle_affine_lower_relative_chain d := by
  simp only [properCycle_affine_half_ray_middle_chain, Preadditive.add_comp, Category.assoc,
    HomologicalComplex.biprod_inl_fst_f_assoc, HomologicalComplex.biprod_inr_fst_f_assoc,
    Category.id_comp, Category.comp_id, comp_zero, zero_comp, add_zero]
  rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f, Category.comp_id]

/-- Projection to the second actual relative pair recovers the specified upper chain. -/
theorem properCycle_affine_middle_chain_snd (d : ℕ) :
    properCycle_affine_half_ray_middle_chain d ≫
      (biprod.snd :
        properCycle_subcomplex_quotient (properCycle_affine_upper_half_subcomplex d) ⊞
        properCycle_subcomplex_quotient (properCycle_affine_lower_half_subcomplex d) ⟶ _).f (d+1) ≫
        (properCycle_affine_half_ray_lower_iso d).hom.f (d+1) =
      properCycle_affine_upper_relative_chain d := by
  simp only [properCycle_affine_half_ray_middle_chain, Preadditive.add_comp, Category.assoc,
    HomologicalComplex.biprod_inl_snd_f_assoc, HomologicalComplex.biprod_inr_snd_f_assoc,
    Category.id_comp, comp_zero, zero_comp, zero_add]
  rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f, Category.comp_id]

/-- The negative original equatorial cycle in the actual left term of the sequence. -/
def properCycle_affine_half_ray_left_cycle (d : ℕ) :
    ModuleCat.of ℚ ℚ ⟶ (properCycle_affine_half_ray_sequence d).X₁.cycles d :=
  -(properCycle_real_equator_face_cycle d ≫
    HomologicalComplex.cyclesMap (properCycle_affine_half_ray_left_iso d).inv d)

/-- The original cycle inclusion retains the negative equatorial chain in the actual left quotient. -/
theorem properCycle_affine_left_cycle_inclusion (d : ℕ) :
    properCycle_affine_half_ray_left_cycle d ≫
      (properCycle_affine_half_ray_sequence d).X₁.iCycles d =
      (-properCycle_real_equator_face_chain d) ≫ (properCycle_affine_half_ray_left_iso d).inv.f d := by
  rw [properCycle_affine_half_ray_left_cycle, Preadditive.neg_comp, Category.assoc,
    HomologicalComplex.cyclesMap_i, ← Category.assoc,
    properCycle_real_equator_face_cycle_inclusion, Preadditive.neg_comp]

/-- The actual middle-chain boundary is the original sequence image of the specified negative equatorial cycle. -/
theorem properCycle_affine_middle_boundary_lift (d : ℕ) :
    properCycle_affine_half_ray_left_cycle d ≫
        (properCycle_affine_half_ray_sequence d).X₁.iCycles d ≫
          (properCycle_affine_half_ray_sequence d).f.f d =
      properCycle_affine_half_ray_middle_chain d ≫
        (properCycle_affine_half_ray_sequence d).X₂.d (d+1) d := by
  rw [← Category.assoc, properCycle_affine_left_cycle_inclusion]
  apply HomologicalComplex.biprodX_ext_to
  · apply (cancel_mono ((properCycle_affine_half_ray_upper_iso d).hom.f d)).mp
    simp only [Category.assoc]
    have hf := congrArg (fun m => m.f d) (properCycle_affine_half_ray_left_fst d)
    simp only [HomologicalComplex.comp_f] at hf
    have hi : (properCycle_affine_half_ray_left_iso d).inv.f d ≫
        (properCycle_affine_half_ray_left_iso d).hom.f d = 𝟙 _ := by
      rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
    have hl :
        (((-properCycle_real_equator_face_chain d) ≫ (properCycle_affine_half_ray_left_iso d).inv.f d) ≫
          (properCycle_affine_half_ray_sequence d).f.f d) ≫ (biprod.fst : properCycle_subcomplex_quotient (properCycle_affine_upper_half_subcomplex d) ⊞ properCycle_subcomplex_quotient (properCycle_affine_lower_half_subcomplex d) ⟶ properCycle_subcomplex_quotient (properCycle_affine_upper_half_subcomplex d)).f d ≫
            (properCycle_affine_half_ray_upper_iso d).hom.f d =
        -(properCycle_real_equator_face_chain d ≫
          ((relativeChainFunctor ℚ).map (properCycle_equator_to_upper_half_ray_pair d)).f d) := by
      simp only [Category.assoc, hf, reassoc_of% hi, Category.id_comp, Preadditive.neg_comp]
    simp only [Category.assoc] at hl
    refine hl.trans ?_
    symm
    calc
      _ = (properCycle_affine_half_ray_middle_chain d ≫ (biprod.fst : properCycle_subcomplex_quotient (properCycle_affine_upper_half_subcomplex d) ⊞ properCycle_subcomplex_quotient (properCycle_affine_lower_half_subcomplex d) ⟶ properCycle_subcomplex_quotient (properCycle_affine_upper_half_subcomplex d)).f (d+1) ≫
          (properCycle_affine_half_ray_upper_iso d).hom.f (d+1)) ≫
          ((relativeChainFunctor ℚ).obj (properCycle_real_upper_half_ray_pair d)).d (d+1) d := by
        have h := congrArg (fun m => properCycle_affine_half_ray_middle_chain d ≫ m)
          ((biprod.fst ≫ (properCycle_affine_half_ray_upper_iso d).hom).comm (d+1) d).symm
        simpa only [HomologicalComplex.comp_f, Category.assoc,
          properCycle_affine_half_ray_sequence, properCycle_subcomplex_quotient_sequence,
          properCycle_affine_upper_half_subcomplex, properCycle_affine_lower_half_subcomplex] using h
      _ = _ := by rw [properCycle_affine_middle_chain_fst, properCycle_affine_signed_lower_boundary]
  · apply (cancel_mono ((properCycle_affine_half_ray_lower_iso d).hom.f d)).mp
    simp only [Category.assoc]
    have hf := congrArg (fun m => m.f d) (properCycle_affine_half_ray_left_snd d)
    simp only [HomologicalComplex.comp_f, HomologicalComplex.neg_f_apply] at hf
    have hi : (properCycle_affine_half_ray_left_iso d).inv.f d ≫
        (properCycle_affine_half_ray_left_iso d).hom.f d = 𝟙 _ := by
      rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
    have hl :
        (((-properCycle_real_equator_face_chain d) ≫ (properCycle_affine_half_ray_left_iso d).inv.f d) ≫
          (properCycle_affine_half_ray_sequence d).f.f d) ≫ (biprod.snd : properCycle_subcomplex_quotient (properCycle_affine_upper_half_subcomplex d) ⊞ properCycle_subcomplex_quotient (properCycle_affine_lower_half_subcomplex d) ⟶ properCycle_subcomplex_quotient (properCycle_affine_lower_half_subcomplex d)).f d ≫
            (properCycle_affine_half_ray_lower_iso d).hom.f d =
        properCycle_real_equator_face_chain d ≫
          ((relativeChainFunctor ℚ).map (properCycle_equator_to_lower_half_ray_pair d)).f d := by
      simp only [Category.assoc, hf, Preadditive.comp_neg, Preadditive.neg_comp,
        neg_neg, reassoc_of% hi, Category.id_comp]
    simp only [Category.assoc] at hl
    refine hl.trans ?_
    symm
    calc
      _ = (properCycle_affine_half_ray_middle_chain d ≫ (biprod.snd : properCycle_subcomplex_quotient (properCycle_affine_upper_half_subcomplex d) ⊞ properCycle_subcomplex_quotient (properCycle_affine_lower_half_subcomplex d) ⟶ properCycle_subcomplex_quotient (properCycle_affine_lower_half_subcomplex d)).f (d+1) ≫
          (properCycle_affine_half_ray_lower_iso d).hom.f (d+1)) ≫
          ((relativeChainFunctor ℚ).obj (properCycle_real_lower_half_ray_pair d)).d (d+1) d := by
        have h := congrArg (fun m => properCycle_affine_half_ray_middle_chain d ≫ m)
          ((biprod.snd ≫ (properCycle_affine_half_ray_lower_iso d).hom).comm (d+1) d).symm
        simpa only [HomologicalComplex.comp_f, Category.assoc,
          properCycle_affine_half_ray_sequence, properCycle_subcomplex_quotient_sequence,
          properCycle_affine_upper_half_subcomplex, properCycle_affine_lower_half_subcomplex] using h
      _ = _ := by rw [properCycle_affine_middle_chain_snd, properCycle_affine_upper_relative_boundary,
        properCycle_equator_chain_to_upper_boundary]

end HodgeLean.Foundations.QuotientDuality
