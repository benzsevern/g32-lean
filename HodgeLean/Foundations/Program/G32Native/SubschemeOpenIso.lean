import HodgeLean.Foundations.Program.G32Native.SubschemeOpenNeighbourhood

/-! Identify the pulled closed subscheme with the actual restricted source. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Restricting an ideal to an ambient open gives the open restriction of its subscheme. -/
def g32l4_subscheme_comap_open_iso {X : Scheme}
    (I : X.IdealSheafData) (U : X.Opens) :
    (I.comap U.ι).subscheme ≅ (I.subschemeι ⁻¹ᵁ U).toScheme :=
  I.comapIso U.ι ≪≫ (isPullback_morphismRestrict I.subschemeι U).isoPullback.symm

/-- The comparison identifies the actual closed immersions into the ambient open. -/
theorem g32l4_subscheme_comap_open_iso_hom_restrict {X : Scheme}
    (I : X.IdealSheafData) (U : X.Opens) :
    (g32l4_subscheme_comap_open_iso I U).hom ≫ (I.subschemeι ∣_ U) =
      (I.comap U.ι).subschemeι := by
  change (I.comapIso U.ι).hom ≫
    (isPullback_morphismRestrict I.subschemeι U).isoPullback.inv ≫
      (I.subschemeι ∣_ U) = _
  rw [IsPullback.isoPullback_inv_fst, Scheme.IdealSheafData.comapIso_hom_fst]

/-- The open comparison retains the original ambient map. -/
theorem g32l4_subscheme_comap_open_iso_to_ambient {X : Scheme}
    (I : X.IdealSheafData) (U : X.Opens) :
    (g32l4_subscheme_comap_open_iso I U).hom ≫ (I.subschemeι ⁻¹ᵁ U).ι ≫
      I.subschemeι = (I.comap U.ι).subschemeι ≫ U.ι := by
  rw [← morphismRestrict_ι I.subschemeι U, ← Category.assoc,
    g32l4_subscheme_comap_open_iso_hom_restrict]

/-- A subscheme point in an ambient open lifts to the actual pulled-ideal subscheme. -/
theorem g32l4_subscheme_comap_open_lift_point {X : Scheme}
    (I : X.IdealSheafData) (U : X.Opens) (z : I.subscheme) (hz : I.subschemeι z ∈ U) :
    ∃ y : (I.comap U.ι).subscheme, U.ι ((I.comap U.ι).subschemeι y) = I.subschemeι z := by
  let e := g32l4_subscheme_comap_open_iso I U
  let p : (I.subschemeι ⁻¹ᵁ U).toScheme := ⟨z, hz⟩
  let y := e.inv p
  have hey : e.hom y = p := by
    change (e.inv ≫ e.hom) p = p
    rw [e.inv_hom_id]
    rfl
  have h := congrArg (fun k => k y) (g32l4_subscheme_comap_open_iso_to_ambient I U)
  simp only [Scheme.Hom.comp_apply] at h
  rw [hey] at h
  exact ⟨y, h.symm⟩

end HodgeLean.Foundations.Program
