import HodgeLean.Foundations.Program.SchoenCycleC1EtaleSourceUnion

/-! # Unions of actual etale base restrictions -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Etaleness over actual base opens glues over their union, including the
whole inverse image of that union. -/
theorem s2e_c1_etale_base_iSup
    {X Y : Scheme} (f : X ⟶ Y) {ι : Type*} (U : ι → Y.Opens)
    (hU : ∀ i, Etale (f ∣_ U i)) : Etale (f ∣_ ⨆ i, U i) := by
  have hs (i) : Etale ((f ⁻¹ᵁ U i).ι ≫ f) := by
    letI := hU i
    rw [← morphismRestrict_ι]
    infer_instance
  have he := s2e_c1_etale_source_iSup f (fun i => f ⁻¹ᵁ U i) hs
  letI : Etale ((f ⁻¹ᵁ (⨆ i, U i)).ι ≫ f) := by
    rw [f.preimage_iSup]
    exact he
  letI : Etale ((f ∣_ ⨆ i, U i) ≫ (⨆ i, U i).ι) := by
    rw [morphismRestrict_ι]
    infer_instance
  exact Etale.of_comp _ (⨆ i, U i).ι

end HodgeLean.Foundations.Program
