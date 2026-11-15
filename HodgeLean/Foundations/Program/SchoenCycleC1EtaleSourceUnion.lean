import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Unions of actual etale source neighbourhoods -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The specified morphism is etale on the union of any family of source
opens on which its actual restrictions are etale. -/
theorem s2e_c1_etale_source_iSup
    {X Y : Scheme} (f : X ⟶ Y) {ι : Type*} (V : ι → X.Opens)
    (hV : ∀ i, Etale ((V i).ι ≫ f)) :
    Etale ((⨆ i, V i).ι ≫ f) := by
  let O := ⨆ i, V i
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale)
    (fun i => O.ι ⁻¹ᵁ V i)
  · apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp x.property
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro i
    letI : Etale ((V i).ι ≫ f) := hV i
    change Etale ((O.ι ⁻¹ᵁ V i).ι ≫ (O.ι ≫ f))
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    infer_instance

end HodgeLean.Foundations.Program
