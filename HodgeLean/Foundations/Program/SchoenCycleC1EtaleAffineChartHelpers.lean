import HodgeLean.Foundations.Program.SchoenCycleC1ComplexGenericEtaleHelpers

/-! # Affine charts inside actual etale base neighbourhoods -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A smaller base open retains etaleness of the entire inverse image. -/
theorem s2e_c1_etale_restriction_of_le
    {X Y : Scheme} (f : X ⟶ Y) (U A : Y.Opens) (hAU : A ≤ U)
    [Etale (f ∣_ U)] : Etale (f ∣_ A) := by
  let V := U.ι ⁻¹ᵁ A
  have he : U.ι ''ᵁ V = A := by
    simp only [V, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hAU
  have hEt : Etale (f ∣_ U ∣_ V) := inferInstance
  have hEt' : Etale (f ∣_ U.ι ''ᵁ V) :=
    (MorphismProperty.arrow_mk_iso_iff @Etale (morphismRestrictRestrict f U V)).mp hEt
  rwa [he] at hEt'

end HodgeLean.Foundations.Program
