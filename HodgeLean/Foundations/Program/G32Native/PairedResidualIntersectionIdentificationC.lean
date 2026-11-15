import HodgeLean.Foundations.Program.G32Native.PairedResidualIntersection

/-! # Scheme identifications from the residual intersection ideal -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native.FibreC

variable {S : Scheme} {P V : Over S} (i : P ⟶ V)
  [IsClosedImmersion i.left] (J : V.left.IdealSheafData)

/-- Equality with the pulled residual ideal identifies the actual intersection subscheme. -/
theorem residualIntersection_iso_of_comap_eq
    (K : P.left.IdealSheafData) (hK : J.comap i.left = K) :
    ∃ e : (residualIntersection i J).left ≅ K.subscheme,
      e.hom ≫ K.subschemeι = (residualIntersectionFirst i J).left := by
  let a := (residualIntersectionFirst i J).left
  have h : K.subschemeι.ker = a.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, residualIntersectionFirst_kernel, hK]
  let l := IsClosedImmersion.lift K.subschemeι a h.le
  have hl : l ≫ K.subschemeι = a := IsClosedImmersion.lift_fac _ _ _
  haveI : IsIso l := IsClosedImmersion.isIso_lift K.subschemeι a h
  exact ⟨asIso l, hl⟩

/-- A compatible scheme identification determines the pulled ideal, including its nilpotents. -/
theorem residualIntersection_comap_eq_of_iso
    (K : P.left.IdealSheafData)
    (e : (residualIntersection i J).left ≅ K.subscheme)
    (he : e.hom ≫ K.subschemeι = (residualIntersectionFirst i J).left) :
    J.comap i.left = K := by
  rw [← residualIntersectionFirst_kernel, ← he,
    Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

/-- Compatible intersection identifications are equivalent to equality of the actual ideals. -/
theorem residualIntersection_iso_iff_comap_eq
    (K : P.left.IdealSheafData) :
    (∃ e : (residualIntersection i J).left ≅ K.subscheme,
      e.hom ≫ K.subschemeι = (residualIntersectionFirst i J).left) ↔
      J.comap i.left = K := by
  constructor
  · rintro ⟨e, he⟩
    exact residualIntersection_comap_eq_of_iso i J K e he
  · exact residualIntersection_iso_of_comap_eq i J K

#print axioms residualIntersection_iso_of_comap_eq
#print axioms residualIntersection_comap_eq_of_iso
#print axioms residualIntersection_iso_iff_comap_eq
end HodgeLean.Foundations.Program.G32Native.FibreC
