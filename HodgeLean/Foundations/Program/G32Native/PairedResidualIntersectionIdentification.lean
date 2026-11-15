import HodgeLean.Foundations.Program.G32Native.PairedResidualIntersection

/-! # Identifying the retained intersection by its ideal -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native.FibreB

/-- Two immersions with the same ideal determine an isomorphism over their ambient scheme. -/
def residualIsoOfKernelEq {X Y P : Scheme} (a : X ⟶ P) (h : Y ⟶ P)
    [IsClosedImmersion a] [IsClosedImmersion h] (he : a.ker = h.ker) : X ≅ Y where
  hom := IsClosedImmersion.lift h a (by rw [← he])
  inv := IsClosedImmersion.lift a h (by rw [he])
  hom_inv_id := by
    apply (cancel_mono a).mp
    rw [Category.assoc, IsClosedImmersion.lift_fac, IsClosedImmersion.lift_fac,
      Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono h).mp
    rw [Category.assoc, IsClosedImmersion.lift_fac, IsClosedImmersion.lift_fac,
      Category.id_comp]

@[reassoc]
theorem residualIsoOfKernelEq_hom {X Y P : Scheme} (a : X ⟶ P) (h : Y ⟶ P)
    [IsClosedImmersion a] [IsClosedImmersion h] (he : a.ker = h.ker) :
    (residualIsoOfKernelEq a h he).hom ≫ h = a :=
  IsClosedImmersion.lift_fac _ _ _

/-- The immersion equation in the fibre-diagram target is equivalent to equality
of the actual ideals on the retained component. -/
theorem residual_intersection_identification_iff
    {C : Scheme} {P V : Over C} (i : P ⟶ V) [IsClosedImmersion i.left]
    (J : V.left.IdealSheafData) (H : Scheme) (h : H ⟶ P.left)
    [IsClosedImmersion h] :
    (∃ e : (residualIntersection i J).left ≅ H,
      e.hom ≫ h = (residualIntersectionFirst i J).left) ↔
      J.comap i.left = h.ker := by
  constructor
  · rintro ⟨e, he⟩
    rw [← residualIntersectionFirst_kernel i J, ← he, Scheme.Hom.ker_comp_of_isIso]
  · intro he
    have hk : (residualIntersectionFirst i J).left.ker = h.ker :=
      (residualIntersectionFirst_kernel i J).trans he
    exact ⟨residualIsoOfKernelEq _ h hk, residualIsoOfKernelEq_hom _ h hk⟩

/-- For a subscheme specified by an ideal, the criterion uses that same ideal,
without changing the parametrization of the retained component. -/
theorem residual_intersection_subscheme_iff
    {C : Scheme} {P V : Over C} (i : P ⟶ V) [IsClosedImmersion i.left]
    (J : V.left.IdealSheafData) (K : P.left.IdealSheafData) :
    (∃ e : (residualIntersection i J).left ≅ K.subscheme,
      e.hom ≫ K.subschemeι = (residualIntersectionFirst i J).left) ↔
      J.comap i.left = K := by
  rw [residual_intersection_identification_iff i J K.subscheme K.subschemeι,
    Scheme.IdealSheafData.ker_subschemeι]

end HodgeLean.Foundations.Program.G32Native.FibreB
