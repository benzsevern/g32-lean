import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.BoundaryFiniteLocus

noncomputable section
open CategoryTheory TopologicalSpace
open scoped Classical
namespace AlgebraicGeometry.SingularCycles

set_option backward.isDefEq.respectTransparency false in
theorem boundary_flat_fiber_source_iso {X X' Y : Scheme} (e : X' ≅ X) (f : X ⟶ Y) :
    {y : Y | ∀ x : X', (e.hom ≫ f) x = y → ((e.hom ≫ f).stalkMap x).hom.Flat} =
      {y : Y | ∀ x : X, f x = y → (f.stalkMap x).hom.Flat} := by
  ext y
  constructor
  · intro h x hx
    have hx' : (e.hom ≫ f) (e.inv x) = y := by simpa using hx
    have hf := h (e.inv x) hx'
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
      RingHom.Flat.respectsIso.cancel_right_isIso] at hf
    have heq : e.hom (e.inv x) = x := by
      change (e.inv ≫ e.hom) x = x
      rw [e.inv_hom_id]
      rfl
    exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (f.arrowStalkMapIsoOfEq heq)).mp hf
  · intro h x hx
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
      RingHom.Flat.respectsIso.cancel_right_isIso]
    exact h (e.hom x) hx

set_option backward.isDefEq.respectTransparency false in
theorem boundary_flat_fiber_target_iso {X Y Y' : Scheme} (f : X ⟶ Y) (e : Y ≅ Y') :
    e.hom ⁻¹' {y : Y' | ∀ x : X, (f ≫ e.hom) x = y →
      ((f ≫ e.hom).stalkMap x).hom.Flat} =
      {y : Y | ∀ x : X, f x = y → (f.stalkMap x).hom.Flat} := by
  ext y
  constructor
  · intro h x hx
    have hf := h x (show (f ≫ e.hom) x = e.hom y by
      change e.hom (f x) = e.hom y
      rw [hx])
    rwa [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
      RingHom.Flat.respectsIso.cancel_left_isIso] at hf
  · intro h x hx
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
      RingHom.Flat.respectsIso.cancel_left_isIso]
    exact h x (e.hom.isOpenEmbedding.injective hx)

end AlgebraicGeometry.SingularCycles
