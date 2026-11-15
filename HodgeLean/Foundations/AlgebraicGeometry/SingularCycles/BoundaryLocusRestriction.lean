import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.BoundaryLocusTransport

noncomputable section
open CategoryTheory TopologicalSpace
open scoped Classical
namespace AlgebraicGeometry.SingularCycles

set_option backward.isDefEq.respectTransparency false in
theorem boundary_flat_fiber_restrict {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) :
    U.ι ⁻¹' {y : Y | ∀ x : X, f x = y → (f.stalkMap x).hom.Flat} =
      {y : U.toScheme | ∀ x : (f ⁻¹ᵁ U).toScheme, (f ∣_ U) x = y →
        ((f ∣_ U).stalkMap x).hom.Flat} := by
  ext y
  constructor
  · intro h x hx
    apply (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap f U x)).mpr
    apply h x.1
    exact (morphismRestrict_base_coe f U x).symm.trans (congrArg Subtype.val hx)
  · intro h x hx
    have hxU : f x ∈ U := hx ▸ y.2
    let x' : (f ⁻¹ᵁ U).toScheme := ⟨x, hxU⟩
    have hx' : (f ∣_ U) x' = y := Subtype.ext
      ((morphismRestrict_base_coe f U x').trans hx)
    exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap f U x')).mp (h x' hx')

end AlgebraicGeometry.SingularCycles
