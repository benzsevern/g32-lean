import HodgeLean.Foundations.Program.G32Native.PairedC3ResidualQuotientCover

/-! # Actual quotient charts of inclusions of ideal subschemes -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The quotient-ring map for an inclusion of ideal subschemes is the
pullback of the original inclusion to its canonical affine chart. -/
theorem pairedC3_subscheme_inclusion_quotient_square
    {X : Scheme} (I L : X.IdealSheafData) (h : I ≤ L) (V : X.affineOpens) :
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (h V))))
      (L.subschemeCover.f V) (I.subschemeCover.f V)
      (Scheme.IdealSheafData.inclusion h) := by
  have hc : Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (h V))) ≫
      I.subschemeCover.f V = L.subschemeCover.f V ≫
        Scheme.IdealSheafData.inclusion h := by
    apply (cancel_mono I.subschemeι).mp
    rw [Category.assoc, Category.assoc,
      Scheme.IdealSheafData.inclusion_subschemeι,
      I.subschemeCover_map_subschemeι, L.subschemeCover_map_subschemeι,
      I.glueDataObjι_ι, L.glueDataObjι_ι, ← Spec.map_comp_assoc]
    congr 2
  apply IsOpenImmersion.isPullback
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (h V))))
    (L.subschemeCover.f V) (I.subschemeCover.f V)
    (Scheme.IdealSheafData.inclusion h) hc.symm
  rw [I.opensRange_subschemeCover_map, L.opensRange_subschemeCover_map,
    ← Scheme.Hom.comp_preimage, Scheme.IdealSheafData.inclusion_subschemeι]

#print axioms pairedC3_subscheme_inclusion_quotient_square
end HodgeLean.Foundations.Program.G32Native
