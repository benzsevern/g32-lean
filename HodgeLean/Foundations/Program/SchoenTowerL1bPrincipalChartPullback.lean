import HodgeLean.Foundations.Program.SchoenTowerL1aIdealPullback
import HodgeLean.Foundations.Program.SchoenTowerL1aIdealOpenRestriction

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Exact principal equations on an affine restriction pull back to affine inverse images. -/
theorem s2v_l1b_principal_chart_pullback
    {X Y : Scheme} (f : X ⟶ Y) [IsAffineHom f]
    (O : Y.affineOpens) (I : Y.IdealSheafData)
    (u : Γ(O.1.toScheme, ⊤))
    (hu : (I.comap O.1.ι).ideal ⟨⊤, @isAffineOpen_top _ O.2⟩ = Ideal.span {u}) :
    ∃ v : Γ(X, f ⁻¹ᵁ O.1),
      (I.comap f).ideal ⟨f ⁻¹ᵁ O.1, O.2.preimage f⟩ = Ideal.span {v} := by
  let U : X.affineOpens := ⟨f ⁻¹ᵁ O.1, O.2.preimage f⟩
  letI : IsAffine O.1.toScheme := O.2
  letI : IsAffine U.1.toScheme := U.2
  have H : ((I.comap f).comap U.1.ι).ideal ⟨⊤, @isAffineOpen_top _ U.2⟩ =
      Ideal.span {(f ∣_ O.1).appTop.hom u} := by
    rw [← Scheme.IdealSheafData.comap_comp, ← morphismRestrict_ι,
      Scheme.IdealSheafData.comap_comp, s2v_l1a_affine_ideal_pullback,
      hu, Ideal.map_span, Set.image_singleton]
  rw [s2v_l1a_open_ideal_top] at H
  let e := U.1.topIso.symm.commRingCatIsoToRingEquiv
  refine ⟨e.symm ((f ∣_ O.1).appTop.hom u), ?_⟩
  change ((I.comap f).ideal U).comap e.symm.toRingHom = _ at H
  have H' := congrArg (Ideal.map e.symm.toRingHom) H
  rw [Ideal.map_comap_of_surjective e.symm.toRingHom e.symm.surjective,
    Ideal.map_span, Set.image_singleton] at H'
  exact H'

end HodgeLean.Foundations.Program
