import HodgeLean.Foundations.QuotientDuality.ModificationOpenFibres

/-! The normalized transition is an open immersion on the actual isomorphism open. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

theorem normalization_transition_openImmersion_on_preimage
    {K : Type} [Field K] (X Y : Over (Spec ↧ℂ))
    [IsIntegral X.left] [IsIntegral Y.left] [IsSeparated Y.hom]
    (f : Spec (CommRingCat.of K) ⟶ X.left)
    (g : Spec (CommRingCat.of K) ⟶ Y.left)
    [QuasiCompact f] [QuasiSeparated f] [IsDominant f]
    [QuasiCompact g] [QuasiSeparated g] [IsDominant g]
    (b : X ⟶ Y) (hfg : f ≫ b.left = g)
    (w : s2b_normalizationOver X f ⟶ s2b_normalizationOver Y g)
    (hw : f.toNormalization ≫ w.left = g.toNormalization)
    (V : Y.left.Opens) (hV : (V : Set Y.left).Nonempty)
    [IsIso (b.left ∣_ V)] :
    IsOpenImmersion
      ((f.fromNormalization ⁻¹ᵁ (b.left ⁻¹ᵁ V)).ι ≫ w.left) := by
  let U := b.left ⁻¹ᵁ V
  have hU : (U : Set X.left).Nonempty := by
    obtain ⟨y, hy⟩ := hV
    obtain ⟨x, _⟩ := (b.left ∣_ V).surjective ⟨y, hy⟩
    exact ⟨x.val, x.property⟩
  obtain ⟨fU, hfqc, hfqs, hf⟩ := s2e_c1_generic_source_lift_to_open X.left f U hU
  obtain ⟨gV, hgqc, hgqs, hg⟩ := s2e_c1_generic_source_lift_to_open Y.left g V hV
  letI := hfqc
  letI := hfqs
  letI := hgqc
  letI := hgqs
  let e := asIso (b.left ∣_ V)
  have hb : e.hom ≫ V.ι = U.ι ≫ b.left := morphismRestrict_ι b.left V
  have he : fU ≫ e.hom = gV := by
    rw [← cancel_mono V.ι, Category.assoc, hb,
      ← Category.assoc, hf, hg, hfg]
  have hwb := s2e_c1_normalization_transition_over X Y b f g hfg w hw
  have hwb' : w.left ≫ g.fromNormalization = f.fromNormalization ≫ b.left :=
    congrArg Over.Hom.left hwb
  obtain ⟨E, hE⟩ := s2e_c1_normalization_transition_open_iso f g b.left w.left hw hwb'
    U V e (morphismRestrict_ι b.left V) fU gV hf hg he
  change IsOpenImmersion ((f.fromNormalization ⁻¹ᵁ U).ι ≫ w.left)
  rw [← hE]
  infer_instance

#print axioms normalization_transition_openImmersion_on_preimage
end HodgeLean.Foundations.QuotientDuality
