import HodgeLean.Foundations.Program.SchoenCycleC1NormalizationComparisonHelpers

/-! # The specified transition on isomorphic open bases -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The isomorphism of restricted normalizations is the actual specified
transition whenever that transition retains its generic and base squares. -/
theorem s2e_c1_normalization_transition_open_iso {T X Y : Scheme} [IsReduced T]
    (f : T ⟶ X) (g : T ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (b : X ⟶ Y) (w : f.normalization ⟶ g.normalization)
    (hw : f.toNormalization ≫ w = g.toNormalization)
    (hwb : w ≫ g.fromNormalization = f.fromNormalization ≫ b)
    (U : X.Opens) (V : Y.Opens) (e : U.toScheme ≅ V.toScheme)
    (hb : e.hom ≫ V.ι = U.ι ≫ b)
    (fU : T ⟶ U.toScheme) (gV : T ⟶ V.toScheme)
    [QuasiCompact fU] [QuasiSeparated fU] [QuasiCompact gV] [QuasiSeparated gV]
    (hf : fU ≫ U.ι = f) (hg : gV ≫ V.ι = g) (he : fU ≫ e.hom = gV) :
    ∃ E : (f.fromNormalization ⁻¹ᵁ U).toScheme ≅ (g.fromNormalization ⁻¹ᵁ V).toScheme,
      E.hom ≫ (g.fromNormalization ⁻¹ᵁ V).ι = (f.fromNormalization ⁻¹ᵁ U).ι ≫ w := by
  obtain ⟨E, u, v, hudom, hbase, hu, hv, huv⟩ :=
    s2e_c1_normalization_open_base_iso f g U V e fU gV hf hg he
  haveI : IsReduced f.normalization := inferInstance
  haveI : IsDominant u := hudom
  refine ⟨E, ?_⟩
  apply ext_of_isDominant_of_isSeparated g.fromNormalization ?_ u ?_
  · calc
      (E.hom ≫ (g.fromNormalization ⁻¹ᵁ V).ι) ≫ g.fromNormalization =
          (E.hom ≫ (g.fromNormalization ∣_ V)) ≫ V.ι := by
        rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc]
      _ = ((f.fromNormalization ∣_ U) ≫ e.hom) ≫ V.ι :=
        congrArg (fun h => h ≫ V.ι) hbase
      _ = ((f.fromNormalization ⁻¹ᵁ U).ι ≫ f.fromNormalization) ≫ b := by
        rw [Category.assoc, hb, ← Category.assoc, morphismRestrict_ι]
      _ = ((f.fromNormalization ⁻¹ᵁ U).ι ≫ w) ≫ g.fromNormalization := by
        simp only [Category.assoc, hwb]
  · rw [← Category.assoc, huv, hv, ← Category.assoc, hu, hw]

end HodgeLean.Foundations.Program
