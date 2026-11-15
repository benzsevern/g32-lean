import HodgeLean.Foundations.Program.G32Native.NormalizationTransitions

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Powers of a source action pass through its specified equivariant map. -/
theorem g32w_source_power {T X : Scheme} (u : T ⟶ T) (q : T ⟶ X)
    (d : X ⟶ X) (h : q ≫ d = u ≫ q) (n : ℕ) :
    q ≫ (End.of d ^ n).asHom = (End.of u ^ n).asHom ≫ q := by
  induction n with
  | zero => simp only [pow_zero]; exact (Category.comp_id q).trans (Category.id_comp q).symm
  | succ n ih =>
    rw [pow_succ, pow_succ]
    change q ≫ d ≫ (End.of d ^ n).asHom = (u ≫ (End.of u ^ n).asHom) ≫ q
    rw [← Category.assoc, h, Category.assoc, ih, Category.assoc]

/-- A finite source action gives an action of the same order on each actual normalization. -/
theorem g32w_normalization_deck {T : Scheme} (X : Over (Spec ↧ℂ))
    (f : T ⟶ X.left) [QuasiCompact f] [QuasiSeparated f]
    (u : T ≅ T) (hu : u.hom ≫ f = f) (m : ℕ)
    (hm : End.of u.hom ^ m = 1) :
    ∃ d : s2b_normalizationOver X f ⟶ s2b_normalizationOver X f,
      f.toNormalization ≫ d.left = u.hom ≫ f.toNormalization ∧
      d ≫ s2b_normalizationMap X f = s2b_normalizationMap X f ∧
      End.of d ^ m = 1 := by
  obtain ⟨E, hE, hbase⟩ := s2e_c1_normalization_source_iso f f u hu
  let d : s2b_normalizationOver X f ⟶ s2b_normalizationOver X f :=
    Over.homMk E.hom (by
      change E.hom ≫ (f.fromNormalization ≫ X.hom) = f.fromNormalization ≫ X.hom
      rw [← Category.assoc, hbase])
  have hd : d ≫ s2b_normalizationMap X f = s2b_normalizationMap X f :=
    Over.OverMorphism.ext hbase
  refine ⟨d, hE, hd, ?_⟩
  have hp : f.toNormalization ≫ (End.of E.hom ^ m).asHom = f.toNormalization := by
    rw [g32w_source_power u.hom f.toNormalization E.hom hE, hm]
    exact Category.id_comp _
  apply End.ext
  apply Over.OverMorphism.ext
  apply Scheme.Hom.normalization.hom_ext (f := f) _ _ f.fromNormalization
  · have hpow := ((Over.forget (Spec ↧ℂ)).mapEnd _).map_pow (End.of d) m
    have hpow' := congrArg End.asHom hpow
    change (End.of d ^ m).asHom.left = (End.of E.hom ^ m).asHom at hpow'
    rw [hpow']
    exact hp.trans (Category.comp_id _).symm
  · exact congrArg Over.Hom.left (s2e_c1_generator_power_over
      (s2b_normalizationMap X f) d hd m)
  · exact Category.id_comp _

/-- The lifted source action commutes with every source-preserving transition. -/
theorem g32w_normalization_deck_transition {T : Scheme} [IsReduced T]
    (X Y : Over (Spec ↧ℂ)) [IsSeparated Y.hom]
    (f : T ⟶ X.left) (g : T ⟶ Y.left)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (u : T ⟶ T)
    (w : s2b_normalizationOver X f ⟶ s2b_normalizationOver Y g)
    (hw : f.toNormalization ≫ w.left = g.toNormalization)
    (dX : s2b_normalizationOver X f ⟶ s2b_normalizationOver X f)
    (dY : s2b_normalizationOver Y g ⟶ s2b_normalizationOver Y g)
    (hX : f.toNormalization ≫ dX.left = u ≫ f.toNormalization)
    (hY : g.toNormalization ≫ dY.left = u ≫ g.toNormalization) :
    dX ≫ w = w ≫ dY := by
  haveI : IsSeparated (s2b_normalizationOver Y g).hom :=
    inferInstanceAs (IsSeparated (g.fromNormalization ≫ Y.hom))
  haveI : IsReduced (s2b_normalizationOver X f).left :=
    inferInstanceAs (IsReduced f.normalization)
  apply Over.OverMorphism.ext
  apply ext_of_isDominant_of_isSeparated (s2b_normalizationOver Y g).hom
    ((Over.w (dX ≫ w)).trans (Over.w (w ≫ dY)).symm) f.toNormalization
  change f.toNormalization ≫ (dX.left ≫ w.left) =
    f.toNormalization ≫ (w.left ≫ dY.left)
  rw [← Category.assoc, hX, Category.assoc, hw, ← Category.assoc, hw, hY]

end HodgeLean.Foundations.Program
