import HodgeLean.Foundations.Program.SchoenInvariantAffineGluing

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The diagram of the original invariant affine open subschemes. -/
def s2_invariantAffineSourceDiagram (X : Scheme.{0}) (G : Type) [Group G]
    (ρ : G →* Aut X) : s2_InvariantAffineOpen X G ρ ⥤ Scheme.{0} where
  obj U := U.val.toScheme
  map {U V} i := X.homOfLE i.le
  map_id U := X.homOfLE_rfl U.val
  map_comp i j := (X.homOfLE_homOfLE i.le j.le).symm

instance s2_invariantAffineSourceDiagram_map_openImmersion (X : Scheme.{0})
    (G : Type) [Group G] (ρ : G →* Aut X) {U V : s2_InvariantAffineOpen X G ρ} (i : U ⟶ V) :
    IsOpenImmersion ((s2_invariantAffineSourceDiagram X G ρ).map i) :=
  inferInstanceAs (IsOpenImmersion (X.homOfLE i.le))

/-- Source chart inclusions form a cocone with vertex the original scheme. -/
def s2_invariantAffineSourceCocone (X : Scheme.{0}) (G : Type) [Group G]
    (ρ : G →* Aut X) : Cocone (s2_invariantAffineSourceDiagram X G ρ) where
  pt := X
  ι.app U := U.val.ι
  ι.naturality {U V} i := (X.homOfLE_ι i.le).trans (Category.id_comp _).symm

/-- The source open diagram is locally directed through its affine intersections. -/
instance s2_invariantAffineSourceDiagram_locallyDirected (X : Scheme.{0}) [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (G : Type) [Group G] (ρ : G →* Aut X) :
    ((s2_invariantAffineSourceDiagram X G ρ) ⋙ Scheme.forget).IsLocallyDirected := by
  constructor
  intro U V W i j u v huv
  have hv : u.val = v.val := by
    have ha := congrArg (fun w : W.val.toScheme => w.val) huv
    change (X.homOfLE i.le u).val = (X.homOfLE j.le v).val at ha
    exact (X.homOfLE_apply i.le u).symm.trans (ha.trans (X.homOfLE_apply j.le v))
  have huV : u.val ∈ V.val := hv.symm ▸ v.property
  let L := s2_invariantAffineOpenInf X G ρ U V
  have hLU : L ≤ U := show U.val ⊓ V.val ≤ U.val from inf_le_left
  have hLV : L ≤ V := show U.val ⊓ V.val ≤ V.val from inf_le_right
  let z : L.val.toScheme := ⟨u.val, u.property, huV⟩
  refine ⟨L, homOfLE hLU, homOfLE hLV, z, ?_, ?_⟩
  · apply Subtype.ext
    exact X.homOfLE_apply hLU z
  · apply Subtype.ext
    exact (X.homOfLE_apply hLV z).trans hv

section
variable (X : Scheme.{0}) [IsIntegral X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (G : Type) [Group G] (ρ : G →* Aut X)

/-- The canonical map from the gluing of the source charts to the original scheme. -/
def s2_invariantSourceToScheme : colimit (s2_invariantAffineSourceDiagram X G ρ) ⟶ X :=
  colimit.desc _ (s2_invariantAffineSourceCocone X G ρ)

/-- The source gluing map restricts to each original open immersion. -/
@[reassoc]
theorem s2_invariantSourceToScheme_ι (U : s2_InvariantAffineOpen X G ρ) :
    colimit.ι (s2_invariantAffineSourceDiagram X G ρ) U ≫ s2_invariantSourceToScheme X G ρ = U.val.ι :=
  colimit.ι_desc _ U

/-- The source gluing map is injective because intersections identify equal ambient points. -/
theorem s2_invariantSourceToScheme_injective :
    Function.Injective (s2_invariantSourceToScheme X G ρ) := by
  intro a b hab
  obtain ⟨U, u, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (s2_invariantAffineSourceDiagram X G ρ) a
  obtain ⟨V, v, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (s2_invariantAffineSourceDiagram X G ρ) b
  have heu := congrArg (fun m => m u) (s2_invariantSourceToScheme_ι X G ρ U)
  have hev := congrArg (fun m => m v) (s2_invariantSourceToScheme_ι X G ρ V)
  simp only [Scheme.Hom.comp_apply] at heu hev
  have hval : u.val = v.val := heu.symm.trans (hab.trans hev)
  have huV : u.val ∈ V.val := hval.symm ▸ v.property
  let L := s2_invariantAffineOpenInf X G ρ U V
  have hLU : L ≤ U := show U.val ⊓ V.val ≤ U.val from inf_le_left
  have hLV : L ≤ V := show U.val ⊓ V.val ≤ V.val from inf_le_right
  let z : L.val.toScheme := ⟨u.val, u.property, huV⟩
  apply (Scheme.IsLocallyDirected.ι_eq_ι_iff (s2_invariantAffineSourceDiagram X G ρ)).mpr
  refine ⟨L, homOfLE hLU, homOfLE hLV, z, ?_, ?_⟩
  · apply Subtype.ext
    exact X.homOfLE_apply hLU z
  · apply Subtype.ext
    exact (X.homOfLE_apply hLV z).trans hval

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical source gluing map is an open immersion on its union of charts. -/
instance s2_invariantSourceToScheme_openImmersion :
    IsOpenImmersion (s2_invariantSourceToScheme X G ρ) := by
  apply IsOpenImmersion.of_forall_source_exists _ (s2_invariantSourceToScheme_injective X G ρ)
  intro p
  obtain ⟨U, u, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (s2_invariantAffineSourceDiagram X G ρ) p
  refine ⟨U.val.toScheme, colimit.ι (s2_invariantAffineSourceDiagram X G ρ) U,
    inferInstance, ?_, ?_⟩
  · exact ⟨u, rfl⟩
  · rw [s2_invariantSourceToScheme_ι]
    infer_instance

/-- Covering the source by invariant affine opens identifies its gluing with the source. -/
theorem s2_invariantSourceToScheme_isIso
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val) :
    IsIso (s2_invariantSourceToScheme X G ρ) := by
  have hsurj : Function.Surjective (s2_invariantSourceToScheme X G ρ) := by
    intro x
    obtain ⟨U, hx⟩ := hcover x
    let u : U.val.toScheme := ⟨x, hx⟩
    refine ⟨colimit.ι (s2_invariantAffineSourceDiagram X G ρ) U u, ?_⟩
    exact congrArg (fun m => m u) (s2_invariantSourceToScheme_ι X G ρ U)
  haveI : Epi (s2_invariantSourceToScheme X G ρ).base := ConcreteCategory.epi_of_surjective _ hsurj
  exact IsOpenImmersion.isIso (s2_invariantSourceToScheme X G ρ)

end
end HodgeLean.Foundations.Program
