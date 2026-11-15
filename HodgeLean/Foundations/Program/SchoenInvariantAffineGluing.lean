import HodgeLean.Foundations.Program.SchoenInvariantAffineDiagram

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The invariant affine quotient diagram is locally directed: equality in a
larger quotient chart is represented on an invariant affine intersection. -/
instance s2_invariantAffineDiagram_locallyDirected (X : Scheme.{0}) [IsIntegral X]
    [IsAffineHom (CategoryTheory.Limits.pullback.diagonal (CategoryTheory.Limits.terminal.from X))]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X) :
    ((s2_invariantAffineDiagram X G ρ) ⋙ Scheme.forget).IsLocallyDirected := by
  constructor
  intro U V W i j pu pv hab
  obtain ⟨u, hu⟩ := s2_affineSchemeQuotientMap_surjective U.val.toScheme G
    (s2_invariantAffineOpenAction X G ρ U) pu
  obtain ⟨v, hv⟩ := s2_affineSchemeQuotientMap_surjective V.val.toScheme G
    (s2_invariantAffineOpenAction X G ρ V) pv
  let uW := X.homOfLE i.le u
  let vW := X.homOfLE j.le v
  have hqu : (s2_invariantAffineDiagram X G ρ).map i pu =
      s2_invariantAffineProjection X G ρ W uW := by
    rw [← hu]
    exact congrArg (fun m => m u) (s2_invariantAffineProjection_naturality X G ρ U W i.le)
  have hqv : (s2_invariantAffineDiagram X G ρ).map j pv =
      s2_invariantAffineProjection X G ρ W vW := by
    rw [← hv]
    exact congrArg (fun m => m v) (s2_invariantAffineProjection_naturality X G ρ V W j.le)
  have he := hqu.symm.trans (hab.trans hqv)
  obtain ⟨g, hg⟩ := (s2_affineSchemeQuotientMap_fibres W.val.toScheme G
    (s2_invariantAffineOpenAction X G ρ W) uW vW).mp he
  have hambient : (ρ g).asIso.hom u.val = v.val := by
    have ha := congrArg (fun w : W.val.toScheme => w.val) hg
    simpa only [s2_invariantAffineOpenAction_apply, uW, vW, Scheme.homOfLE_apply] using ha
  have hu' : ((s2_invariantAffineOpenAction X G ρ U g).asIso.hom u).val = v.val :=
    (s2_invariantAffineOpenAction_apply X G ρ U g u).trans hambient
  have hvU : v.val ∈ U.val := hu' ▸ ((s2_invariantAffineOpenAction X G ρ U g).asIso.hom u).property
  let L := s2_invariantAffineOpenInf X G ρ U V
  have hLU : L ≤ U := show U.val ⊓ V.val ≤ U.val from inf_le_left
  have hLV : L ≤ V := show U.val ⊓ V.val ≤ V.val from inf_le_right
  let z : L.val.toScheme := ⟨v.val, hvU, v.property⟩
  refine ⟨L, homOfLE hLU, homOfLE hLV, s2_invariantAffineProjection X G ρ L z, ?_, ?_⟩
  · have heU := congrArg (fun m => m z) (s2_invariantAffineProjection_naturality X G ρ L U hLU)
    have hzU : X.homOfLE hLU z = (s2_invariantAffineOpenAction X G ρ U g).asIso.hom u := by
      apply Subtype.ext
      simpa only [Scheme.homOfLE_apply] using hu'.symm
    change s2_invariantAffineQuotientMap X G ρ L U hLU
      (s2_invariantAffineProjection X G ρ L z) = pu
    simp only [Scheme.Hom.comp_apply] at heU
    rw [heU, hzU]
    exact (congrArg (fun m => m u) (s2_affineSchemeQuotientMap_invariant U.val.toScheme G
      (s2_invariantAffineOpenAction X G ρ U) g)).trans hu
  · have heV := congrArg (fun m => m z) (s2_invariantAffineProjection_naturality X G ρ L V hLV)
    have hzV : X.homOfLE hLV z = v := by
      apply Subtype.ext
      simp only [Scheme.homOfLE_apply]
      rfl
    change s2_invariantAffineQuotientMap X G ρ L V hLV
      (s2_invariantAffineProjection X G ρ L z) = pv
    simp only [Scheme.Hom.comp_apply] at heV
    rw [heV, hzV]
    exact hv

section
variable (X : Scheme.{0}) [IsIntegral X]
    [IsAffineHom (CategoryTheory.Limits.pullback.diagonal (CategoryTheory.Limits.terminal.from X))]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)

/-- The scheme obtained by gluing all nonempty invariant affine quotient charts. -/
def s2_invariantAffineGlued : Scheme.{0} :=
  CategoryTheory.Limits.colimit (s2_invariantAffineDiagram X G ρ)

/-- The open immersion of an invariant quotient chart into the glued scheme. -/
def s2_invariantAffineGluedι (U : s2_InvariantAffineOpen X G ρ) :
    s2_invariantAffineQuotientObj X G ρ U ⟶ s2_invariantAffineGlued X G ρ :=
  CategoryTheory.Limits.colimit.ι (s2_invariantAffineDiagram X G ρ) U

instance s2_invariantAffineGluedι_openImmersion (U : s2_InvariantAffineOpen X G ρ) :
    IsOpenImmersion (s2_invariantAffineGluedι X G ρ U) :=
  inferInstanceAs (IsOpenImmersion (CategoryTheory.Limits.colimit.ι (s2_invariantAffineDiagram X G ρ) U))

/-- The invariant affine quotient charts cover the glued scheme. -/
theorem s2_invariantAffineGluedι_jointly_surjective (p : s2_invariantAffineGlued X G ρ) :
    ∃ (U : s2_InvariantAffineOpen X G ρ) (u : s2_invariantAffineQuotientObj X G ρ U),
      s2_invariantAffineGluedι X G ρ U u = p :=
  Scheme.IsLocallyDirected.ι_jointly_surjective (s2_invariantAffineDiagram X G ρ) p

end
end HodgeLean.Foundations.Program
