import HodgeLean.Foundations.Program.SchoenTowerI1aGluedFiniteness
import HodgeLean.Foundations.Program.SchoenTowerI1aComplexGluing

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_quotient_from_affine_cover
    (X : Over (Spec ↧ℂ)) [X.left.IsSeparated]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (hcover : (⨆ U : {U : X.left.affineOpens // ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1}, U.1.1) = ⊤)
    (hfin : ∀ (U : X.left.Opens) (hU : IsAffineOpen U)
      (hi : ∀ g, U ≤ (a g).left ⁻¹ᵁ U),
      IsFinite (s2v_i1a_affineQuotientMap X G a U hi)) :
    ∃ (Q : Over (Spec ↧ℂ)) (q : X ⟶ Q),
      IsFinite q.left ∧ Surjective q.left ∧ (∀ g, a g ≫ q = q) ∧
      ∀ (U : X.left.Opens), IsAffineOpen U →
        ∀ (hi : ∀ g, U ≤ (a g).left ⁻¹ᵁ U),
        ∃ (V : Q.left.Opens)
          (e : Spec ↧(s2v_i1a_chartInvariants X G a U hi) ≅ V.toScheme),
          q.left ⁻¹ᵁ V = U ∧
          U.ι ≫ q.left = s2v_i1a_affineQuotientMap X G a U hi ≫ e.hom ≫ V.ι := by
  let F := s2v_i1ahi_chartDiagram X G a
  haveI {U V} (f : U ⟶ V) : IsOpenImmersion (F.map f) :=
    s2v_i1ahi_chartDiagram_openImmersion X G a ha1 hamul f
  letI := s2v_i1ahi_chartDiagram_locallyDirected X G a ha1 hamul
  let Q := colimit F
  let ι := colimit.ι F
  have hi U : IsOpenImmersion (ι U) := inferInstance
  have hj : ∀ z : Q, ∃ U p, ι U p = z := Scheme.IsLocallyDirected.ι_jointly_surjective F
  have ho U V (p : F.obj U) (q : F.obj V) :
      ι U p = ι V q → ∃ L, ∃ (f : L ⟶ U) (g : L ⟶ V), ∃ t,
        F.map f t = p ∧ F.map g t = q :=
    (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp
  obtain ⟨q, hq, _⟩ := s2v_i1ahi_glued_source_map X G a hcover Q ι (fun _ _ f => colimit.w F f)
  have hpre U : q ⁻¹' Set.range (ι U) = (U.1.1 : Set X.left) :=
    s2v_i1ahi_glued_chart_preimage X G a ha1 hamul hcover Q ι ho q hq U
  have hqfin : IsFinite q := s2v_i1ahi_glued_source_finite X G a Q ι hi hj q hq hpre
    (fun U => hfin U.1.1 U.1.2 U.2)
  have hqsurj : Surjective q := s2v_i1ahi_glued_source_surjective X G a ha1 hamul Q ι hj q hq
  obtain ⟨s, hs⟩ := s2v_i1ahi_glued_complex_structure X G a ha1 hamul
    (colimit.cocone F) (colimit.isColimit F)
  have hbase : q ≫ s = X.hom := by
    apply (X.left.openCoverOfIsOpenCover
      (fun U : {U : X.left.affineOpens // ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1} => U.1.1) hcover).hom_ext
    intro U
    change U.1.1.ι ≫ q ≫ s = U.1.1.ι ≫ X.hom
    rw [← Category.assoc, hq, Category.assoc]
    exact hs U
  let Qc : Over (Spec ↧ℂ) := Over.mk s
  let qc : X ⟶ Qc := Over.homMk q hbase
  refine ⟨Qc, qc, hqfin, hqsurj, ?_, ?_⟩
  · intro g
    apply Over.OverMorphism.ext
    exact s2v_i1ahi_glued_source_invariant X G a hcover Q ι q hq g
  · intro U hU hiU
    let u : {U : X.left.affineOpens // ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1} := ⟨⟨U, hU⟩, hiU⟩
    refine ⟨(ι u).opensRange, (ι u).isoOpensRange, ?_, ?_⟩
    · apply TopologicalSpace.Opens.ext
      exact hpre u
    · rw [Scheme.Hom.isoOpensRange_hom_ι]
      exact hq u

end HodgeLean.Foundations.Program
