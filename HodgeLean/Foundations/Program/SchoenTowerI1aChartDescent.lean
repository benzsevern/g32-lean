import HodgeLean.Foundations.Program.SchoenTowerI1aChartTransitions
import HodgeLean.Foundations.Program.SchoenTowerI1aEpimorphisms

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_chart_schematic_dominance
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U) :
    IsSchemeTheoreticallyDominant (s2v_i1a_affineQuotientMap X G a U hiU) := by
  let j := CommRingCat.ofHom (s2v_i1a_chartInvariants X G a U hiU).subtype
  haveI : IsIso U.toSpecΓ := by change IsIso hU.isoSpec.hom; infer_instance
  haveI : IsSchemeTheoreticallyDominant (Spec.map j) :=
    s2v_i1ahi_schematic_dominance_of_appTop (Spec.map j)
      (s2v_i1ahi_specMap_appTop_injective j
        (s2v_i1a_chartInvariants X G a U hiU).subtype_injective)
  exact inferInstanceAs (IsSchemeTheoreticallyDominant (U.toSpecΓ ≫ Spec.map j))

lemma s2v_i1ahi_chart_epi
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U) :
    Epi (s2v_i1a_affineQuotientMap X G a U hiU) := by
  haveI : IsIso U.toSpecΓ := by change IsIso hU.isoSpec.hom; infer_instance
  letI := s2v_i1ahi_chart_surjective X G a ha1 hamul U hU hiU
  letI := s2v_i1ahi_chart_schematic_dominance X G a U hU hiU
  haveI : QuasiCompact (s2v_i1a_affineQuotientMap X G a U hiU) := by
    dsimp only [s2v_i1a_affineQuotientMap]
    infer_instance
  exact s2v_i1ahi_scheme_epi_of_schematic_dominance _

lemma s2v_i1ahi_invariant_target_open_source
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U : X.left.Opens) (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (T : Scheme) (f : U.toScheme ⟶ T)
    (hf : ∀ g, (a g).left.resLE U U (hiU g) ≫ f = f) (O : T.Opens) :
    ∀ g, U.ι ''ᵁ (f ⁻¹ᵁ O) ≤ (a g).left ⁻¹ᵁ (U.ι ''ᵁ (f ⁻¹ᵁ O)) := by
  intro g t ht
  obtain ⟨x, hx, rfl⟩ := ht
  refine ⟨(a g).left.resLE U U (hiU g) x, ?_, ?_⟩
  · change f ((a g).left.resLE U U (hiU g) x) ∈ O
    have he := congrArg (fun h : U.toScheme ⟶ T => h x) (hf g)
    change f ((a g).left.resLE U U (hiU g) x) = f x at he
    rw [he]
    exact hx
  · exact congrArg (fun h : U.toScheme ⟶ X.left => h x)
      (Scheme.Hom.resLE_comp_ι (a g).left (hiU g))

lemma s2v_i1ahi_target_open_quotient
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (T : Scheme) (f : U.toScheme ⟶ T)
    (hf : ∀ g, (a g).left.resLE U U (hiU g) ≫ f = f) (O : T.Opens) :
    ∃ W : (Spec ↧(s2v_i1a_chartInvariants X G a U hiU)).Opens,
      (s2v_i1a_affineQuotientMap X G a U hiU) ⁻¹ᵁ W = f ⁻¹ᵁ O := by
  let N := U.ι ''ᵁ (f ⁻¹ᵁ O)
  have hiN := s2v_i1ahi_invariant_target_open_source X G a U hiU T f hf O
  let W : (Spec ↧(s2v_i1a_chartInvariants X G a U hiU)).Opens :=
    ⟨s2v_i1a_affineQuotientMap X G a U hiU '' {x | U.ι x ∈ N},
      s2v_i1ahi_chart_open_image X G a ha1 hamul U hU hiU N hiN⟩
  refine ⟨W, ?_⟩
  have he : (s2v_i1a_affineQuotientMap X G a U hiU) ⁻¹ᵁ W = U.ι ⁻¹ᵁ N := by
    apply TopologicalSpace.Opens.ext
    exact s2v_i1ahi_chart_saturated_preimage X G a ha1 hamul U hU hiU N hiN
  exact he.trans (U.ι.preimage_image_eq (f ⁻¹ᵁ O))

end HodgeLean.Foundations.Program
