import HodgeLean.Foundations.Program.SchoenTowerI1aLocalFactors

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_pointwise_target_factor
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (T : Scheme) (f : U.toScheme ⟶ T)
    (hf : ∀ g, (a g).left.resLE U U (hiU g) ≫ f = f)
    (z : Spec ↧(s2v_i1a_chartInvariants X G a U hiU)) :
    ∃ (D : (Spec ↧(s2v_i1a_chartInvariants X G a U hiU)).Opens), z ∈ D ∧
      ∃ v : D.toScheme ⟶ T,
        (s2v_i1a_affineQuotientMap X G a U hiU ∣_ D) ≫ v =
          ((s2v_i1a_affineQuotientMap X G a U hiU) ⁻¹ᵁ D).ι ≫ f := by
  let q := s2v_i1a_affineQuotientMap X G a U hiU
  letI := s2v_i1ahi_chart_surjective X G a ha1 hamul U hU hiU
  obtain ⟨x, rfl⟩ := q.surjective z
  obtain ⟨O, hO, hxO, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : T.Opens) from trivial)
  obtain ⟨W, hW⟩ := s2v_i1ahi_target_open_quotient X G a ha1 hamul U hU hiU T f hf O
  have hxW : q x ∈ W := by
    change x ∈ q ⁻¹ᵁ W
    rw [hW]
    exact hxO
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrW⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxW W.isOpen
  exact ⟨PrimeSpectrum.basicOpen r, hxr,
    s2v_i1ahi_principal_target_factor X G a ha1 hamul U hU hiU T f hf O hO W hW r hrW⟩

lemma s2v_i1ahi_affine_descent
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (T : Scheme) (f : U.toScheme ⟶ T)
    (hf : ∀ g, (a g).left.resLE U U (hiU g) ≫ f = f) :
    ∃! v : Spec ↧(s2v_i1a_chartInvariants X G a U hiU) ⟶ T,
      s2v_i1a_affineQuotientMap X G a U hiU ≫ v = f := by
  choose D hz v hv using s2v_i1ahi_pointwise_target_factor X G a ha1 hamul U hU hiU T f hf
  have hD : (⨆ z, D z) = ⊤ := by
    apply top_unique
    intro z _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hz z⟩
  let q := s2v_i1a_affineQuotientMap X G a U hiU
  letI := s2v_i1ahi_chart_surjective X G a ha1 hamul U hU hiU
  letI := s2v_i1ahi_chart_schematic_dominance X G a U hU hiU
  haveI : IsIso U.toSpecΓ := by change IsIso hU.isoSpec.hom; infer_instance
  haveI : QuasiCompact q := by dsimp only [q, s2v_i1a_affineQuotientMap]; infer_instance
  exact s2v_i1ahi_assemble_descended_factors q f D hD v hv

end HodgeLean.Foundations.Program
