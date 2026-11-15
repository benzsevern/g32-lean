import HodgeLean.Foundations.Program.SchoenTransferQ3InverseReducedSupport
import HodgeLean.Foundations.Program.SchoenTransferQ3FiniteGenericOpen
import HodgeLean.Foundations.Program.SchoenTransferQ3RegularSupportFibreMultiplicity

/-! One actual support base for the etale comparison and generic unreduced length. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
open HodgeLean.Adapters AlgebraicGeometry.SingularCycles
namespace HodgeLean.Foundations.Program

/-- The same finite support base supplies smooth etale pieces, an open
underlying reduced piece, and the retained generic length at every regular
support point in that piece. -/
theorem s4_q3_component_generic_length_base
    {X W C D : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    [IsIntegral C.left] [IsIntegral D.left] [LocallyOfFinitePresentation D.hom]
    (q : X ⟶ W) (x : W.left) (η : (ccm3_inverseIdeal q.left x).subscheme)
    (hη : closure ({η} : Set (ccm3_inverseIdeal q.left x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal q.left x).subscheme)
    [IsNoetherian (ccm3_inverseIdeal q.left x).subscheme]
    (ψ : C.left ⟶ (ccm3_inverseIdeal q.left x).subscheme) [IsClosedImmersion ψ]
    (himage : Set.range ψ = closure ({η} : Set (ccm3_inverseIdeal q.left x).subscheme))
    (hgeneric : ψ (genericPoint C.left) = η)
    (κ : (ccm3_inverseIdeal q.left x).subscheme ⟶ D.left) [IsFinite κ]
    (f : C ⟶ D) [IsFinite f.left] (hsurj : Function.Surjective f.left)
    (hcompat : ψ ≫ κ = f.left)
    (S₀ : D.left.Opens) (hd₀ : Dense (S₀ : Set D.left)) (he₀ : Etale (f.left ∣_ S₀)) :
    ∃ S : D.left.Opens, Dense (S : Set D.left) ∧ S ≤ S₀ ∧
      Smooth (S.ι ≫ D.hom) ∧ Etale (f.left ∣_ S) ∧
      Smooth ((f.left ⁻¹ᵁ S).ι ≫ C.hom) ∧
      IsOpenEmbedding ((((f.left ⁻¹ᵁ S).ι ≫ ψ)).base) ∧
      ∀ (c : C.left), f.left c ∈ S → ∀ (r : ℕ), Order.coheight (f.left c) = r →
        IsRegularLocalRing (D.left.presheaf.stalk (f.left c)) →
        pointFibreLength κ (ψ c) =
          (genericMultiplicity q.left x η (ccm3_genericLength_finite_pos q x η hη).2 : ℕ∞) := by
  obtain ⟨R₀, hηR₀, hψR₀, _⟩ := s4_q3_closed_component_open_piece ψ η hη himage
  let O₀ := ψ ⁻¹ᵁ R₀
  have hO₀ : genericPoint C.left ∈ O₀ := by
    change ψ (genericPoint C.left) ∈ R₀
    rw [hgeneric]
    exact hηR₀
  obtain ⟨S₁, hd₁, hS₁₀, hpre₁, hsD₁, he₁, hsC₁⟩ :=
    s4_q3_smooth_etale_refinement_in_source_open f S₀ hd₀ he₀ O₀ hO₀
  let P := ComplexPoint.openScheme C (f.left ⁻¹ᵁ S₁)
  let ψ₁ := (f.left ⁻¹ᵁ S₁).ι ≫ ψ
  have hfac₁ : C.left.homOfLE hpre₁ ≫ ((ψ ⁻¹ᵁ R₀).ι ≫ ψ) = ψ₁ := by
    rw [← Category.assoc, Scheme.homOfLE_ι]
  have hopen₁ : IsOpenEmbedding ψ₁.base := by
    rw [← hfac₁]
    exact hψR₀.comp (C.left.homOfLE hpre₁).isOpenEmbedding
  letI : Etale (f.left ∣_ S₁) := he₁
  have hEtκ₁ : Etale (ψ₁ ≫ κ) := by
    have hfac : ψ₁ ≫ κ = (f.left ∣_ S₁) ≫ S₁.ι := by
      rw [morphismRestrict_ι]
      exact Category.assoc _ _ _ |>.trans (congrArg ((f.left ⁻¹ᵁ S₁).ι ≫ ·) hcompat)
    rw [hfac]
    infer_instance
  letI : Etale (ψ₁ ≫ κ) := hEtκ₁
  letI : IsLocallyNoetherian D.left := LocallyOfFiniteType.isLocallyNoetherian D.hom
  obtain ⟨R, hηR, hR⟩ :=
    s4_q3_regular_support_point_fibre_generic_multiplicity q x η hη κ ψ₁ hopen₁
  have hgen₁ : genericPoint C.left ∈ f.left ⁻¹ᵁ S₁ := by
    obtain ⟨d, hd⟩ := hd₁.nonempty
    obtain ⟨c, hc⟩ := hsurj d
    have hcS : f.left c ∈ S₁ := by rw [hc]; exact hd
    exact (genericPoint_specializes c).mem_open (f.left ⁻¹ᵁ S₁).isOpen hcS
  let O := (f.left ⁻¹ᵁ S₁) ⊓ (ψ ⁻¹ᵁ R)
  have hO : genericPoint C.left ∈ O := by
    refine ⟨hgen₁, ?_⟩
    change ψ (genericPoint C.left) ∈ R
    rw [hgeneric]
    exact hηR
  obtain ⟨S, hdS, hSS₁, hpre, hsD, he, hsC⟩ :=
    s4_q3_smooth_etale_refinement_in_source_open f S₁ hd₁ he₁ O hO
  have hpreR₀ : f.left ⁻¹ᵁ S ≤ ψ ⁻¹ᵁ R₀ := fun c hc => hpre₁ (hpre hc).1
  let ψS := (f.left ⁻¹ᵁ S).ι ≫ ψ
  have hfacS : C.left.homOfLE hpreR₀ ≫ ((ψ ⁻¹ᵁ R₀).ι ≫ ψ) = ψS := by
    rw [← Category.assoc, Scheme.homOfLE_ι]
  have hopenS : IsOpenEmbedding ψS.base := by
    rw [← hfacS]
    exact hψR₀.comp (C.left.homOfLE hpreR₀).isOpenEmbedding
  refine ⟨S, hdS, hSS₁.trans hS₁₀, hsD, he, hsC, hopenS, ?_⟩
  intro c hc r hr hreg
  let p : P.left := ⟨c, (hpre hc).1⟩
  have hpR : ψ₁ p ∈ R := (hpre hc).2
  have hpco : Order.coheight (κ (ψ₁ p)) = r := by
    change Order.coheight ((ψ ≫ κ) c) = r
    rw [hcompat]
    exact hr
  have hpreg : IsRegularLocalRing (D.left.presheaf.stalk (κ (ψ₁ p))) := by
    change IsRegularLocalRing (D.left.presheaf.stalk ((ψ ≫ κ) c))
    rw [hcompat]
    exact hreg
  exact hR p hpR r hpco hpreg

end HodgeLean.Foundations.Program
