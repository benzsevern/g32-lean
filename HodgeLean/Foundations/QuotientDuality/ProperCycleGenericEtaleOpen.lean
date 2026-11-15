import HodgeLean.Foundations.QuotientDuality.ProperCycleGenericFiniteOpen
import HodgeLean.Foundations.Program.SchoenCycleC1ComplexGenericEtaleHelpers
import HodgeLean.Foundations.Program.SchoenCycleC11EtaleSmoothHelpers

/-! # Actual dense finite etale base neighborhoods -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- A proper map with the specified generic image and positive residue degree has an actual dense finite etale base neighborhood.
Source: Stacks Project, Tag 02UP; SGA 1, Expose I, generic etaleness in characteristic zero.
HC no distance; AV milestone no distance. -/
lemma properCycle_generically_finite_etale_base_open
    {X Y : Over (Spec ↧ℂ)} [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left]
    (hgeneric : f.left (genericPoint X.left) = genericPoint Y.left)
    (hdegree : 0 < a1p_degree f.left (genericPoint X.left)) :
    ∃ U : Y.left.Opens, Dense (U : Set Y.left) ∧ IsFinite (f.left ∣_ U) ∧ Etale (f.left ∣_ U) := by
  obtain ⟨U, hU, _, hfinite⟩ := properCycle_generically_finite_base_open f hgeneric hdegree
  letI : Surjective f.left := properCycle_proper_surjective_of_generic_image f hgeneric
  letI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  letI : Nonempty U := ⟨⟨genericPoint Y.left, hU⟩⟩
  letI : Nonempty (f.left ⁻¹ᵁ U) := ⟨⟨genericPoint X.left, by
    change f.left (genericPoint X.left) ∈ U
    rwa [hgeneric]⟩⟩
  let XU := openScheme X (f.left ⁻¹ᵁ U)
  let YU := openScheme Y U
  let fU := s2e_c11_restricted_over_morphism X Y f U
  letI : Nonempty XU.left := ⟨⟨genericPoint X.left, by
    change f.left (genericPoint X.left) ∈ U
    rwa [hgeneric]⟩⟩
  letI : Nonempty YU.left := ⟨⟨genericPoint Y.left, hU⟩⟩
  letI : IsIntegral XU.left := isIntegral_of_isOpenImmersion (f.left ⁻¹ᵁ U).ι
  letI : IsIntegral YU.left := isIntegral_of_isOpenImmersion U.ι
  letI : IsLocallyNoetherian YU.left := LocallyOfFiniteType.isLocallyNoetherian U.ι
  letI : IsFinite fU.left := hfinite
  letI : Surjective fU.left := by
    constructor
    intro y
    obtain ⟨x, hx⟩ := f.left.surjective y.1
    refine ⟨⟨x, by change f.left x ∈ U; rw [hx]; exact y.2⟩, ?_⟩
    apply Subtype.ext
    exact (morphismRestrict_base_coe f.left U _).trans hx
  obtain ⟨V, hV, hfinV, hEtV⟩ := s2e_c1_complex_finite_exists_etale_base_open XU YU fU
  have hfin : IsFinite (f.left ∣_ U.ι ''ᵁ V) :=
    (MorphismProperty.arrow_mk_iso_iff @IsFinite (morphismRestrictRestrict f.left U V)).mp hfinV
  have hEt : Etale (f.left ∣_ U.ι ''ᵁ V) :=
    (MorphismProperty.arrow_mk_iso_iff @Etale (morphismRestrictRestrict f.left U V)).mp hEtV
  obtain ⟨v, hv⟩ := hV
  exact ⟨U.ι ''ᵁ V, (U.ι ''ᵁ V).isOpen.dense ⟨U.ι v, ⟨v, hv, rfl⟩⟩, hfin, hEt⟩

end HodgeLean.Foundations.QuotientDuality
