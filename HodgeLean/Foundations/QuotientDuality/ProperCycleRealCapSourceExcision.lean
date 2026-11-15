import HodgeLean.Foundations.QuotientDuality.ProperCycleRealCapSourceRefinement
import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenPairQuotient

/-! # Excision on the actual left cap source refinement
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Open-pair excision applies to the literal left leg of the cap source refinement.
Source: Hatcher, Algebraic Topology, section 2.2; properCycle_open_pair_quotient_quasiIso.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_cap_source_refinement_left_quasiIso
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T) :
    QuasiIso (properCycle_real_cap_source_refinement Y S T).τ₁ := by
  let X := TopCat.of (ℝ × Y)
  let U : Set X := Prod.snd ⁻¹' Sᶜ
  let V : Set X := {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ ∩ {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
  have hU : IsOpen U := hS.isOpen_compl.preimage continuous_snd
  have hV : IsOpen V :=
    (((isClosed_le continuous_const continuous_fst).inter
      (hT.preimage continuous_snd)).isOpen_compl).inter
    (((isClosed_le continuous_fst continuous_const).inter
      (hT.preimage continuous_snd)).isOpen_compl)
  have hset : U ∪ V =
      {z : X | 0 ≤ z.1 ∧ z.2 ∈ S ∩ T}ᶜ ∩
      {z : X | z.1 ≤ 0 ∧ z.2 ∈ S ∩ T}ᶜ := by
    ext z
    simp only [U, V, Set.mem_union, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_compl_iff, Set.mem_ofPred_eq]
    tauto
  have h := properCycle_open_pair_quotient_quasiIso X U V hU hV
  have transport {K : SSet.{0}} {A B A' B' : K.Subcomplex}
      (hA : A = A') (hB : B = B') (hAB : A ≤ B) (hAB' : A' ≤ B')
      (hq : QuasiIso (properCycle_subcomplex_quotient_map hAB)) :
      QuasiIso (properCycle_subcomplex_quotient_map hAB') := by
    subst A'
    subst B'
    exact hq
  have hdom : subsetSingularSubcomplex X U ⊔ subsetSingularSubcomplex X V =
      subsetSingularSubcomplex X U ⊔
        (subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ ⊓
          subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ) := by
    rw [show V = _ from rfl, subsetSingularSubcomplex_inter]
  have hcod : subsetSingularSubcomplex X (U ∪ V) =
      subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ S ∩ T}ᶜ ⊓
        subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ S ∩ T}ᶜ := by
    rw [hset, subsetSingularSubcomplex_inter]
  dsimp only [properCycle_real_cap_source_refinement, ShortComplex.comp_τ₁,
    properCycle_fixed_subcomplex_sequence_iso, ShortComplex.isoMk,
    properCycle_subcomplex_mv_refinement, properCycle_subcomplex_quotient_iso_of_eq,
    id_eq, ShortComplex.homMk, ShortComplex.Hom.comp]
  erw [properCycle_subcomplex_quotient_map_comp]
  exact transport hdom hcod _ _ h

end HodgeLean.Foundations.QuotientDuality
