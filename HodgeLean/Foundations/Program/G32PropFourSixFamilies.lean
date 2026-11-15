import HodgeLean.Foundations.Program.G32PropFourSixPacked0444
import HodgeLean.Foundations.Program.G32PropFourSixPacked0443
import HodgeLean.Foundations.Program.G32PropFourSixPacked0443

/-! The specified 44 character pairs and four quaternionic representations,
from finite class data and actual supplier-generator traces.
HC no distance; AV milestone no distance. -/

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory HodgeLean.Papers
open scoped Classical

set_option maxHeartbeats 400000

/-- Representation families in the coordinate order of the supplier certificates.
Source: G32 v0.16, Proposition 4.6 and Appendix A. -/
theorem g32p_families_of_class_data (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (hsquare : ∀ g, D.label (g * g) = g32p_familiesSquare (D.label g))
    (htrace : ∀ k c, (g32p_recordedInductionGenerators k).character
      (g32p_literalRepresentative c) =
        HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue k c)) :
    ∃ (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G),
      (∀ j, Simple (τ j) ∧ Simple (τbar j) ∧ ¬ g32p_SelfDual (τ j) ∧
        ∀ g, (τbar j).character g = star ((τ j).character g)) ∧
      (∀ j, Simple (θ j) ∧ g32p_Quaternionic (θ j)) ∧
      (∀ j k, j ≠ k → IsEmpty (τ j ≅ τ k) ∧ IsEmpty (τ j ≅ τbar k)) ∧
      (∀ j k : Fin 4, j ≠ k → IsEmpty (θ j ≅ θ k)) ∧
      Nonempty (τ 2 ≅ g32p_rho) ∧
      (∀ σ : FDRep ℂ g32p_G, Simple σ →
        (¬ g32p_SelfDual σ → ∃ j, Nonempty (σ ≅ τ j) ∨ Nonempty (σ ≅ τbar j)) ∧
        (g32p_Quaternionic σ → ∃ j, Nonempty (σ ≅ θ j))) ∧
      (∀ j g, (τ j).character g =
        g32p_literalComplexValue (g32p_familiesPair j) (D.label g)) ∧
      (∀ j g, (τbar j).character g =
        g32p_literalComplexValue (g32p_familiesBar j) (D.label g)) ∧
      (∀ j g, (θ j).character g =
        g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) := by
  have htraceAll (k : Fin 408) (g : g32p_G) :
      (g32p_recordedInductionGenerators k).character g =
        HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue k (D.label g)) := by
    rw [← htrace]
    obtain ⟨u, hu⟩ := isConj_iff.mp (hconj g)
    rw [← hu, FDRep.char_conj]
  obtain ⟨W, hS, hW⟩ := g32p_families_realization D htraceAll
  have hsurj : Function.Surjective D.label :=
    fun c => ⟨g32p_literalRepresentative c, hrep c⟩
  refine ⟨(fun j => W (g32p_familiesPair j)),
    (fun j => W (g32p_familiesBar j)), (fun j => W (g32p_familiesQuat j)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    refine ⟨hS _, hS _, g32p_families_pair_not_selfDual D.label hsurj W hW j, ?_⟩
    intro g
    change (W (g32p_familiesBar j)).character g =
      star ((W (g32p_familiesPair j)).character g)
    rw [← g32p_families_selected_conjugate.1 j]
    exact g32p_families_character_conjugate D.label W hW _ g
  · intro j
    exact ⟨hS _, g32p_families_quaternionic D.label D.card hsquare W hW j⟩
  · intro j k hjk
    constructor
    · exact g32p_families_distinct D.label hsurj W hW _ _
        (fun he => hjk (g32p_families_indices.1 he))
    · exact g32p_families_distinct D.label hsurj W hW _ _
        (g32p_families_indices.2.2.2 j k)
  · intro j k hjk
    exact g32p_families_distinct D.label hsurj W hW _ _
      (fun he => hjk (g32p_families_indices.2.2.1 he))
  · exact g32p_families_natural_iso D.label hconj W hS hW
  · intro σ hσ
    letI := hσ
    exact ⟨g32p_families_pair_coverage D.label hrep hconj W hS hW σ,
      g32p_families_quaternionic_coverage D.label hrep hconj D.card hsquare W hS hW σ⟩
  · exact fun j => hW (g32p_familiesPair j)
  · exact fun j => hW (g32p_familiesBar j)
  · exact fun j => hW (g32p_familiesQuat j)

end HodgeLean.Foundations.Program
