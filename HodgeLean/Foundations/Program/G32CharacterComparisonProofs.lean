import HodgeLean.Foundations.Program.G32CharacterComparisonRows1Proofs
import HodgeLean.Foundations.Program.G32CharacterComparisonRows2Proofs
import HodgeLean.Foundations.Program.G32CharacterComparisonRows3Proofs
import HodgeLean.Foundations.Program.G32CharacterComparisonRows4Proofs
import HodgeLean.Foundations.Program.G32CharacterComparisonRows5Proofs
import HodgeLean.Foundations.Program.G32CharacterComparisonRows6Proofs
import HodgeLean.Foundations.Program.G32CharacterComparisonClassProofs

/-! Finite character comparison interface. HC no distance; AV milestone no distance. -/
noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory HodgeLean.Papers
set_option maxHeartbeats 400000

theorem g32cc_rows (D : g32p_familiesClassData)
    (hrep : ∀ c, D.label (g32p_literalRepresentative c) = c)
    (hconj : ∀ g, IsConj g (g32p_literalRepresentative (D.label g)))
    (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G)
    (ht : ∀ j g, (τ j).character g =
      g32p_literalComplexValue (g32p_familiesPair j) (D.label g))
    (hb : ∀ j g, (τbar j).character g =
      g32p_literalComplexValue (g32p_familiesBar j) (D.label g))
    (hq : ∀ j g, (θ j).character g =
      g32p_literalComplexValue (g32p_familiesQuat j) (D.label g)) (i : Fin 51) :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = i.val + 1 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) ∧
      ∃ v ∈ g32VectorTable, v.i = i.val + 1 ∧
        papersA τ τbar θ S.H χc = g32SparseVec v.coords := by
  fin_cases i
  · exact g32cc_row01 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row02 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row03 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row04 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row05 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row06 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row07 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row08 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row09 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row10 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row11 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row12 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row13 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row14 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row15 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row16 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row17 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row18 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row19 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row20 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row21 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row22 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row23 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row24 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row25 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row26 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row27 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row28 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row29 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row30 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row31 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row32 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row33 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row34 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row35 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row36 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row37 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row38 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row39 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row40 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row41 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row42 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row43 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row44 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row45 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row46 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row47 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row48 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row49 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row50 D hrep hconj τ τbar θ ht hb hq
  · exact g32cc_row51 D hrep hconj τ τbar θ ht hb hq

theorem g32cc_character_comparison_aux : ∃ (S : Fin 51 → g32p_Supplier) (χc : ∀ i, (S i).H →* ℂˣ)
      (τ τbar : Fin 44 → FDRep ℂ g32p_G) (θ : Fin 4 → FDRep ℂ g32p_G),
      (∀ j, Simple (τ j) ∧ Simple (τbar j) ∧ ¬ g32p_SelfDual (τ j) ∧
        (∀ g, (τbar j).character g = star ((τ j).character g)) ∧ 0 < g32p_cwMult (τ j)) ∧
      (∀ j, Simple (θ j) ∧ g32p_Quaternionic (θ j) ∧ 0 < g32p_cwMult (θ j)) ∧
      (∀ j k, j ≠ k → IsEmpty (τ j ≅ τ k) ∧ IsEmpty (τ j ≅ τbar k)) ∧
      (∀ j k : Fin 4, j ≠ k → IsEmpty (θ j ≅ θ k)) ∧
      Nonempty (τ 2 ≅ g32p_rho) ∧
      (∀ σ : FDRep ℂ g32p_G, Simple σ → 0 < g32p_cwMult σ →
        (¬ g32p_SelfDual σ → ∃ j, Nonempty (σ ≅ τ j) ∨ Nonempty (σ ≅ τbar j)) ∧
        (g32p_Quaternionic σ → ∃ j, Nonempty (σ ≅ θ j))) ∧
      ∀ i : Fin 51,
        (∀ h, ((χc i h : ℂˣ) : ℂ) =
          g32p_root (S i).m ^ (Multiplicative.toAdd ((S i).χ h)).val) ∧
        (∃ r ∈ g32WitnessTable, r.i = i.val + 1 ∧ r.m = (S i).m ∧
          r.orderH = Nat.card (S i).H ∧ (g32p_exponents (S i)).Perm (expandExps r.exps)) ∧
        ∃ v ∈ g32VectorTable, v.i = i.val + 1 ∧
          papersA τ τbar θ (S i).H (χc i) = g32SparseVec v.coords := by
  obtain ⟨D, hrep, hconj, hsquare, hbranch, htrace⟩ := g32cc_class_data_aux
  obtain ⟨τ, τbar, θ, hp, hq, hd, hqd, hρ, hc, _, ht, hb, hθ⟩ :=
    g32p_familyCW_families_of_class_data D hrep hconj hsquare hbranch htrace
  have hr := g32cc_rows D hrep hconj τ τbar θ ht hb hθ
  choose S χc hroot htable hvector using hr
  exact ⟨S, χc, τ, τbar, θ, hp, hq, hd, hqd, hρ, hc,
    fun i => ⟨hroot i, htable i, hvector i⟩⟩

end HodgeLean.Foundations.Program
