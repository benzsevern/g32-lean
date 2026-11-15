import HodgeLean.Foundations.QuotientDuality.ProperCycleOriginalCapBijectivity
import HodgeLean.Foundations.QuotientDuality.ProperCycleRealCapMiddleVanishing

/-! # Real suspension for the original relative cap -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original triad cap suspends across the actual real half-ray cover, with all subdivision comparisons and middle-group contractions constructed from the specified supports.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, relative Mayer--Vietoris and cap suspension.
HC no distance; AV milestone no distance. -/
lemma properCycle_original_real_cap_suspension_bijective
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℕ) (hp : Even p) :
    let X := TopCat.of (ℝ × Y)
    let A : Set X := Prod.snd ⁻¹' Sᶜ
    let P : Set X := {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q : Set X := {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    ∀ (φ : RelativeCochain ℚ (TopPair.ofSubset (X := X) A) p)
      (hφ : relativeCoboundary ℚ (TopPair.ofSubset (X := X) A) p φ = 0),
      Function.Bijective (triadCapHomologyMap ℚ X A (P ∩ Q) p q φ hφ) →
      Function.Bijective (triadCapHomologyMap ℚ X A (P ∪ Q) p (q + 1) φ hφ) := by
  dsimp only
  intro φ hφ hc
  let X := TopCat.of (ℝ × Y)
  let A : Set X := Prod.snd ⁻¹' Sᶜ
  let P : Set X := {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
  let Q : Set X := {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
  let ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj X) p :=
    ⟨relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) p φ, by
      change AlgebraicTopology.Simplicial.coboundary ℚ p _ = 0
      exact (relativeCochainToAbsolute_coboundary ℚ (TopPair.ofSubset (X := X) A) p φ).symm.trans
        ((congrArg (relativeCochainToAbsolute ℚ (TopPair.ofSubset (X := X) A) (p + 1)) hφ).trans
          (map_zero _))⟩
  have hAo : IsOpen A := hS.isOpen_compl.preimage continuous_snd
  have hPo : IsOpen P := ((isClosed_le continuous_const continuous_fst).inter
    (hT.preimage continuous_snd)).isOpen_compl
  have hQo : IsOpen Q := ((isClosed_le continuous_fst continuous_const).inter
    (hT.preimage continuous_snd)).isOpen_compl
  have hlo := (properCycle_original_triad_cap_bijective_iff X A (P ∩ Q) p q hp φ hφ).mpr hc
  rw [subsetSingularSubcomplex_inter] at hlo
  have hup := properCycle_real_cap_suspension_bijective Y S T hS hT p q hp ψ.1 ψ.2
    (properCycle_relative_cochain_subcomplex_zero X A p φ) hlo
  rw [subsetSingularSubcomplex_sup] at hup
  have hcover : ⋃ b : Bool, (if b then P else Q) = P ∪ Q := by
    ext x
    constructor
    · intro hx
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
      cases b <;> simp_all
    · intro hx
      rcases hx with hx | hx
      · exact Set.mem_iUnion.mpr ⟨true, hx⟩
      · exact Set.mem_iUnion.mpr ⟨false, hx⟩
  have hout := properCycle_open_cover_cap_bijective X A (fun b : Bool => if b then P else Q)
    (P ∪ Q) hAo (fun b => by cases b <;> assumption) hcover p (q + 1) hp ψ.1
    (properCycle_relative_cochain_subcomplex_zero X A p φ) ψ.2 hup
  exact (properCycle_original_triad_cap_bijective_iff X A (P ∪ Q) p (q + 1) hp φ hφ).mp hout

/-- Real suspension bijectivity holds for the original relative cohomology cap, independently of the chosen cocycle representative.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, relative cap suspension.
HC no distance; AV milestone no distance. -/
lemma properCycle_original_real_cohomology_cap_suspension_bijective
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℕ) (hp : Even p) :
    let X := TopCat.of (ℝ × Y)
    let A : Set X := Prod.snd ⁻¹' Sᶜ
    let P : Set X := {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
    let Q : Set X := {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
    ∀ a : RelativeCohomology ℚ (TopPair.ofSubset (X := X) A) p,
      Function.Bijective (triadCapCohomologyLinear ℚ X A (P ∩ Q) p q a) →
      Function.Bijective (triadCapCohomologyLinear ℚ X A (P ∪ Q) p (q + 1) a) := by
  dsimp only
  intro a hc
  let X := TopCat.of (ℝ × Y)
  let A : Set X := Prod.snd ⁻¹' Sᶜ
  let P : Set X := {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
  let Q : Set X := {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
  let C := ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) A)).sc p
  obtain ⟨u, rfl⟩ := (relativeCochainCohomologyEquiv ℚ (TopPair.ofSubset (X := X) A) p).surjective a
  obtain ⟨φ, rfl⟩ := C.linearDual.moduleCatHomologyClass_surjective u
  erw [triadCapCohomologyLinear_on_cycle] at hc ⊢
  exact properCycle_original_real_cap_suspension_bijective Y S T hS hT p q hp
    (relativeCohomologyCycleToCocycle ℚ (TopPair.ofSubset (X := X) A) p φ).1
    (relativeCohomologyCycleToCocycle ℚ (TopPair.ofSubset (X := X) A) p φ).2 hc

end HodgeLean.Foundations.QuotientDuality
