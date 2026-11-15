import HodgeLean.Adapters.NormalConeB4aDefs
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.LocalHomologyVanishing

/-! # Local ingredients for analytic cycle classes

Proof decomposition:
* `a3b4a_classLocal_vanishing_below_codimension` computes the chart model by
  radial compression and the punctured complex vector space calculation.
* Global support vanishing requires a finite smooth stratification and support
  localization, retaining the algebraic codimension bound on each stratum.
* Existence requires gluing the complex normal coclasses on the regular strata,
  then extension over the strata of larger codimension.
* Uniqueness requires restriction injectivity across those strata and detection
  of degree `2 * c` classes by their local normal coclasses.

The local computations here do not require a projective ambient scheme.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry AlgebraicTopology.Singular

/-- Relative cohomology on a flattening neighborhood vanishes below twice the
normal codimension. The comparison uses the explicit radial pair isomorphism.
Source: `flattenedSupportRelativeHomologyIso` and
`AlgebraicTopology.Singular.standardComplexLocalHomology_isZero_of_ne`. -/
theorem a3b4a_classLocal_vanishing_below_codimension
    {M : Type} [TopologicalSpace M] {r c : ℕ}
    (e : OpenPartialHomeomorph M ((Fin r → ℂ) × (Fin c → ℂ)))
    (S : Set M) (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (x : M) (hx : x ∈ e.source) (hxS : x ∈ S)
    (n : ℕ) (hn : n < 2 * c) :
    IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair
        (flattenedSupportNeighborhood (Fin r → ℂ) c e x hx) S) n) := by
  apply relativeCohomology_isZero
  exact (standardComplexLocalHomology_isZero_of_ne c n (ne_of_lt hn)).of_iso
    (flattenedSupportRelativeHomologyIso (Fin r → ℂ) c e x hx S hS
      ((hS x hx).mp hxS) n)

/-- The lower-degree vanishing neighborhoods can be chosen inside any prescribed
open neighborhood, by restricting the flattening chart before radial compression. -/
theorem a3b4a_classLocal_vanishing_basis
    {M : Type} [TopologicalSpace M] {r c : ℕ}
    (e : OpenPartialHomeomorph M ((Fin r → ℂ) × (Fin c → ℂ)))
    (S : Set M) (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (x : M) (hx : x ∈ e.source) (hxS : x ∈ S)
    (U : Set M) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ W ⊆ e.source ∧
      ∀ n : ℕ, n < 2 * c →
        IsZero (RelativeCohomology ℚ (neighborhoodSupportComplementPair W S) n) := by
  let e' := e.restrOpen U hU
  have hx' : x ∈ e'.source := ⟨hx, hxU⟩
  have hS' : ∀ y ∈ e'.source, y ∈ S ↔ (e' y).2 = 0 :=
    fun y hy => hS y hy.1
  let W := flattenedSupportNeighborhood (Fin r → ℂ) c e' x hx'
  have hW := flattenedSupportNeighborhood_subset_source (Fin r → ℂ) c e' x hx'
  exact ⟨W, W.isOpen, mem_flattenedSupportNeighborhood (Fin r → ℂ) c e' x hx',
    fun _ hy => (hW hy).2, fun _ hy => (hW hy).1,
    fun n hn => a3b4a_classLocal_vanishing_below_codimension e' S hS' x hx' hxS n hn⟩

end HodgeLean.Adapters
