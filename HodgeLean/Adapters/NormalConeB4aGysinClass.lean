import HodgeLean.Adapters.NormalConeB4aClassExistsPure
import HodgeLean.Adapters.NormalConeB4aClassUniqueBoundary
import HodgeLean.Adapters.NormalConeB4aGysinSupport

/-! # A fixed fundamental class for the hypersurface calculation

Existence selects a normalized class. Uniqueness identifies any normalized input
with that selection before the local intersection calculation.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry AlgebraicTopology.Singular

/-- The ambient space of a smooth family over the affine line is smooth over the field. -/
theorem a3b4a_gysin_ambient_smooth {Z : Scheme.{0}}
    {q : Z ⟶ Spec (CommRingCat.of ℂ)} (h : Z ⟶ a3b2_line ℂ) [Smooth h]
    (hq : h ≫ a3b2_lineToBase ℂ = q) : Smooth q := by
  have : Smooth (a3b2_lineToBase ℂ) := by
    rw [a3b2_lineToBase, HasRingHomProperty.Spec_iff (P := @Smooth)]
    change (algebraMap ℂ (Polynomial ℂ)).Smooth
    rw [RingHom.smooth_algebraMap]
    exact ⟨inferInstance, inferInstance⟩
  rw [← hq]
  infer_instance

/-- A selected normalized fundamental class with the original generic-length coefficients.
Source: `a3b4a_cycleClass_exists_of_codimension`. -/
def a3b4a_gysin_fundamentalClass {Z K : Scheme.{0}}
    (q : Z ⟶ Spec (CommRingCat.of ℂ)) [IsNoetherian Z] [Smooth q]
    [QuasiCompact q] [IsSeparated q] (i : K ⟶ Z) (c : ℕ)
    (hc : ∀ ξ ∈ (a3b3_imageCycle i inferInstance).support, (c : ℕ∞) ≤ Order.coheight ξ) :
    RelativeCohomology ℚ (TopPair.ofSubset (X := a3b4_an q)
      (a3b4_cycleSupport q (a3b3_imageCycle i inferInstance))ᶜ) (2 * c) :=
  (a3b4a_cycleClass_exists_of_codimension q (a3b3_imageCycle i inferInstance) c hc).choose

/-- The selected class satisfies the original chart normalization. -/
theorem a3b4a_gysin_fundamentalClass_normalized {Z K : Scheme.{0}}
    (q : Z ⟶ Spec (CommRingCat.of ℂ)) [IsNoetherian Z] [Smooth q]
    [QuasiCompact q] [IsSeparated q] (i : K ⟶ Z) (c : ℕ)
    (hc : ∀ ξ ∈ (a3b3_imageCycle i inferInstance).support, (c : ℕ∞) ≤ Order.coheight ξ) :
    a3b4_IsCycleClass q (a3b3_imageCycle i inferInstance) c
      (a3b4a_gysin_fundamentalClass q i c hc) :=
  (a3b4a_cycleClass_exists_of_codimension q (a3b3_imageCycle i inferInstance) c hc).choose_spec

/-- The selected class is a normalized class of the image cycle of `i`. -/
example {Z K : Scheme.{0}}
    (q : Z ⟶ Spec (CommRingCat.of ℂ)) [IsNoetherian Z] [Smooth q]
    [QuasiCompact q] [IsSeparated q] (i : K ⟶ Z) (c : ℕ)
    (hc : ∀ ξ ∈ (a3b3_imageCycle i inferInstance).support, (c : ℕ∞) ≤ Order.coheight ξ) :
    a3b4_IsCycleClass q (a3b3_imageCycle i inferInstance) c
      (a3b4a_gysin_fundamentalClass q i c hc) :=
  a3b4a_gysin_fundamentalClass_normalized q i c hc

/-- Normalization identifies an input class with the selected fundamental class. -/
theorem a3b4a_gysin_eq_fundamentalClass {Z K : Scheme.{0}}
    (q : Z ⟶ Spec (CommRingCat.of ℂ)) [IsNoetherian Z] [Smooth q]
    [QuasiCompact q] [IsSeparated q] (i : K ⟶ Z) (c : ℕ)
    (hc : ∀ ξ ∈ (a3b3_imageCycle i inferInstance).support, (c : ℕ∞) ≤ Order.coheight ξ)
    (β : RelativeCohomology ℚ (TopPair.ofSubset (X := a3b4_an q)
      (a3b4_cycleSupport q (a3b3_imageCycle i inferInstance))ᶜ) (2 * c))
    (hβ : a3b4_IsCycleClass q (a3b3_imageCycle i inferInstance) c β) :
    β = a3b4a_gysin_fundamentalClass q i c hc := by
  let γ := a3b3_imageCycle i inferInstance
  exact a3b4a_cycleClass_unique_of_regularBoundary q γ c hc
    (a3b4a_classRegularBoundary q γ c) (a3b4a_classRegularBoundary_le q γ c)
    (a3b4a_classRegularBoundary_coheight q γ c hc)
    (a3b4a_classRegularBoundary_charts q γ c hc) β _ hβ
    (a3b4a_gysin_fundamentalClass_normalized q i c hc)

end HodgeLean.Adapters
