import HodgeLean.Adapters.IntersectionProductCCGerms
import HodgeLean.Adapters.IntersectionProductCCDiag

/-! # Normal evaluations for the local intersection comparison -/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs

namespace HodgeLean.Adapters

/-- Evaluation on the normal generator determines a class on a flattened neighborhood.
Source: the universal coefficient isomorphism and
`span_flattenedSupportNormalClass_eq_top`. -/
theorem a3cc2_flattened_eq_of_normalEvaluation
    {M : Type} [TopologicalSpace M] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℕ) (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (S : Set M)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (b : M) (hb : b ∈ e.source) (hb0 : (e b).2 = 0)
    (α β : RelativeCohomology ℚ (neighborhoodSupportComplementPair
      (flattenedSupportNeighborhood E c e b hb : Set M) S) (2 * c))
    (h : relativeCohomologyEquivDualHomology ℚ _ (2 * c) α
        (flattenedSupportNormalClass E c e b hb S hS hb0) =
      relativeCohomologyEquivDualHomology ℚ _ (2 * c) β
        (flattenedSupportNormalClass E c e b hb S hS hb0)) : α = β := by
  apply (relativeCohomologyEquivDualHomology ℚ _ (2 * c)).injective
  apply LinearMap.ext
  intro w
  have hw : w ∈ Submodule.span ℚ
      {flattenedSupportNormalClass E c e b hb S hS hb0} := by
    rw [span_flattenedSupportNormalClass_eq_top E c e S hS b hb hb0]
    trivial
  obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [map_smul, map_smul, h]

#print axioms a3cc2_flattened_eq_of_normalEvaluation

/-- An isolated smooth intersection component has a chart flattening the entire intersection.
Source: component flattening and `ccm5_finiteSupport_local_eq`. -/
theorem a3cc2_intersection_flatteningChart (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r : ℕ) (x y : X.left)
    (w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme)
    (hw : closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
      irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme)
    (hwcodim : Order.coheight
      ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) = r)
    (a : ComplexPoint X)
    (ha : a ∈ cycleComponentAnalyticClosedSupport X
      ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w))
    (hother : ∀ w' : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
      closure ({w'} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme →
      w' ≠ w → a ∉ cycleComponentAnalyticClosedSupport X
        ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w'))
    (hsing : a ∉ cycleComponentSingularAnalyticClosedFiltration X
      ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) 0) :
    ∃ e : OpenPartialHomeomorph (ComplexPoint X)
        ((Fin (dim X.left - r) → ℂ) × (Fin r → ℂ)),
      (∀ b ∈ e.source, b ∈ (cycleComponentAnalyticClosedSupport X x ⊓
        cycleComponentAnalyticClosedSupport X y : Closeds (ComplexPoint X)) ↔
        (e b).2 = 0) ∧ a ∈ e.source := by
  classical
  let I := {v : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme //
    closure ({v} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
      irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme}
  let : Fintype I := (hc9k_components_finite X x y).fintype
  obtain ⟨e, he, hae⟩ := hc9k_component_flatteningChart X r _ hwcodim a hsing ha
  obtain ⟨W, _, haW, hW⟩ := ccm5_finiteSupport_local_eq
    (fun c : I => cycleComponentAnalyticClosedSupport X
      ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι c.1))
    (⟨w, hw⟩ : I) a
    (fun c hc => hother c.1 c.2 (fun h => hc (Subtype.ext h)))
    ⟨e.source, e.open_source⟩ hae
  refine ⟨e.restrOpen (W : Set (ComplexPoint X)) W.isOpen, ?_, ⟨hae, haW⟩⟩
  intro b hb
  have hlocal : b ∈ (cycleComponentAnalyticClosedSupport X x ⊓
      cycleComponentAnalyticClosedSupport X y : Closeds (ComplexPoint X)) ↔
      b ∈ cycleComponentAnalyticClosedSupport X
        ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) := by
    rw [hc9k_support_inf_eq_iSup X x y]
    exact hW b hb.2
  exact hlocal.trans (he b hb.1)

#print axioms a3cc2_intersection_flatteningChart

/-- Evaluation of a supported class on the normal homology generator of a flattened chart.
Source: the relative universal coefficient pairing and the normal class of a support chart. -/
def a3cc2_normalEvaluation (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (c : ℕ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin c → ℂ)))
    (hS : ∀ b ∈ e.source, b ∈ S ↔ (e b).2 = 0)
    (a : ComplexPoint X) (ha : a ∈ e.source) (ha0 : (e a).2 = 0)
    (u : H_[S]^(2 * c)(X; ℚ)) : ℚ :=
  relativeCohomologyEquivDualHomology ℚ
    (neighborhoodSupportComplementPair
      (flattenedSupportNeighborhood E c e a ha : Set (ComplexPoint X)) S) (2 * c)
    (relativeCohomologyMap ℚ (2 * c)
      (neighborhoodSupportInclusionPairMap
        (show (flattenedSupportNeighborhood E c e a ha : Set (ComplexPoint X)) ⊆
          (⊤ : Opens (ComplexPoint X)) from le_top) (S : Set (ComplexPoint X)))
      (supportedSingularClass X S (2 * c) u))
    (flattenedSupportNormalClass E c e a ha S hS ha0)

/-- Equality of normal evaluations gives equality of the supported germs at the chart center.
Source: `a3cc2_flattened_eq_of_normalEvaluation` and restriction of germs. -/
theorem a3cc2_supportGerm_eq_of_normalEvaluation (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (c : ℕ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin c → ℂ)))
    (hS : ∀ b ∈ e.source, b ∈ S ↔ (e b).2 = 0)
    (a : ComplexPoint X) (ha : a ∈ e.source) (ha0 : (e a).2 = 0)
    (u v : H_[S]^(2 * c)(X; ℚ))
    (h : a3cc2_normalEvaluation X S c e hS a ha ha0 u =
      a3cc2_normalEvaluation X S c e hS a ha ha0 v) :
    ccm5_supportGerm X S (2 * c) a u = ccm5_supportGerm X S (2 * c) a v := by
  have hclass := a3cc2_flattened_eq_of_normalEvaluation c e (S : Set (ComplexPoint X))
    hS a ha ha0 _ _ h
  have hg := congrArg (supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
    (S : Set (ComplexPoint X)) (2 * c) (flattenedSupportNeighborhood E c e a ha)
    a (mem_flattenedSupportNeighborhood E c e a ha)) hclass
  simpa only [ccm5_supportGerm_restriction] using hg

#print axioms a3cc2_normalEvaluation
#print axioms a3cc2_supportGerm_eq_of_normalEvaluation

/-- Normal evaluation respects integer multiplicities.
Source: additivity of restriction and of the relative cohomology pairing. -/
theorem a3cc2_normalEvaluation_zsmul (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (c : ℕ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin c → ℂ)))
    (hS : ∀ b ∈ e.source, b ∈ S ↔ (e b).2 = 0)
    (a : ComplexPoint X) (ha : a ∈ e.source) (ha0 : (e a).2 = 0)
    (m : ℤ) (u : H_[S]^(2 * c)(X; ℚ)) :
    a3cc2_normalEvaluation X S c e hS a ha ha0 (m • u) =
      m • a3cc2_normalEvaluation X S c e hS a ha ha0 u := by
  simp only [a3cc2_normalEvaluation, map_zsmul]
  rfl

#print axioms a3cc2_normalEvaluation_zsmul

/-- Normal evaluation is the ambient comparison paired with the included normal class.
Source: naturality of the relative universal coefficient pairing. -/
theorem a3cc2_normalEvaluation_comparison (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (c : ℕ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin c → ℂ)))
    (hS : ∀ b ∈ e.source, b ∈ S ↔ (e b).2 = 0)
    (a : ComplexPoint X) (ha : a ∈ e.source) (ha0 : (e a).2 = 0)
    (u : H_[S]^(2 * c)(X; ℚ)) :
    a3cc2_normalEvaluation X S c e hS a ha ha0 u =
      relativeCohomologyEquivDualHomology ℚ
        (TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
          (S : Set (ComplexPoint X))ᶜ) (2 * c)
        (ccm16_supportedComparison X S (2 * c) u)
        (relativeHomologyMap ℚ (2 * c)
          (ccm17_preimagePair (TopCat.of (flattenedSupportNeighborhood E c e a ha))
            (TopCat.of (ComplexPoint X)) ⟨Subtype.val, continuous_subtype_val⟩ S)
          (flattenedSupportNormalClass E c e a ha S hS ha0)) := by
  unfold a3cc2_normalEvaluation
  rw [← hc9k_supportedComparison_restrict]
  exact relativeCohomologyEquivDualHomology_relativeCohomologyMap ℚ (2 * c) _ _ _

#print axioms a3cc2_normalEvaluation_comparison

/-- Pairing the supported cup is pairing the exterior product with the diagonal image.
Source: the diagonal cup formula and naturality of the relative pairing. -/
theorem a3cc2_supportedCup_diagonal_pairing (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S T : Closeds (ComplexPoint X)) (p q : ℕ)
    (u : H_[S]^p(X; ℚ)) (v : H_[T]^q(X; ℚ))
    (z : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
      ((S ⊓ T : Closeds (ComplexPoint X)) : Set (ComplexPoint X))ᶜ) (p + q)) :
    relativeCohomologyEquivDualHomology ℚ
      (TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
        ((S ⊓ T : Closeds (ComplexPoint X)) : Set (ComplexPoint X))ᶜ) (p + q)
      (ccm16_supportedComparison X (S ⊓ T) (p + q)
        (ccm16_supportedCup X S T p q u v)) z =
      relativeCohomologyEquivDualHomology ℚ _ (p + q)
        (a3cc2_relativeExternal (TopCat.of (ComplexPoint X)) S T p q
          (ccm16_supportedComparison X S p u) (ccm16_supportedComparison X T q v))
        (relativeHomologyMap ℚ (p + q)
          (a3cc2_diagonalPair (TopCat.of (ComplexPoint X)) S T) z) := by
  rw [a3cc2_supportedCup_diagonal]
  exact relativeCohomologyEquivDualHomology_relativeCohomologyMap ℚ (p + q) _ _ _

#print axioms a3cc2_supportedCup_diagonal_pairing

/-- On a flattened neighborhood, equality at one supported germ determines the relative class.
Source: `hc9k_flattened_restrict_eq_zero_of_germ` applied to the difference. -/
theorem a3cc2_flattened_eq_of_germ
    {M : Type} [TopologicalSpace M] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℕ) (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (S : Set M)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (b : M) (hb : b ∈ e.source) (hb0 : (e b).2 = 0)
    (α β : RelativeCohomology ℚ (neighborhoodSupportComplementPair
      (flattenedSupportNeighborhood E c e b hb : Set M) S) (2 * c))
    (z : M) (hz : z ∈ flattenedSupportNeighborhood E c e b hb) (hzS : z ∈ S)
    (h : supportRelativeCohomologyGerm (TopCat.of M) S (2 * c)
        (flattenedSupportNeighborhood E c e b hb) z hz α =
      supportRelativeCohomologyGerm (TopCat.of M) S (2 * c)
        (flattenedSupportNeighborhood E c e b hb) z hz β) : α = β := by
  apply sub_eq_zero.mp
  apply hc9k_flattened_restrict_eq_zero_of_germ c e S hS b hb hb0 (α - β) z hz hzS
  simpa only [supportRelativeCohomologyGerm, map_sub, sub_eq_zero] using h

#print axioms a3cc2_flattened_eq_of_germ

/-- A germ identity at any support point of the flattened neighborhood determines evaluation.
Source: `a3cc2_flattened_eq_of_germ` and restriction of supported germs. -/
theorem a3cc2_normalEvaluation_eq_of_supportGerm (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (c : ℕ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin c → ℂ)))
    (hS : ∀ b ∈ e.source, b ∈ S ↔ (e b).2 = 0)
    (a : ComplexPoint X) (ha : a ∈ e.source) (ha0 : (e a).2 = 0)
    (u v : H_[S]^(2 * c)(X; ℚ))
    (z : ComplexPoint X) (hz : z ∈ flattenedSupportNeighborhood E c e a ha)
    (hzS : z ∈ S)
    (h : ccm5_supportGerm X S (2 * c) z u = ccm5_supportGerm X S (2 * c) z v) :
    a3cc2_normalEvaluation X S c e hS a ha ha0 u =
      a3cc2_normalEvaluation X S c e hS a ha ha0 v := by
  unfold a3cc2_normalEvaluation
  apply congrArg (fun α => relativeCohomologyEquivDualHomology ℚ
    (neighborhoodSupportComplementPair
      (flattenedSupportNeighborhood E c e a ha : Set (ComplexPoint X)) S) (2 * c) α
    (flattenedSupportNormalClass E c e a ha S hS ha0))
  apply a3cc2_flattened_eq_of_germ c e (S : Set (ComplexPoint X)) hS a ha ha0 _ _ z hz hzS
  simpa only [ccm5_supportGerm_restriction] using h

#print axioms a3cc2_normalEvaluation_eq_of_supportGerm

end HodgeLean.Adapters
