import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian10
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.FlattenedSupport
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian8Defs
import HodgeLean.Adapters.CycleClassSmoothCharts

/-! # Local concentration and exclusion of critical hypersurface germs

Implications from analyticity and regular-point data, and from reduced analytic germs.
These primitives isolate local concentration and analytic codimension work.
The two full degree-two endpoints require further constructions.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology TopologicalSpace CategoryTheory CategoryTheory.Limits
  AlgebraicTopology.Singular
open AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Adapters

private theorem bh12_flattenedSupport_relativeCohomology_isZero_of_ne
    {M E : Type} [TopologicalSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℕ) (e : OpenPartialHomeomorph M (E × (Fin c → ℂ)))
    (x : M) (hx : x ∈ e.source) (S : Set M)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0) (h0 : (e x).2 = 0)
    (j : ℕ) (hj : j ≠ 2 * c) :
    IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair
        (flattenedSupportNeighborhood E c e x hx) S) j) := by
  apply relativeCohomology_isZero ℚ _ j
  exact (standardComplexLocalHomology_isZero_of_ne c j hj).of_iso
    (flattenedSupportRelativeHomologyIso E c e x hx S hS h0 j)

/-- A reduced equation's critical zero germ contains no irreducible hypersurface germ.
Source: `bh10_reduced_factor_derivative` and
`AnalyticDivisorAlgebraic18.spec_hypersurface_nullstellensatz`. -/
theorem bh12_no_critical_hypersurface_aux (n : ℕ) (p : Fin n → ℂ)
    (f g : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    (hred : Squarefree (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGermAt n p))
    (hi : IsIrreducibleAt g p) :
    ¬ ∀ᶠ z in 𝓝 p, g z = 0 → f z = 0 ∧ fderiv ℂ f z = 0 := by
  intro hcritical
  have hdivf :=
    HodgeLean.Foundations.AnalyticDivisorAlgebraic18.spec_hypersurface_nullstellensatz
      n p g f hg hf hi (hcritical.mono fun z hz hgz ↦ (hz hgz).1)
  obtain ⟨v, hv⟩ := bh10_reduced_factor_derivative n p f g hf hg hred hi hdivf
  apply hv
  apply HodgeLean.Foundations.AnalyticDivisorAlgebraic18.spec_hypersurface_nullstellensatz
      n p g (fun z ↦ fderiv ℂ f z v) hg
  · change AnalyticAt ℂ ((ContinuousLinearMap.apply ℂ ℂ v) ∘ fderiv ℂ f) p
    exact ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt (fderiv ℂ f p)).comp hf.fderiv
  · exact hi
  · exact hcritical.mono fun z hz hgz ↦ by
      simpa only [(hz hgz).2, zero_apply]

/-- Cofinal neighborhoods of regular-domain points have no supported classes below degree two.
Source: `bh10_equation_chart`, punctured complex-line local purity, and
`ccm5_relativeGerms_injective_of_lowerVanishing` for the subsequent detection step. -/
theorem bh12_regular_local_concentration_aux (n : ℕ) (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f univ) (p : Fin n → ℂ)
    (hp : p ∈ bh8_regularDomain n f) (V : Opens (Fin n → ℂ)) (hpV : p ∈ V) :
    ∃ W : Opens (Fin n → ℂ), p ∈ W ∧ W ≤ V ∧
      (W : Set (Fin n → ℂ)) ⊆ bh8_regularDomain n f ∧
      ∀ j : ℕ, j < 2 → Subsingleton (RelativeCohomology ℚ
        (neighborhoodSupportComplementPair (W : Set (Fin n → ℂ)) {z | f z = 0}) j) := by
  have hfc : Continuous f := hf.continuous
  have hdc : Continuous (fderiv ℂ f) := hf.fderiv.continuous
  let Of : Opens (Fin n → ℂ) :=
    ⟨{z | f z ≠ 0}, hfc.isOpen_preimage _ isOpen_compl_singleton⟩
  by_cases hp0 : f p = 0
  · have hdp : fderiv ℂ f p ≠ 0 := hp.elim (fun h ↦ (h hp0).elim) id
    cases n with
    | zero =>
        exfalso
        apply hdp
        ext v
        have hv : v = 0 := Subsingleton.elim _ _
        subst v
        exact map_zero _
    | succ k =>
        obtain ⟨e, hpe, _he, _hei, heq⟩ :=
          bh10_equation_chart k p f (hf p (by simp)) hp0 hdp
        let Od : Opens (Fin (k + 1) → ℂ) :=
          ⟨{z | fderiv ℂ f z ≠ 0}, hdc.isOpen_preimage _ isOpen_compl_singleton⟩
        let D : Opens (Fin (k + 1) → ℂ) := V ⊓ Od
        let e' := e.restrOpen (D : Set (Fin (k + 1) → ℂ)) D.isOpen
        have hpe' : p ∈ e'.source := ⟨hpe, hpV, hdp⟩
        have hsupport : ∀ y ∈ e'.source, y ∈ {z | f z = 0} ↔ (e' y).2 = 0 := by
          intro y hy
          have hy' : y ∈ e.source := hy.1
          change f y = 0 ↔ (e y).2 = 0
          constructor
          · intro hfy
            ext i
            change (e y).2 i = (0 : ℂ)
            rw [Subsingleton.elim i 0, heq y hy', hfy]
          · intro hzero
            exact (heq y hy').symm.trans (congrFun hzero 0)
        have hnormal : (e' p).2 = 0 := by
          change (e p).2 = 0
          ext i
          change (e p).2 i = (0 : ℂ)
          rw [Subsingleton.elim i 0, heq p hpe, hp0]
        let W : Opens (Fin (k + 1) → ℂ) :=
          flattenedSupportNeighborhood (Fin k → ℂ) 1 e' p hpe'
        refine ⟨W, mem_flattenedSupportNeighborhood _ _ _ _ _, ?_, ?_, ?_⟩
        · intro y hy
          exact (flattenedSupportNeighborhood_subset_source _ _ _ _ _ hy).2.1
        · intro y hy
          exact Or.inr (flattenedSupportNeighborhood_subset_source _ _ _ _ _ hy).2.2
        · intro j hj
          exact ModuleCat.subsingleton_of_isZero
            (bh12_flattenedSupport_relativeCohomology_isZero_of_ne 1 e' p hpe'
              {z | f z = 0} hsupport hnormal j (by omega))
  · let W : Opens (Fin n → ℂ) := V ⊓ Of
    refine ⟨W, ⟨hpV, hp0⟩, inf_le_left, ?_, ?_⟩
    · intro z hz
      exact Or.inl hz.2
    · intro j _hj
      exact neighborhoodSupportRelativeCohomology_subsingleton
        (TopCat.of (Fin n → ℂ)) {z | f z = 0} j W (fun _ hz ↦ hz.2)

/-- On an open part of the regular domain, degree-two supported classes are detected by germs.
Source: `bh12_regular_local_concentration_aux` and
`ccm5_relativeGerms_injective_of_lowerVanishing`. -/
theorem bh12_regular_germs_injective_aux (n : ℕ) (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f univ) (U : Opens (Fin n → ℂ))
    (hU : (U : Set (Fin n → ℂ)) ⊆ bh8_regularDomain n f) :
    Function.Injective (fun z : RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (U : Set (Fin n → ℂ)) {p | f p = 0}) 2 =>
      fun a : U => supportRelativeCohomologyGerm (TopCat.of (Fin n → ℂ))
        {p | f p = 0} 2 U a.1 a.2 z) := by
  classical
  let T := TopCat.of (Fin n → ℂ)
  let S : Closeds T := ⟨{p | f p = 0}, isClosed_eq hf.continuous continuous_const⟩
  let K := supportedRationalSingularCochainComplex T S.compl
  letI : ∀ V : Opens T, ParacompactSpace V := fun _ => inferInstance
  apply ccm5_relativeGerms_injective_of_lowerVanishing T S U 2
  intro j hj
  have hK : CategoryTheory.Limits.IsZero
      ((((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex
        ℤᵘᵖ).obj K).homology (j : ℤ)) := by
    apply TopCat.Sheaf.openRestriction_homology_isZero_of_cofinal_sections
    intro p hp V hpV
    obtain ⟨W, hpW, hWV, _, hW⟩ :=
      bh12_regular_local_concentration_aux n f hf p (hU hp) V hpV
    refine ⟨W, hWV, hpW, ?_⟩
    letI := hW j hj
    let e := supportedRationalSingularSectionCohomologyEquivSupportComplement
      T S S.isClosed W j
    have hs := e.injective.subsingleton
    exact @AddCommGrpCat.isZero_of_subsingleton _ hs
  exact CategoryTheory.Limits.IsZero.of_iso hK
    ((K.sc (j : ℤ)).mapHomologyIso
      (U.isOpenEmbedding.sheafPullback AddCommGrpCat) ≪≫
    (U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapIso
      (supportedSingularCohomologySheafIsoRelative T S S.isClosed j)).symm

end HodgeLean.Adapters
