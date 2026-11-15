import HodgeLean.Foundations.QuotientDuality.ProperCycleChecks

/-! # Detection of normalized supported classes on component charts -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program HodgeLean.RealDefs
namespace HodgeLean.Foundations.QuotientDuality

lemma properCycle_normalized_ne_zero
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (k r : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)))
    (hS : ∀ z ∈ e.source, z ∈ a3b4_cycleSupport X.hom γ ↔ (e z).2 = 0)
    (he : a3b4_IsHolChart X.hom e)
    (z : ComplexPoint X) (hz : z ∈ e.source)
    (hzS : z ∈ a3b4_cycleSupport X.hom γ)
    (hm : a3b4_multiplicity X.hom γ z ≠ 0)
    (a : s2e_supportedClass X γ k)
    (ha : a3b4_IsCycleClass X.hom γ k a) : a ≠ 0 := by
  intro hzero
  obtain ⟨W, hW, hWo, hzW, hnorm⟩ := ha r e hS z hz hzS he
  rw [hzero, map_zero] at hnorm
  have hn := chartNormalProjectionCoclass_ne_zero (Fin r → ℂ) k
    e (a3b4_cycleSupport X.hom γ) hS hWo hW hzW ((hS z hz).mp hzS)
  exact (smul_ne_zero hm hn) hnorm.symm

lemma properCycle_normalized_ne_zero_of_component
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (k r : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)))
    (hS : ∀ z ∈ e.source, z ∈ a3b4_cycleSupport X.hom γ ↔ (e z).2 = 0)
    (he : a3b4_IsHolChart X.hom e)
    (ξ : X.left) (hξ : ξ ∈ γ.support)
    (z : ComplexPoint X) (hz : z ∈ e.source)
    (hzξ : Point.underlying z ∈ closure {ξ})
    (hother : ∀ ζ ∈ γ.support, Point.underlying z ∈ closure {ζ} → ζ = ξ)
    (a : s2e_supportedClass X γ k)
    (ha : a3b4_IsCycleClass X.hom γ k a) : a ≠ 0 := by
  have hzS : z ∈ a3b4_cycleSupport X.hom γ :=
    Set.mem_iUnion₂.mpr ⟨ξ, hξ, hzξ⟩
  apply properCycle_normalized_ne_zero X γ k r e hS he z hz hzS _ a ha
  rw [a3b4a_classMultiplicity_eq_component X.hom γ ξ hξ z hzξ
    (fun ζ hζ hne hzζ => hne (hother ζ hζ hzζ))]
  exact hξ

lemma properCycle_normalized_smul_eq_one
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (k r : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)))
    (hS : ∀ z ∈ e.source, z ∈ a3b4_cycleSupport X.hom γ ↔ (e z).2 = 0)
    (he : a3b4_IsHolChart X.hom e)
    (z : ComplexPoint X) (hz : z ∈ e.source)
    (hzS : z ∈ a3b4_cycleSupport X.hom γ)
    (hm : a3b4_multiplicity X.hom γ z ≠ 0)
    (a : s2e_supportedClass X γ k)
    (ha : a3b4_IsCycleClass X.hom γ k a) (q : ℚ)
    (hqa : a3b4_IsCycleClass X.hom γ k (q • a)) : q = 1 := by
  obtain ⟨V, hV, hVo, hzV, hnorm⟩ := ha r e hS z hz hzS he
  obtain ⟨V', hV', hV'o, hzV', hnorm'⟩ := hqa r e hS z hz hzS he
  have hA := a3b4a_classLocal_normalization_mono e _ hS
    (Set.inter_subset_left : V ∩ V' ⊆ V) hV a _ hnorm
  have hQA := a3b4a_classLocal_normalization_mono e _ hS
    (Set.inter_subset_right : V ∩ V' ⊆ V') hV' (q • a) _ hnorm'
  rw [map_smul, hA] at hQA
  have hn := chartNormalProjectionCoclass_ne_zero (Fin r → ℂ) k
    e (a3b4_cycleSupport X.hom γ) hS (hVo.inter hV'o)
    (Set.inter_subset_left.trans hV) ⟨hzV, hzV'⟩ ((hS z hz).mp hzS)
  exact smul_left_injective ℚ (smul_ne_zero hm hn)
    (hQA.trans (one_smul ℚ _).symm)

lemma properCycle_normalized_unique_of_generator
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (k r : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)))
    (hS : ∀ z ∈ e.source, z ∈ a3b4_cycleSupport X.hom γ ↔ (e z).2 = 0)
    (he : a3b4_IsHolChart X.hom e)
    (z : ComplexPoint X) (hz : z ∈ e.source)
    (hzS : z ∈ a3b4_cycleSupport X.hom γ)
    (hm : a3b4_multiplicity X.hom γ z ≠ 0)
    (a : s2e_supportedClass X γ k)
    (ha : a3b4_IsCycleClass X.hom γ k a)
    (hgen : Function.Bijective (LinearMap.toSpanSingleton ℚ (s2e_supportedClass X γ k) a)) :
    ∃! b : s2e_supportedClass X γ k, a3b4_IsCycleClass X.hom γ k b := by
  refine ⟨a, ha, ?_⟩
  intro b hb
  obtain ⟨q, hq⟩ := hgen.2 b
  have hqb : q • a = b := hq
  have hqa : a3b4_IsCycleClass X.hom γ k (q • a) := hqb.symm ▸ hb
  have hqone := properCycle_normalized_smul_eq_one X γ k r e hS he z hz hzS hm a ha q hqa
  rw [← hqb, hqone, one_smul]

lemma properCycle_zero_normalized
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (k : ℕ) :
    a3b4_IsCycleClass X.hom (0 : AlgebraicCycle X.left ℚ) k
      (0 : s2e_supportedClass X 0 k) := by
  intro r e hS z hz hzS
  simp [a3b4_cycleSupport] at hzS

lemma properCycle_zero_normalization_detects_cycle
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (γ : AlgebraicCycle X.left ℚ) (k : ℕ)
    (hcharts : ∀ ξ ∈ γ.support, ∃ (r : ℕ)
      (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)))
      (hS : ∀ z ∈ e.source, z ∈ a3b4_cycleSupport X.hom γ ↔ (e z).2 = 0),
      a3b4_IsHolChart X.hom e ∧ ∃ z : ComplexPoint X,
        z ∈ e.source ∧ z ∈ a3b4_cycleSupport X.hom γ ∧
        Point.underlying z ∈ closure {ξ} ∧
        ∀ ζ ∈ γ.support, Point.underlying z ∈ closure {ζ} → ζ = ξ)
    (ha : a3b4_IsCycleClass X.hom γ k (0 : s2e_supportedClass X γ k)) : γ = 0 := by
  classical
  ext ξ
  by_contra hξ
  have hmem : ξ ∈ γ.support := hξ
  obtain ⟨r, e, hS, he, z, hz, hzS, hzξ, hother⟩ := hcharts ξ hmem
  exact (properCycle_normalized_ne_zero_of_component X γ k r e hS he
    ξ hmem z hz hzξ hother 0 ha) rfl

lemma properCycle_empty_support_subsingleton (X : TopCat.{0}) (n : ℕ) :
    Subsingleton (CohomologyWithSupport ℚ X ∅ n) := by
  change Subsingleton (RelativeCohomology ℚ (TopPair.ofSubset (X := X) (∅ : Set X)ᶜ) n)
  rw [Set.compl_empty]
  let P := TopPair.ofSubset (X := X) (Set.univ : Set X)
  have hPi : IsIso P.map :=
    (TopCat.isIso_iff_isHomeomorph P.map).mpr (Homeomorph.Set.univ X).isHomeomorph
  have hchain : IsIso ((chainPairFunctor ℚ).obj P).hom := by
    change IsIso (((AlgebraicTopology.singularChainComplexFunctor.{0} (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map P.map)
    infer_instance
  have hK : CategoryTheory.Limits.IsZero ((relativeChainFunctor ℚ).obj P) :=
    CategoryTheory.Limits.isZero_cokernel_of_epi ((chainPairFunctor ℚ).obj P).hom
  have hh : CategoryTheory.Limits.IsZero (RelativeHomology ℚ P n) :=
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n).map_isZero hK
  exact relativeCohomology_subsingleton ℚ P n (ModuleCat.subsingleton_of_isZero hh)

lemma properCycle_zero_supported_eq_zero
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (k : ℕ)
    (a : s2e_supportedClass X (0 : AlgebraicCycle X.left ℚ) k) : a = 0 := by
  have hS : a3b4_cycleSupport X.hom (0 : AlgebraicCycle X.left ℚ) = ∅ := by
    ext z
    simp [a3b4_cycleSupport]
  have hsub : Subsingleton (s2e_supportedClass X (0 : AlgebraicCycle X.left ℚ) k) := by
    change Subsingleton (CohomologyWithSupport ℚ (a3b4_an X.hom)
      (a3b4_cycleSupport X.hom (0 : AlgebraicCycle X.left ℚ)) (2 * k))
    rw [hS]
    exact properCycle_empty_support_subsingleton _ _
  exact hsub.elim a 0

end HodgeLean.Foundations.QuotientDuality
