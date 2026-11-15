import HodgeLean.Foundations.Curves.SymmetricCharts.Defs
import HodgeLean.Foundations.Program.SchoenCycleC2FiniteDimensionHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2PowerDimensionHelpers

/-! # Symmetric chart obligations

Product charts and descent retain the existing invariant-spectrum construction.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
open HodgeLean.Foundations.Curves.Picard.Families
namespace HodgeLean.Foundations.Curves.SymmetricCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
variable (C : Over (Spec ↧ℂ)) [IsIntegral C.left] [Smooth C.hom]
  [IsProjective C.hom] (n : ℕ)

private instance powerIntegral : IsIntegral (g3_power C n).left := by
  letI := HodgeLean.Foundations.spec_g3b_geometricallyIntegral C
  infer_instance

private instance powerDiagonal :
    IsAffineHom (pullback.diagonal (terminal.from (g3_power C n).left)) := by
  haveI : IsSeparated (terminal.from (g3_power C n).left) := by
    rw [← terminal.comp_from (g3_power C n).hom]
    infer_instance
  infer_instance

private theorem chartCover : ∀ x : (g3_power C n).left,
    ∃ W : Index C n, x ∈ W.val :=
  s2_projective_invariantAffineIndex_cover ℂ _ (g3_power C n).hom _ (action C n)

private theorem affineProductOpen {X Y S : Scheme.{0}} [IsAffine S]
    (f : X ⟶ S) (g : Y ⟶ S) (U : X.Opens) (V : Y.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by
  letI : IsAffine U.toScheme := hU
  letI : IsAffine V.toScheme := hV
  let p := pullback.map (U.ι ≫ f) (V.ι ≫ g) f g U.ι V.ι (𝟙 S)
    (by simp only [Category.comp_id]) (by simp only [Category.comp_id])
  have he : p.opensRange = pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V := by
    apply TopologicalSpace.Opens.ext
    change Set.range p = _
    rw [Scheme.Pullback.range_map]
    simp only [Scheme.Opens.range_ι]
    rfl
  rw [← he]
  exact isAffineOpen_opensRange p

private theorem productOpenAffine (U : C.left.Opens) (hU : IsAffineOpen U) :
    ∀ n, IsAffineOpen (productOpen C n U) := by
  intro n
  induction n with
  | zero =>
    simpa only [productOpen, iInf_of_empty] using isAffineOpen_top (Spec ↧ℂ)
  | succ n ih =>
    have he : productOpen C (n + 1) U =
        pullback.fst C.hom (g3_power C n).hom ⁻¹ᵁ U ⊓
        pullback.snd C.hom (g3_power C n).hom ⁻¹ᵁ productOpen C n U := by
      apply TopologicalSpace.Opens.ext
      ext x
      simp only [productOpen, TopologicalSpace.Opens.coe_iInf,
        TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, Set.mem_iInter,
        Scheme.Hom.coe_preimage, Set.mem_preimage]
      change (∀ i : Fin (n + 1), (g3_proj C (n + 1) i).left x ∈ U) ↔
        (pullback.fst C.hom (g3_power C n).hom x ∈ U ∧
          ∀ i : Fin n, (g3_proj C n i).left
            (pullback.snd C.hom (g3_power C n).hom x) ∈ U)
      rw [Fin.forall_fin_succ]
      rfl
    rw [he]
    exact affineProductOpen _ _ _ _ hU ih

/-- Affine curve opens give actual invariant affine product charts, also in degree zero.
Source: Milne, Jacobian Varieties, §3; Mumford, Abelian Varieties, §II. -/
theorem product_affine_index_aux (U : C.left.Opens) (hU : IsAffineOpen U)
    (hne : (U : Set C.left).Nonempty) :
    ∃ W : Index C n, W.val = productOpen C n U := by
  obtain ⟨x, hx⟩ := hne
  let d : C ⟶ g3_power C n := s2_lift n (fun _ => 𝟙 C)
  have hd (i : Fin n) : d.left ≫ (g3_proj C n i).left = 𝟙 C.left := by
    exact congrArg (fun k : C ⟶ C => k.left) (s2_check_lift_proj n (fun _ => 𝟙 C) i)
  have hn : (productOpen C n U : Set (g3_power C n).left).Nonempty := by
    refine ⟨d.left x, ?_⟩
    rw [productOpen, TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr (fun i => by
      change (g3_proj C n i).left (d.left x) ∈ U
      have he := congrArg (fun k : C.left ⟶ C.left => k x) (hd i)
      exact he ▸ hx)
  refine ⟨⟨productOpen C n U, productOpenAffine C U hU n, hn, ?_⟩, rfl⟩
  intro σ
  apply TopologicalSpace.Opens.ext
  ext y
  change (action C n σ).asIso.hom y ∈ (↑(productOpen C n U) : Set (g3_power C n).left) ↔
    y ∈ (↑(productOpen C n U) : Set (g3_power C n).left)
  simp only [productOpen, TopologicalSpace.Opens.coe_iInf,
    Set.mem_iInter, Scheme.Hom.coe_preimage, Set.mem_preimage]
  have he (i : Fin n) : (action C n σ).asIso.hom ≫ (g3_proj C n i).left =
      (g3_proj C n (σ⁻¹ i)).left := by
    exact congrArg (fun k => k.left) (s2_check_lift_proj n
      (fun i => g3_proj C n (σ⁻¹ i)) i)
  have hey (i : Fin n) : (g3_proj C n i).left ((action C n σ).asIso.hom y) =
      (g3_proj C n (σ⁻¹ i)).left y :=
    congrArg (fun k : (g3_power C n).left ⟶ C.left => k y) (he i)
  simp_rw [hey]
  constructor
  · intro h i
    have hh := h (σ i)
    change (g3_proj C n (σ.symm (σ i))).left y ∈ (U : Set C.left) at hh
    rw [σ.symm_apply_apply] at hh
    exact hh
  · intro h i
    exact h (σ⁻¹ i)

/-- Identify the actual affine invariant spectrum with its saturated global chart, retaining the projection.
Source: Milne, Jacobian Varieties, §3; SGA 1, Exposé V, §1. -/
theorem chart_comparison_aux (W : Index C n) :
    ∃ (V : (symmetricPower C n).left.Opens) (e : affineChart C n W ≅ V.toScheme),
      e.hom ≫ V.ι = chartInclusion C n W ∧
      affineProjection C n W ≫ e.hom ≫ V.ι = W.val.ι ≫ (projection C n).left ∧
      (projection C n).left ⁻¹ᵁ V = W.val := by
  let j := chartInclusion C n W
  refine ⟨j.opensRange, j.isoOpensRange, ?_, ?_, ?_⟩
  · exact j.isoOpensRange_hom_ι
  · rw [j.isoOpensRange_hom_ι]
    exact (s2_gluedQuotientMap_ι _ _ _ (chartCover C n) W).symm
  · apply TopologicalSpace.Opens.ext
    exact s2_gluedQuotientMap_preimage_chart _ _ _ (chartCover C n) W

/-- Affine inclusions and both intersection maps descend with their actual projection squares.
Source: Milne, Jacobian Varieties, §3; SGA 1, Exposé V, §1. -/
theorem overlap_descent_aux (U V : Index C n) :
    (∀ h : U ≤ V, chartMap C n U V h ≫ chartInclusion C n V = chartInclusion C n U ∧
    affineProjection C n U ≫ chartMap C n U V h =
      (g3_power C n).left.homOfLE h ≫ affineProjection C n V) ∧
    chartMap C n (intersection C n U V) U (by change U.val ⊓ V.val ≤ U.val; exact inf_le_left) ≫ chartInclusion C n U =
      chartMap C n (intersection C n U V) V (by change U.val ⊓ V.val ≤ V.val; exact inf_le_right) ≫ chartInclusion C n V ∧
    IsPullback
      (chartMap C n (intersection C n U V) U (by change U.val ⊓ V.val ≤ U.val; exact inf_le_left))
      (chartMap C n (intersection C n U V) V (by change U.val ⊓ V.val ≤ V.val; exact inf_le_right))
      (chartInclusion C n U) (chartInclusion C n V) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact ⟨s2_invariantAffineQuotientMap_gluedι _ _ _ U V h,
      s2_invariantAffineProjection_naturality _ _ _ U V h⟩
  · exact (s2_invariantAffineQuotientMap_gluedι _ _ _ _ U _).trans
      (s2_invariantAffineQuotientMap_gluedι _ _ _ _ V _).symm
  · exact (s2_quotientOverlap_isPullback _ _ _ (chartCover C n) U V).flip

/-- The retained ordered power has its finite integral projective categorical permutation quotient.
Source: Milne, Jacobian Varieties, §3; Mumford, Abelian Varieties, §II. -/
theorem projective_quotient_aux :
    IsIntegral (symmetricPower C n).left ∧ IsProjective (symmetricPower C n).hom ∧
    IsFinite (projection C n).left ∧ Function.Surjective (projection C n).left ∧
    (∀ σ : Equiv.Perm (Fin n), orderedPermutation C n σ ≫ orderedProjection C n =
      orderedProjection C n) ∧
    (∀ (T : Over (Spec ↧ℂ)) (f : OrderedPower C n ⟶ T),
      (∀ σ : Equiv.Perm (Fin n), orderedPermutation C n σ ≫ f = f) →
      ∃! d : symmetricPower C n ⟶ T, orderedProjection C n ≫ d = f) := by
  have hover (σ : Equiv.Perm (Fin n)) :
      (action C n σ).asIso.hom ≫ (g3_power C n).hom = (g3_power C n).hom :=
    Over.w (s2_symmetricPowerAction C n σ).asIso.hom
  have hi : ∀ σ : Equiv.Perm (Fin n),
      s2_permute C n σ ≫ projection C n = projection C n := by
    intro σ
    apply Over.OverMorphism.ext
    exact s2_gluedQuotientMap_invariant _ _ _ (chartCover C n) σ
  refine ⟨s2_invariantAffineGlued_isIntegral _ _ _ (chartCover C n),
    s2_projectiveAction_gluedQuotient_projective (g3_power C n) _
      (s2_symmetricPowerAction C n) (chartCover C n) hover,
    s2_gluedQuotientMap_finite_over (g3_power C n).hom _ _ hover (chartCover C n),
    s2_gluedQuotientMap_surjective _ _ _ (chartCover C n), ?_, ?_⟩
  · intro σ
    dsimp only [orderedProjection]
    rw [← Category.assoc, orderedRecursiveIso_permute, Category.assoc, hi]
  · intro T f hf
    let f' := (orderedRecursiveIso C n).inv ≫ f
    have hf' : ∀ σ, (action C n σ).asIso.hom ≫ f'.left = f'.left := by
      intro σ
      have h : s2_permute C n σ ≫ f' = f' := by
        dsimp only [f']
        rw [← Category.assoc, orderedRecursiveIso_inv_permute, Category.assoc, hf]
      exact congrArg (fun k => k.left) h
    obtain ⟨d, hd, hu⟩ := s2_gluedQuotientOverDesc_arbitrary
      (g3_power C n) _ (action C n) hover (chartCover C n) T f' hf'
    refine ⟨d, ?_, ?_⟩
    · change (orderedRecursiveIso C n).hom ≫ projection C n ≫ d = f
      calc
        _ = (orderedRecursiveIso C n).hom ≫ f' :=
          congrArg (fun k : g3_power C n ⟶ T => (orderedRecursiveIso C n).hom ≫ k) hd
        _ = f := (orderedRecursiveIso C n).hom_inv_id_assoc f
    · intro e he
      apply hu
      change projection C n ≫ e = (orderedRecursiveIso C n).inv ≫ f
      rw [← he]
      change projection C n ≫ e = (orderedRecursiveIso C n).inv ≫
        ((orderedRecursiveIso C n).hom ≫ projection C n) ≫ e
      simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The actual quotient has Krull dimension n, including n = 0.
Source: Milne, Jacobian Varieties, §3; Stacks Project, Lemma 29.45.9 (Tag 0ECG), dimension under integral surjective morphisms. -/
theorem krull_dimension_aux [SmoothOfRelativeDimension 1 C.hom] :
    topologicalKrullDim (symmetricPower C n).left = n := by
  obtain ⟨hi, hp, hfin, hs, _⟩ := projective_quotient_aux C n
  letI := hi
  letI := hfin
  letI : Surjective (projection C n).left := ⟨hs⟩
  rw [← s2e_finite_surjective_krull_dimension (projection C n).left]
  letI : SmoothOfRelativeDimension n (g3_power C n).hom := by
    simpa only [Nat.mul_one] using spec_g3_smoothOfRelativeDimension_power C 1 n
  rw [Scheme.topologicalKrullDim_eq_orderKrullDim]
  exact SmoothOfRelativeDimension.orderKrullDim_eq_complex (f := (g3_power C n).hom)

end HodgeLean.Foundations.Curves.SymmetricCharts
