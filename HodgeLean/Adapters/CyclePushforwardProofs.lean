import HodgeLean.Adapters.CyclePushforwardDefs
import HodgeLean.Adapters.CyclePushforwardDimension
import HodgeLean.Foundations.Mathlib.CyclePushforwardWitness
import HodgeLean.Adapters.CyclePushforwardProduct

/-! # Proof obligations for the quasi-compact cycle pushforward extending Fulton's proper
pushforward -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped MonoidalCategory

namespace HodgeLean.Adapters

universe u

/-- For quasi-compact `f`, every fibre meets the support of a cycle in a finite set. -/
theorem a1p_fibre_inter_support_finite {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    {R : Type*} [Zero R] (c : AlgebraicCycle X R) (y : Y) :
    (f ⁻¹' {y} ∩ Function.support c).Finite := by
  obtain ⟨U, hU⟩ := (PrespectralSpace.isTopologicalBasis (X := Y)).exists_subset_of_mem_open
    (by simp : y ∈ (⊤ : Set Y)) isOpen_univ
  refine (c.locallyFiniteSupport.finite_inter_support_of_isCompact
    (f.isSpectralMap.2 hU.1.1 hU.1.2)).subset ?_
  intro x hx
  exact ⟨show f x ∈ U from (show f x = y from hx.1) ▸ hU.2.1, hx.2⟩

/-- The coefficient of `f_* c` at `y` as a sum over the fibre. -/
theorem a1p_pushforward_apply {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    {R : Type*} [Semiring R] (c : AlgebraicCycle X R) (y : Y) :
    a1p_pushforward f c y = ∑ᶠ x ∈ f ⁻¹' {y}, c x * (a1p_degree f x : R) := rfl
/-- The fibre sum of `f_* c` at `y` as a `Finset` sum over any finite `t` between the fibre's
support and the fibre. -/
theorem a1p_pushforward_apply_eq_sum {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    {R : Type*} [Semiring R] (c : AlgebraicCycle X R) (y : Y) (t : Finset X)
    (h₁ : f ⁻¹' {y} ∩ Function.support c ⊆ t) (h₂ : (t : Set X) ⊆ f ⁻¹' {y}) :
    a1p_pushforward f c y = ∑ x ∈ t, c x * (a1p_degree f x : R) :=
  finsum_mem_eq_sum_of_subset _
    ((Set.inter_subset_inter_right _ (Function.support_mul_subset_left _ _)).trans h₁) h₂
/-- The tower law for `finrank` along two ring maps of fields, the infinite case included. -/
theorem a1p_finrank_comp {K L M : Type*} [Field K] [Field L] [Field M] (i : K →+* L)
    (j : L →+* M) :
    (letI := (j.comp i).toAlgebra; Module.finrank K M) =
      (letI := i.toAlgebra; Module.finrank K L) * (letI := j.toAlgebra; Module.finrank L M) := by
  let _ := i.toAlgebra
  let _ := j.toAlgebra
  let _ := (j.comp i).toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (Module.finrank_mul_finrank K L M).symm
/-- The generic point of the affine line is the zero prime of `ℂ[X]`. -/
theorem a1p_affineLineGeneric_asIdeal :
    (a1p_affineLineGeneric : Spec (.of (Polynomial ℂ))).asIdeal = ⊥ := by
  change (genericPoint (Spec (.of (Polynomial ℂ)))).asIdeal = ⊥
  rw [genericPoint_eq_bot_of_affine]
  rfl
/-- The ring map `X ↦ X²` of `ℂ[X]` is injective. -/
theorem a1p_aeval_X_sq_injective :
    Function.Injective (CommRingCat.ofHom
      (Polynomial.aeval (R := ℂ) (Polynomial.X ^ 2 : Polynomial ℂ)).toRingHom) := by
  intro f g h
  have h' : Polynomial.expand ℂ 2 f = Polynomial.expand ℂ 2 g := by
    simpa [a1pw_aeval_X_sq_eq_expand] using h
  exact Polynomial.expand_injective two_pos h'
/-- The squaring map fixes the generic point: `X ↦ X²` is injective. -/
theorem a1p_squareMap_generic :
    a1p_squareMap.left a1p_affineLineGeneric = a1p_affineLineGeneric := by
  apply PrimeSpectrum.ext
  change ((Spec.map (CommRingCat.ofHom
    (Polynomial.aeval (R := ℂ) (Polynomial.X ^ 2 : Polynomial ℂ)).toRingHom))
      a1p_affineLineGeneric).asIdeal = (a1p_affineLineGeneric : Spec (.of (Polynomial ℂ))).asIdeal
  rw [a1pw_Spec_map_asIdeal_eq_bot _ a1p_aeval_X_sq_injective _ a1p_affineLineGeneric_asIdeal,
    a1p_affineLineGeneric_asIdeal]

theorem a1p_degree_square_eq_two_aux :
    a1p_degree a1p_squareMap.left a1p_affineLineGeneric = 2 := by
  change (Spec.map (CommRingCat.ofHom
    (Polynomial.aeval (R := ℂ) (Polynomial.X ^ 2 : Polynomial ℂ)).toRingHom)).residueDegree
      a1p_affineLineGeneric = 2
  rw [a1pw_residueDegree_Spec_map _ a1p_aeval_X_sq_injective _ a1p_affineLineGeneric_asIdeal]
  exact a1pw_finrank_aeval_X_sq ℂ

theorem a1p_degree_contraction_eq_zero_aux :
    a1p_degree (CartesianMonoidalCategory.toUnit a1p_affineLine).left a1p_affineLineGeneric = 0 := by
  change (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ)))).residueDegree
    a1p_affineLineGeneric = 0
  exact a1pw_residueDegree_Spec_map_eq_zero (Polynomial ℂ) Polynomial.not_finite _
    a1p_affineLineGeneric_asIdeal

theorem a1p_height_square_generic_aux :
    Order.height (a1p_squareMap.left a1p_affineLineGeneric) =
      Order.height a1p_affineLineGeneric := by
  rw [a1p_squareMap_generic]

theorem a1p_height_contraction_generic_aux :
    Order.height ((CartesianMonoidalCategory.toUnit a1p_affineLine).left a1p_affineLineGeneric) ≠
      Order.height a1p_affineLineGeneric := by
  have hpt : IsMin ((CartesianMonoidalCategory.toUnit a1p_affineLine).left
      a1p_affineLineGeneric) := by
    intro y _
    have h : ∀ z : (𝟙_ (Over (Spec ↧ℂ))).left, z = y := fun z => by
      apply PrimeSpectrum.ext
      have := (z : PrimeSpectrum ℂ).isPrime
      have := (y : PrimeSpectrum ℂ).isPrime
      rw [Ideal.eq_bot_of_prime (z : PrimeSpectrum ℂ).asIdeal,
        Ideal.eq_bot_of_prime (y : PrimeSpectrum ℂ).asIdeal]
    rw [h ((CartesianMonoidalCategory.toUnit a1p_affineLine).left a1p_affineLineGeneric)]
  rw [Order.height_eq_zero.mpr hpt, ne_comm, Ne, Order.height_eq_zero]
  intro hmin
  have hX : (Ideal.span {Polynomial.X} : Ideal (Polynomial ℂ)).IsPrime :=
    (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X
  let p : a1p_affineLine.left := (⟨Ideal.span {Polynomial.X}, hX⟩ : PrimeSpectrum (Polynomial ℂ))
  have hle : p ≤ a1p_affineLineGeneric := by
    refine (PrimeSpectrum.le_iff_specializes (a1p_affineLineGeneric : PrimeSpectrum (Polynomial ℂ))
      (p : PrimeSpectrum (Polynomial ℂ))).mp ?_
    change (a1p_affineLineGeneric : Spec (.of (Polynomial ℂ))).asIdeal ≤ Ideal.span {_}
    rw [a1p_affineLineGeneric_asIdeal]
    exact bot_le
  have hge := hmin hle
  replace hge := (PrimeSpectrum.le_iff_specializes (p : PrimeSpectrum (Polynomial ℂ))
    (a1p_affineLineGeneric : PrimeSpectrum (Polynomial ℂ))).mpr hge
  change Ideal.span {_} ≤ (a1p_affineLineGeneric : Spec (.of (Polynomial ℂ))).asIdeal at hge
  rw [a1p_affineLineGeneric_asIdeal, le_bot_iff, Ideal.span_singleton_eq_bot] at hge
  exact Polynomial.X_ne_zero hge

theorem a1p_pushforward_single_aux {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    {R : Type*} [Semiring R] [DecidableEq X] [DecidableEq Y] (x : X) (r : R) :
    a1p_pushforward f (Function.locallyFinsuppWithin.single x r) =
      Function.locallyFinsuppWithin.single (f x) (r * (a1p_degree f x : R)) := by
  ext y
  rw [Function.locallyFinsuppWithin.single_apply]
  split_ifs with hy
  · subst hy
    rw [a1p_pushforward_apply_eq_sum f _ _ {x} (fun x' hx' => by
        by_contra h
        exact hx'.2 (by simp [show x' ≠ x by simpa using h])) (by simp),
      Finset.sum_singleton]
    simp
  · rw [a1p_pushforward_apply_eq_sum f _ _ ∅ (fun x' hx' => by
        by_cases h : x' = x
        · subst h
          exact absurd (hx'.1 : f x' = y).symm hy
        · exact (hx'.2 (by simp [h])).elim) (by simp),
      Finset.sum_empty]

theorem a1p_pushforward_add_aux {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    {R : Type*} [Semiring R] (c d : AlgebraicCycle X R) :
    a1p_pushforward f (c + d) = a1p_pushforward f c + a1p_pushforward f d := by
  ext y
  simp only [a1p_pushforward_apply, Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
    add_mul]
  exact finsum_mem_add_distrib'
    ((a1p_fibre_inter_support_finite f c y).subset
      (Set.inter_subset_inter_right _ (Function.support_mul_subset_left _ _)))
    ((a1p_fibre_inter_support_finite f d y).subset
      (Set.inter_subset_inter_right _ (Function.support_mul_subset_left _ _)))

theorem a1p_pushforward_mul_aux {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    {R : Type*} [Semiring R] (r : R) (c : AlgebraicCycle X R) :
    a1p_pushforward f (c.mapRange (r * ·) (mul_zero r)) =
      (a1p_pushforward f c).mapRange (r * ·) (mul_zero r) := by
  ext y
  have hfin := a1p_fibre_inter_support_finite f c y
  have h₂ : (hfin.toFinset : Set X) ⊆ f ⁻¹' {y} := fun x hx => (hfin.mem_toFinset.1 hx).1
  rw [Function.locallyFinsuppWithin.mapRange_apply,
    a1p_pushforward_apply_eq_sum f c y hfin.toFinset (fun x hx => hfin.mem_toFinset.2 hx) h₂,
    a1p_pushforward_apply_eq_sum f _ y hfin.toFinset (fun x hx => hfin.mem_toFinset.2
      ⟨hx.1, fun h => hx.2 (by simp [Function.locallyFinsuppWithin.mapRange_apply, h])⟩) h₂,
    Finset.mul_sum]
  simp only [Function.locallyFinsuppWithin.mapRange_apply, mul_assoc]

theorem a1p_pushforward_id_aux {X : Scheme.{u}} {R : Type*} [Semiring R]
    (c : AlgebraicCycle X R) :
    a1p_pushforward (𝟙 X) c = c := by
  ext x
  have h1 : ∀ x' : X, a1p_degree (𝟙 X) x' = 1 := Scheme.Hom.residueDegree_id
  rw [a1p_pushforward_apply]
  simp [h1]

theorem a1p_degree_comp_aux {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    a1p_degree (f ≫ g) x = a1p_degree g (f x) * a1p_degree f x := by
  have h := a1p_finrank_comp (g.residueFieldMap (f x)).hom (f.residueFieldMap x).hom
  unfold a1p_degree
  rw [Scheme.residueFieldMap_comp]
  exact h

theorem a1p_pushforward_comp_aux {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g] {R : Type*} [Semiring R] (c : AlgebraicCycle X R) :
    a1p_pushforward (f ≫ g) c = a1p_pushforward g (a1p_pushforward f c) := by
  classical
  ext z
  have hfin := a1p_fibre_inter_support_finite (f ≫ g) c z
  set T := hfin.toFinset
  have hT : ∀ x, x ∈ T ↔ g (f x) = z ∧ c x ≠ 0 := fun x => hfin.mem_toFinset
  rw [a1p_pushforward_apply_eq_sum (f ≫ g) c z T (fun x hx => (hT x).2 hx)
      (fun x hx => ((hT x).1 hx).1),
    a1p_pushforward_apply_eq_sum g _ z (T.image f) ?_ ?_]
  rotate_left
  · rintro y ⟨hy, hne⟩
    obtain ⟨x, hx, hcx⟩ := exists_ne_zero_of_finsum_mem_ne_zero hne
    have hfx : f x = y := hx
    refine Finset.mem_image.2 ⟨x, (hT x).2 ⟨?_, left_ne_zero_of_mul hcx⟩, hfx⟩
    rw [hfx]
    exact hy
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    exact ((hT x).1 hx).1
  have hfib : ∀ y ∈ T.image f, a1p_pushforward f c y =
      ∑ x ∈ T with f x = y, c x * (a1p_degree f x : R) := by
    intro y hy
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hy
    refine a1p_pushforward_apply_eq_sum f c _ _ (fun x hx => ?_) (fun x hx => ?_)
    · refine Finset.mem_filter.2 ⟨(hT x).2 ⟨?_, hx.2⟩, hx.1⟩
      rw [show f x = f x₀ from hx.1]
      exact ((hT x₀).1 hx₀).1
    · exact (Finset.mem_filter.1 hx).2
  have hrow : ∀ y ∈ T.image f, a1p_pushforward f c y * (a1p_degree g y : R) =
      ∑ x ∈ T with f x = y, c x * (a1p_degree f x : R) * (a1p_degree g (f x) : R) := by
    intro y hy
    rw [hfib y hy, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.1 hx).2]
  rw [Finset.sum_congr rfl hrow,
    Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem f hx)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [a1p_degree_comp_aux, Nat.cast_mul, mul_assoc, (Nat.cast_commute _ _).eq]

theorem a1p_degree_pos_iff_aux {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (x : X.left) :
    0 < a1p_degree f.left x ↔ Order.height (f.left x) = Order.height x :=
  a1d_degree_pos_iff f x

theorem a1p_pushforward_preserves_dimension_aux {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact f.left]
    {R : Type*} [Semiring R] (k : ℕ∞) (c : AlgebraicCycle X.left R)
    (hc : ∀ x, c x ≠ 0 → Order.height x = k) (y : Y.left)
    (hy : a1p_pushforward f.left c y ≠ 0) :
    Order.height y = k := by
  obtain ⟨x, hxy, hx⟩ := exists_ne_zero_of_finsum_mem_ne_zero hy
  have hxy : f.left x = y := hxy
  have hc0 : c x ≠ 0 := fun h => hx (by rw [h, zero_mul])
  have hd : 0 < a1p_degree f.left x :=
    Nat.pos_of_ne_zero fun h => hx (by simp [h])
  rw [← hxy, (a1d_degree_pos_iff f x).mp hd, hc x hc0]

theorem a1p_pushforward_eq_map_aux {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact f.left]
    {R : Type*} [Semiring R] (c : AlgebraicCycle X.left R) :
    a1p_pushforward f.left c = AlgebraicCycle.map f.left Order.height Order.height c := by
  have h : (fun x => (a1p_degree f.left x : R)) =
      fun x => (AlgebraicCycle.mapCoeff f.left Order.height Order.height x : R) := by
    funext x
    unfold AlgebraicCycle.mapCoeff
    split_ifs with hx
    · rfl
    · rw [Nat.eq_zero_of_not_pos fun hpos =>
        hx ((a1p_degree_pos_iff_aux f x).1 hpos).symm, Nat.cast_zero]
  unfold a1p_pushforward AlgebraicCycle.map
  rw [h]

theorem a1p_productSet_isIrreducible_aux (X Y : Over (Spec ↧ℂ))
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (z : X.left) (w : Y.left) :
    IsIrreducible (a1p_productSet X Y z w) :=
  a1x_productSet_isIrreducible X Y z w

theorem a1p_pushforward_externalProduct_prime_aux {X Y X' Y' : Over (Spec ↧ℂ)}
    (f : X ⟶ X') (g : Y ⟶ Y')
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    [QuasiCompact f.left] [QuasiCompact g.left] {R : Type*} [Semiring R]
    (z : X.left) (w : Y.left) :
    a1p_pushforward (f ⊗ₘ g).left (a1p_externalProduct X Y z w R) =
      (a1p_externalProduct X' Y' (f.left z) (g.left w) R).mapRange
        (((a1p_degree f.left z * a1p_degree g.left w : ℕ) : R) * ·) (mul_zero _) := by
  classical
  have h := a1p_productSet_isIrreducible_aux X Y z w
  have h' := a1p_productSet_isIrreducible_aux X' Y' (f.left z) (g.left w)
  let T : Scheme.Pullback.Triplet X.hom Y.hom :=
    Scheme.Pullback.Triplet.mk' z w (Subsingleton.elim _ _)
  have : IsAlgClosed ((Spec ↧ℂ).residueField T.s) := a1x_isAlgClosed_residueField _
  obtain ⟨hD, hD', hinj, hrank⟩ := a1x_tensorMap_spec f.left g.left (Over.w f) (Over.w g) T
  let φ := a1x_tensorMap f.left g.left (Over.w f) (Over.w g) T
  let T' := a1x_imageTriplet f.left g.left (Over.w f) (Over.w g) T
  let q : Spec T.tensor := ⟨⊥, Ideal.isPrime_bot⟩
  have hq : ∀ r : Spec T.tensor, q ⤳ r := fun r =>
    (PrimeSpectrum.le_iff_specializes _ _).mp (show q.asIdeal ≤ r.asIdeal from bot_le)
  let q' : Spec T'.tensor := Spec.map φ q
  have hq'0 : q'.asIdeal = ⊥ := Ideal.comap_bot_of_injective φ.hom hinj
  have hq' : ∀ r : Spec T'.tensor, q' ⤳ r := fun r =>
    (PrimeSpectrum.le_iff_specializes _ _).mp
      (show q'.asIdeal ≤ r.asIdeal by rw [hq'0]; exact bot_le)
  have hp := a1x_genericPoint_eq X Y z w h T rfl rfl q hq
  have hp' := a1x_genericPoint_eq X' Y' (f.left z) (g.left w) h' T' rfl rfl q' hq'
  have hsq : T.SpecTensorTo ≫ (f ⊗ₘ g).left = Spec.map φ ≫ T'.SpecTensorTo :=
    a1x_specTensorTo_map f.left g.left (Over.w f) (Over.w g) T
  have hpt : (f ⊗ₘ g).left h.genericPoint = h'.genericPoint := by
    rw [hp, hp']
    exact congr($(hsq) q)
  have hdeg : a1p_degree (f ⊗ₘ g).left h.genericPoint =
      a1p_degree f.left z * a1p_degree g.left w := by
    have h1 := a1p_degree_comp_aux T.SpecTensorTo (f ⊗ₘ g).left q
    have h2 := a1p_degree_comp_aux (Spec.map φ) T'.SpecTensorTo q
    rw [hsq, h2, a1x_degree_specTensorTo_bot T q rfl, a1x_degree_specTensorTo_bot T' q' hq'0,
      a1x_degree_specMap_bot φ q rfl hq'0, hrank] at h1
    rw [hp]
    simp only [mul_one, one_mul] at h1
    exact h1.symm
  rw [a1p_externalProduct, a1p_externalProduct, dite_eq_left h, dite_eq_left h']
  refine (a1p_pushforward_single_aux _ _ _).trans ?_
  rw [hpt, hdeg]
  ext y
  change _ = ((a1p_degree f.left z * a1p_degree g.left w : ℕ) : R) * _
  erw [Function.locallyFinsuppWithin.single_apply, Function.locallyFinsuppWithin.single_apply]
  split_ifs with h1 h2 h2
  · simp
  · exact absurd h1 h2
  · exact absurd h2 h1
  · simp

theorem a1p_pushforward_externalProduct_aux {X Y X' Y' : Over (Spec ↧ℂ)}
    (f : X ⟶ X') (g : Y ⟶ Y')
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    [CompactSpace X.left] [CompactSpace Y.left]
    [QuasiCompact f.left] [QuasiCompact g.left] {R : Type*} [Semiring R]
    (α : AlgebraicCycle X.left R) (β : AlgebraicCycle Y.left R) :
    a1p_pushforward (f ⊗ₘ g).left (a1p_externalProductCycle α β) =
      a1p_externalProductCycle (a1p_pushforward f.left α) (a1p_pushforward g.left β) := by
  classical
  let s := (Function.locallyFinsupp.finite_support α).toFinset
  let t := (Function.locallyFinsupp.finite_support β).toFinset
  have hs : α.support ⊆ s := by simp [s]
  have ht : β.support ⊆ t := by simp [t]
  let P : AlgebraicCycle (gagam_product X Y).left R →+ AlgebraicCycle (gagam_product X' Y').left R :=
    { toFun := a1p_pushforward (f ⊗ₘ g).left
      map_zero' := a1x_pushforward_zero (f ⊗ₘ g).left
      map_add' := a1p_pushforward_add_aux (f ⊗ₘ g).left }
  let H : X.left → Y.left → AlgebraicCycle (gagam_product X' Y').left R := fun z w =>
    (a1p_externalProduct X' Y' (f.left z) (g.left w) R).mapRange
      (α z * (a1p_degree f.left z : R) * (β w * (a1p_degree g.left w : R)) * ·) (mul_zero _)
  have hL : a1p_pushforward (f ⊗ₘ g).left (a1p_externalProductCycle α β) =
      ∑ z ∈ s, ∑ w ∈ t, H z w := by
    rw [a1x_externalProductCycle_eq_sum α β s t hs ht]
    change P _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    change a1p_pushforward (f ⊗ₘ g).left
      ((a1p_externalProduct X Y z w R).mapRange ((α z * β w) * ·) (mul_zero _)) = _
    refine (a1p_pushforward_mul_aux (f ⊗ₘ g).left (α z * β w)
      (a1p_externalProduct X Y z w R)).trans ?_
    rw [a1p_pushforward_externalProduct_prime_aux]
    refine (a1x_mapRange_mapRange _ _ _).trans ?_
    simp only [H, Nat.cast_mul, mul_assoc]
    congr 1
    funext x
    rw [← mul_assoc (β w), ← Nat.cast_comm, mul_assoc]
  have hR : a1p_externalProductCycle (a1p_pushforward f.left α) (a1p_pushforward g.left β) =
      ∑ z ∈ s, ∑ w ∈ t, H z w := by
    rw [a1x_externalProductCycle_eq_sum _ _ (s.image f.left) (t.image g.left)
      (a1x_pushforward_support f.left α s hs) (a1x_pushforward_support g.left β t ht)]
    have hterm : ∀ z' w', (a1p_externalProduct X' Y' z' w' R).mapRange
        (a1p_pushforward f.left α z' * a1p_pushforward g.left β w' * ·) (mul_zero _) =
        ∑ z ∈ s with f.left z = z', ∑ w ∈ t with g.left w = w', H z w := by
      intro z' w'
      rw [a1x_pushforward_apply_eq_sum f.left α s hs, a1x_pushforward_apply_eq_sum g.left β t ht,
        Finset.sum_mul_sum, a1x_mapRange_sum]
      refine Finset.sum_congr rfl fun z hz => ?_
      rw [a1x_mapRange_sum]
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [(Finset.mem_filter.mp hz).2.symm, (Finset.mem_filter.mp hw).2.symm]
    simp only [hterm]
    rw [Finset.sum_congr rfl fun z' _ => Finset.sum_comm]
    rw [Finset.sum_congr rfl fun z' _ => Finset.sum_congr rfl fun z _ =>
      Finset.sum_fiberwise_of_maps_to (fun w hw => Finset.mem_image_of_mem g.left hw) _]
    exact Finset.sum_fiberwise_of_maps_to (fun z hz => Finset.mem_image_of_mem f.left hz) _
  rw [hL, hR]

end HodgeLean.Adapters
