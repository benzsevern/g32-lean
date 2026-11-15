import HodgeLean.Adapters.ChowCorrespondenceProofs
import HodgeLean.Adapters.CyclePushforwardDimension
import HodgeLean.Adapters.CyclePushforwardProduct
import HodgeLean.Adapters.KleimanCoheightCharts
import Other.AlgebraicGeometry.Cycle.Component.GenericPoint

/-! # Rational equivalences from families over a pointed curve

Let `C` be an integral scheme with a rational function `t` that is a unit at every point outside
two sets `Z₀` and `Z_∞`, and lies in the maximal ideal at the points of `Z₀`. A subvariety `closure {y}` of a scheme `T`
that dominates `C` through `h₀ : T → C` carries the rational function `h₀^* t`. Its principal
cycle, pushed forward along a proper `q : T → X`, is rationally equivalent to zero on `X`; it is
supported on the images of the components of the fibres of `closure {y}` over `Z₀` and `Z_∞`,
and its coefficient at the image of a component over `Z₀` that no component over `Z_∞` reaches is
positive.

This is how a family of cycles parametrised by `ℙ¹` gives a rational equivalence between its
fibres over `0` and `∞` (Fulton, §1.6), with only the supports and the sign at one component
computed.

Source: Fulton, *Intersection Theory*, second edition, §1.3, §1.4 and §1.6 (Proposition 1.6 and
the description of `Rat_k X` through `X × ℙ¹`). HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Order HodgeLean.Foundations.Curves

namespace HodgeLean.Adapters

universe u

/-! ## Dimension of subvarieties -/

/-- On an integral scheme of finite type over `ℂ`, height plus coheight of a point is the height of
the generic point.
Source: Hartshorne, *Algebraic Geometry*, II, Exercise 3.20. -/
theorem a3m_height_add_coheight (Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType Y.hom]
    [IsIntegral Y.left] (y : Y.left) :
    height y + coheight y = height (genericPoint Y.left) := by
  obtain ⟨-, n, hn, htr⟩ := a1d_height_eq_trdeg (genericPoint Y.left)
  rw [hn]
  refine hc9k8_height_add_coheight_of_charts Y.left n (fun y => ?_) y
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : Y.left.Opens) from trivial)
  have : Nonempty U := ⟨⟨_, hyU⟩⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hU.fromSpec ≫ Y.hom)
  let : Algebra ℂ Γ(Y.left, U) := φ.hom.toAlgebra
  have : Algebra.FiniteType ℂ Γ(Y.left, U) := by
    have : LocallyOfFiniteType (Spec.map φ) := hφ ▸ inferInstance
    exact RingHom.finiteType_algebraMap.mp (HasRingHomProperty.Spec_iff.mp this)
  refine ⟨Γ(Y.left, U), hU.fromSpec, inferInstance, by rw [hU.range_fromSpec]; exact hyU,
    fun P hP => ?_⟩
  rw [hc9k8_height_add_ringKrullDim_quotient (k := ℂ) P]
  have hηU : genericPoint Y.left ∈ U :=
    ((genericPoint_spec Y.left).mem_open_set_iff U.isOpen).mpr (by simpa using ⟨y, hyU⟩)
  let q := hU.primeIdealOf ⟨genericPoint Y.left, hηU⟩
  obtain ⟨-, m, hm, htr'⟩ := a1d_height_chart (genericPoint Y.left) U hU q
    (hU.fromSpec_primeIdealOf ⟨genericPoint Y.left, hηU⟩)
  have hmn : m = n := by exact_mod_cast htr'.symm.trans htr
  have hq : q.asIdeal = ⊥ := by
    change (hU.primeIdealOf _).asIdeal = ⊥
    rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
    rfl
  have h := hc9k8_height_spec Γ(Y.left, U) q
  rw [hm, hmn, hq] at h
  rw [← ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _), ← h]
  rfl

/-- The integral subscheme `closure {w}` of a scheme over `ℂ`, as a scheme over `ℂ`. -/
abbrev a3m_component (X : Over (Spec ↧ℂ)) (w : X.left) : Over (Spec ↧ℂ) :=
  Over.mk (cycleComponentι X.left w ≫ X.hom)

instance a3m_component_locallyOfFiniteType (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (w : X.left) : LocallyOfFiniteType (a3m_component X w).hom := by
  change LocallyOfFiniteType (cycleComponentι X.left w ≫ X.hom)
  infer_instance

instance a3m_component_isIntegral (X : Over (Spec ↧ℂ)) (w : X.left) :
    IsIntegral (a3m_component X w).left :=
  inferInstanceAs (IsIntegral (cycleComponent X.left w))

/-- The closed immersion of `closure {w}` preserves heights. -/
theorem a3m_height_cycleComponentι (X : Scheme) (w : X) (z : cycleComponent X w) :
    height (cycleComponentι X w z) = height z := by
  rw [← height_orderIso (cycleComponentOrderIsoIic X w) z]
  exact (height_eq_of_strictMono (Subtype.val : Set.Iic w → X) (fun _ _ h => h)
    (fun a b hb => ⟨⟨b, hb.le.trans a.2⟩, hb, rfl⟩) (cycleComponentOrderIsoIic X w z)).symm

/-- The generic point of `closure {w}` maps to `w`. -/
theorem a3m_cycleComponentι_genericPoint (X : Scheme) (w : X) :
    cycleComponentι X w (genericPoint (cycleComponent X w)) = w := by
  set e := cycleComponentOrderIsoIic X w
  have h1 : e (genericPoint (cycleComponent X w)) ≤ ⟨w, le_refl w⟩ :=
    (e (genericPoint (cycleComponent X w))).2
  have h2 : (⟨w, le_refl w⟩ : Set.Iic w) ≤ e (genericPoint (cycleComponent X w)) := by
    rw [← e.apply_symm_apply ⟨w, le_refl w⟩, e.le_iff_le, Scheme.le_iff_specializes]
    exact (genericPoint_spec (cycleComponent X w)).specializes trivial
  have h1' : cycleComponentι X w (genericPoint (cycleComponent X w)) ≤ w := h1
  have h2' : w ≤ cycleComponentι X w (genericPoint (cycleComponent X w)) := h2
  rw [Scheme.le_iff_specializes] at h1' h2'
  exact (h2'.antisymm h1').eq

/-- The generic point of `closure {w}` has the height of `w`. -/
theorem a3m_height_cycleComponent_genericPoint (X : Scheme) (w : X) :
    height (genericPoint (cycleComponent X w)) = height w := by
  rw [← a3m_height_cycleComponentι, a3m_cycleComponentι_genericPoint]

/-- A point of `closure {w}` has codimension one in it exactly when its height is one less than
that of `w`. -/
theorem a3m_coheight_eq_one_iff (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] (w : X.left)
    (k : ℕ) (hw : height w = (k + 1 : ℕ)) (z : cycleComponent X.left w) :
    coheight z = 1 ↔ height (cycleComponentι X.left w z) = k := by
  have hsum := a3m_height_add_coheight (a3m_component X w) z
  change height z + coheight z = height (genericPoint (cycleComponent X.left w)) at hsum
  rw [a3m_height_cycleComponent_genericPoint, hw] at hsum
  rw [a3m_height_cycleComponentι]
  have hfin : height z ≠ ⊤ := fun h => by
    rw [h, top_add] at hsum
    exact ENat.top_ne_natCast (k + 1) hsum
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hfin
  rw [← hm] at hsum ⊢
  have hfin' : coheight z ≠ ⊤ := fun h => by
    rw [h, add_top] at hsum
    exact ENat.top_ne_natCast (k + 1) hsum
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hfin'
  rw [← hn] at hsum ⊢
  have : m + n = k + 1 := by exact_mod_cast hsum
  constructor
  · intro h1
    have : n = 1 := by exact_mod_cast h1
    norm_cast
    omega
  · intro h1
    have : m = k := by exact_mod_cast h1
    norm_cast
    omega

/-- A closed immersion has degree one at every point. -/
theorem a3m_degree_closedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X) :
    a1p_degree f x = 1 := by
  refine a1x_degree_eq_one_of_surjective f x ?_
  intro a
  obtain ⟨b, rfl⟩ := X.residue_surjective x a
  obtain ⟨c, hc⟩ := f.stalkMap_surjective x b
  refine ⟨Y.residue (f x) c, ?_⟩
  rw [← hc, ← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]

/-! ## Orders of vanishing -/

section Ord

variable {Z : Scheme.{u}} [IsIntegral Z]

/-- The order of vanishing at a point of codimension one of the image of a nonzero element of the
local ring is the length of its quotient.
Source: Mathlib, `AlgebraicGeometry.Scheme.ord` and `Ring.ordFrac_eq_ord`. -/
theorem a3m_ord_algebraMap [IsLocallyNoetherian Z] (z : Z) (hz : coheight z = 1)
    (a : Z.presheaf.stalk z) (ha : a ≠ 0) :
    ∃ n : ℕ, Ring.ord (Z.presheaf.stalk z) a = n ∧
      Z.ord (algebraMap (Z.presheaf.stalk z) Z.functionField a) z = n := by
  have : Ring.KrullDimLE 1 (Z.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  have hnzd : a ∈ nonZeroDivisors (Z.presheaf.stalk z) := mem_nonZeroDivisors_of_ne_zero ha
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (Ring.ord_ne_top hnzd)
  refine ⟨n, hn.symm, ?_⟩
  have hne : algebraMap (Z.presheaf.stalk z) Z.functionField a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha
  rw [Scheme.ord_eq_iff hz hne]
  change Ring.ordFrac (Z.presheaf.stalk z) (algebraMap (Z.presheaf.stalk z) Z.functionField a) = _
  rw [Ring.ordFrac_eq_ord _ ha, Ring.ordMonoidWithZeroHom_eq_coe _ hnzd hn.symm]

/-- A unit of the local ring has order zero. -/
theorem a3m_ord_algebraMap_of_isUnit [IsLocallyNoetherian Z] (z : Z)
    (a : Z.presheaf.stalk z) (ha : IsUnit a) :
    Z.ord (algebraMap (Z.presheaf.stalk z) Z.functionField a) z = 0 := by
  by_cases hz : coheight z = 1
  · obtain ⟨n, hn, h⟩ := a3m_ord_algebraMap z hz a ha.ne_zero
    rw [h]
    rw [Ring.ord_of_isUnit ha] at hn
    exact_mod_cast hn.symm
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hz _

/-- A nonzero element of the maximal ideal has positive order at a point of codimension one. -/
theorem a3m_ord_algebraMap_pos [IsLocallyNoetherian Z] (z : Z) (hz : coheight z = 1)
    (a : Z.presheaf.stalk z) (ha : a ≠ 0) (hm : a ∈ IsLocalRing.maximalIdeal _) :
    0 < Z.ord (algebraMap (Z.presheaf.stalk z) Z.functionField a) z := by
  obtain ⟨n, hn, h⟩ := a3m_ord_algebraMap z hz a ha
  rw [h]
  have hne : Ring.ord (Z.presheaf.stalk z) a ≠ 0 := by
    rw [Ring.ord, Ne, Module.length_eq_zero_iff, not_subsingleton_iff_nontrivial]
    exact Ideal.Quotient.nontrivial_iff.2 (by
      rw [Ne, Ideal.span_singleton_eq_top]
      exact (IsLocalRing.mem_maximalIdeal a).1 hm)
  rw [hn] at hne
  exact_mod_cast Nat.pos_of_ne_zero (by exact_mod_cast hne)

/-- On a Noetherian integral scheme a nonzero rational function has finitely many points of
nonzero order.
Source: Hartshorne, *Algebraic Geometry*, II, Lemma 6.1. -/
theorem a3m_ord_support_finite [IsNoetherian Z] (f : Z.functionField) (hf : f ≠ 0) :
    (Function.support (Z.ord f)).Finite := by
  obtain ⟨U, _, g, hU, hfg, hg⟩ := exists_isUnit_germ_eq Z f hf
  let p : Set Z := (U : Set Z)ᶜ
  have hsub : Function.support (Z.ord f) ⊆ p := by
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx
    intro hxU
    apply hx
    rw [← hfg]
    exact Scheme.ord_of_isUnit hg hxU
  have hpclosed : IsClosed p := U.isOpen.isClosed_compl
  have hclosure : closure p ≠ Set.univ := by
    intro h
    let y : Z := hU.some.1
    have hyU : y ∈ (U : Z.Opens) := by simpa [y] using hU.some.2
    have hu : y ∈ p := by
      rw [← hpclosed.closure_eq, h]
      exact Set.mem_univ _
    exact hu hyU
  have : QuasiSober p := Topology.IsClosedEmbedding.quasiSober
    hpclosed.isClosedEmbedding_subtypeVal
  have hfinite := TopologicalSpace.NoetherianSpace.finite_coheight_one_of_closure_ne_univ
    (X := Z) (p := p) hclosure
  refine hfinite.subset ?_
  intro x hx
  refine ⟨hsub hx, ?_⟩
  by_contra hn
  exact hx (Scheme.ord_eq_zero_of_coheight_neq_one hn f)

end Ord

/-! ## Pulling back rational functions along a dominant morphism -/

section Pullback

variable {Z C : Scheme.{u}} [IsIntegral Z] [IsIntegral C] (h : Z ⟶ C)

theorem a3m_specializes_genericPoint (hgen : h (genericPoint Z) = genericPoint C) :
    h (genericPoint Z) ⤳ genericPoint C := by
  rw [hgen]

/-- The pullback `h^* t` of a rational function along a morphism of integral schemes sending the
generic point to the generic point: the stalk map at the generic point.
Source: Hartshorne, *Algebraic Geometry*, I, §4 (dominant rational maps induce maps of function
fields); Mathlib, `AlgebraicGeometry.Scheme.Hom.stalkMap`. -/
def a3m_pullbackFF (hgen : h (genericPoint Z) = genericPoint C) (t : C.functionField) :
    Z.functionField :=
  h.stalkMap (genericPoint Z)
    (C.presheaf.stalkSpecializes (a3m_specializes_genericPoint h hgen) t)

/-- The pullback of a rational function that is regular at `h z`, with value `a` in the local
ring, is the image of `h^♯ a` in the local ring of `z`. -/
theorem a3m_pullbackFF_eq (hgen : h (genericPoint Z) = genericPoint C) (t : C.functionField)
    (z : Z) (a : C.presheaf.stalk (h z))
    (ha : C.presheaf.stalkSpecializes (genericPoint_specializes (h z)) a = t) :
    a3m_pullbackFF h hgen t =
      algebraMap (Z.presheaf.stalk z) Z.functionField (h.stalkMap z a) := by
  rw [a3m_pullbackFF, ← ha]
  change _ = Z.presheaf.stalkSpecializes _ (h.stalkMap z a)
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply h (genericPoint Z) z
    (genericPoint_specializes z)]
  congr 1
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply]

theorem a3m_pullbackFF_ne_zero (hgen : h (genericPoint Z) = genericPoint C)
    (t : C.functionField) (ht : t ≠ 0) : a3m_pullbackFF h hgen t ≠ 0 := by
  let ψ : C.functionField →+* Z.functionField :=
    (C.presheaf.stalkSpecializes (a3m_specializes_genericPoint h hgen) ≫
      h.stalkMap (genericPoint Z)).hom
  have : a3m_pullbackFF h hgen t = ψ t := rfl
  rw [this]
  exact (map_ne_zero_iff _ ψ.injective).2 ht

variable [IsLocallyNoetherian Z]

/-- If `t` is a unit at `h z`, then `h^* t` has order zero at `z`. -/
theorem a3m_ord_pullbackFF_eq_zero (hgen : h (genericPoint Z) = genericPoint C)
    (t : C.functionField) (z : Z) (a : C.presheaf.stalk (h z)) (ha : IsUnit a)
    (hat : C.presheaf.stalkSpecializes (genericPoint_specializes (h z)) a = t) :
    Z.ord (a3m_pullbackFF h hgen t) z = 0 := by
  rw [a3m_pullbackFF_eq h hgen t z a hat]
  exact a3m_ord_algebraMap_of_isUnit z _ (ha.map (h.stalkMap z).hom)

/-- If `t` vanishes at `h z` and `z` has codimension one, then `h^* t` has positive order at
`z`. -/
theorem a3m_ord_pullbackFF_pos (hgen : h (genericPoint Z) = genericPoint C)
    (t : C.functionField) (ht : t ≠ 0) (z : Z) (hz : coheight z = 1)
    (a : C.presheaf.stalk (h z)) (ha : a ∈ IsLocalRing.maximalIdeal _)
    (hat : C.presheaf.stalkSpecializes (genericPoint_specializes (h z)) a = t) :
    0 < Z.ord (a3m_pullbackFF h hgen t) z := by
  have hne := a3m_pullbackFF_ne_zero h hgen t ht
  rw [a3m_pullbackFF_eq h hgen t z a hat] at hne ⊢
  refine a3m_ord_algebraMap_pos z hz _ (fun h0 => hne (by rw [h0, map_zero])) ?_
  exact (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
    (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit (h.stalkMap z).hom a hu)

end Pullback

/-! ## The rational equivalence of a family -/

/-- A pointed curve with a coordinate: an integral scheme `C`, a zero set `Z₀`, a second set
`Z_∞`, and a nonzero rational function `t` that is a unit at every point outside `Z₀ ∪ Z_∞` and
lies in the maximal ideal at every point of `Z₀`. The projective line `Proj ℤ[x₀, x₁]` with
`t = x₁/(x₁ - x₀)`, `Z₀ = V₊(x₁)` and `Z_∞ = V₊(x₁ - x₀)` is the example used.
Source: Fulton, *Intersection Theory*, second edition, §1.6 (the coordinate `t` on `ℙ¹`). -/
structure a3m_PointedCurve where
  /-- The curve. -/
  C : Scheme.{0}
  [isIntegral : IsIntegral C]
  /-- The zeros of `t`. -/
  Z0 : Set C
  /-- The other points where `t` may fail to be a unit. -/
  Zinf : Set C
  /-- The coordinate. -/
  t : C.functionField
  t_ne_zero : t ≠ 0
  unit : ∀ c : C, c ∉ Z0 → c ∉ Zinf → ∃ a : C.presheaf.stalk c, IsUnit a ∧
    C.presheaf.stalkSpecializes (genericPoint_specializes c) a = t
  zero : ∀ c ∈ Z0, ∃ a : C.presheaf.stalk c, a ∈ IsLocalRing.maximalIdeal _ ∧
    C.presheaf.stalkSpecializes (genericPoint_specializes c) a = t

attribute [instance] a3m_PointedCurve.isIntegral

/-- Pushforward commutes with casting integer coefficients to rational ones. -/
theorem a3m_pushforward_intCast {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (D : AlgebraicCycle X ℤ) :
    (a1p_pushforward f D).mapRange (Int.cast : ℤ → ℚ) Int.cast_zero =
      a1p_pushforward f (D.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero) := by
  ext y
  rw [Function.locallyFinsuppWithin.mapRange_apply]
  change ((∑ᶠ x ∈ f ⁻¹' {y}, D x * (a1p_degree f x : ℤ) : ℤ) : ℚ) =
    ∑ᶠ x ∈ f ⁻¹' {y}, ((D x : ℤ) : ℚ) * (a1p_degree f x : ℚ)
  simp only [finsum_mem_def]
  by_cases hfin : (Function.support ((f ⁻¹' {y}).indicator
      fun x => D x * (a1p_degree f x : ℤ))).Finite
  · have := (Int.castAddHom ℚ).map_finsum hfin
    simp only [Int.coe_castAddHom] at this
    rw [this]
    congr 1
    ext x
    by_cases hx : x ∈ f ⁻¹' {y}
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  · have hfin' : ¬ (Function.support ((f ⁻¹' {y}).indicator
        fun x => ((D x : ℤ) : ℚ) * (a1p_degree f x : ℚ))).Finite := by
      convert hfin using 2
      ext x
      by_cases hx : x ∈ f ⁻¹' {y}
      · simp only [Function.mem_support, Set.indicator_of_mem hx]
        constructor <;> intro h h' <;> apply h <;> exact_mod_cast h'
      · simp [hx]
    rw [finsum_of_infinite_support hfin, finsum_of_infinite_support hfin', Int.cast_zero]

/-- The rational equivalence of a family over a pointed curve. Let `q : T → X` be proper, and
`closure {y} ⊆ T` a subvariety of dimension `k + 1` dominating the pointed curve through
`h₀ : T → C`. The pushforward along `q` of the principal cycle of `h₀^* t` on `closure {y}` is a
cycle `c` rationally equivalent to zero on `X`, such that
* every point with a nonzero coefficient in `c` is the image `q r`, of dimension `k`, of a point
  `r` of `closure {y}` of dimension `k` lying over `Z₀` or `Z_∞`;
* if no point of `closure {y}` of dimension `k` over `Z_∞` maps to `x'`, the coefficient of `x'`
  is nonnegative, and positive if moreover some point of dimension `k` over `Z₀` maps to `x'`,
  of dimension `k`.
Source: Fulton, *Intersection Theory*, second edition, §1.4 (proper pushforward of a principal
cycle is rationally equivalent to zero, Theorem 1.4) and §1.6. -/
theorem a3m_family_glue {X T : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsNoetherian T.left]
    (q : T ⟶ X) [IsProper q.left] (L : a3m_PointedCurve) (h₀ : T.left ⟶ L.C)
    (k : ℕ) (y : T.left) (hy : h₀ y = genericPoint L.C) (hk : height y = (k + 1 : ℕ)) :
    ∃ c ∈ a2_ratEquivDim X.left ℚ k,
      (∀ x', c x' ≠ 0 → ∃ r, y ⤳ r ∧ height r = k ∧ (h₀ r ∈ L.Z0 ∨ h₀ r ∈ L.Zinf) ∧
        q.left r = x' ∧ height x' = k) ∧
      (∀ x', (∀ r, y ⤳ r → height r = k → q.left r = x' → h₀ r ∉ L.Zinf) → 0 ≤ c x') ∧
      (∀ x', (∀ r, y ⤳ r → height r = k → q.left r = x' → h₀ r ∉ L.Zinf) →
        (∃ r, y ⤳ r ∧ height r = k ∧ h₀ r ∈ L.Z0 ∧ q.left r = x' ∧ height x' = k) →
          0 < c x') := by
  classical
  set Z := cycleComponent T.left y
  set ι := cycleComponentι T.left y
  have : CompactSpace Z := ι.isClosedEmbedding.compactSpace
  have : IsNoetherian Z := ⟨⟩
  set h := ι ≫ h₀
  have hgen : h (genericPoint Z) = genericPoint L.C := by
    change h₀ (ι (genericPoint Z)) = _
    rw [a3m_cycleComponentι_genericPoint, hy]
  set φ := a3m_pullbackFF h hgen L.t
  have hφ : φ ≠ 0 := a3m_pullbackFF_ne_zero h hgen L.t L.t_ne_zero
  have hP : a2_principalCycle T.left ℚ y φ ∈ a2_ratEquivDim T.left ℚ k :=
    AddSubgroup.subset_closure ⟨y, φ, 1, hk, hφ, by
      ext; simp [Function.locallyFinsuppWithin.mapRange_apply]⟩
  refine ⟨a1p_pushforward q.left (a2_principalCycle T.left ℚ y φ),
    a2_pushforward_ratEquiv_aux q ℚ k _ hP, ?_⟩
  -- the coefficient formula
  have hD : ∀ z, (principalDivisor Z φ : AlgebraicCycle Z ℤ) z = Z.ord φ z := fun z => by
    have hfin : (Function.support (ordAt Z φ)).Finite := a3m_ord_support_finite φ hφ
    rw [principalDivisor, dite_eq_left hfin]
    rfl
  have hc : ∀ x', a1p_pushforward q.left (a2_principalCycle T.left ℚ y φ) x' =
      ∑ᶠ z ∈ (ι ≫ q.left) ⁻¹' {x'}, (Z.ord φ z : ℚ) * (a1p_degree q.left (ι z) : ℚ) := by
    intro x'
    rw [a2_principalCycle, a3m_pushforward_intCast, ← a1p_pushforward_comp]
    change ∑ᶠ z ∈ (ι ≫ q.left) ⁻¹' {x'}, _ * (a1p_degree (ι ≫ q.left) z : ℚ) = _
    refine finsum_mem_congr rfl fun z _ => ?_
    rw [Function.locallyFinsuppWithin.mapRange_apply, hD, a1p_degree_comp,
      a3m_degree_closedImmersion ι, mul_one]
  -- facts about a nonzero term
  have hspec : ∀ z : Z, y ⤳ ι z := fun z => by
    have := (genericPoint_specializes z).map ι.continuous
    rwa [a3m_cycleComponentι_genericPoint] at this
  have hterm : ∀ z : Z, (Z.ord φ z : ℚ) * (a1p_degree q.left (ι z) : ℚ) ≠ 0 →
      coheight z = 1 ∧ 0 < a1p_degree q.left (ι z) ∧ (h z ∈ L.Z0 ∨ h z ∈ L.Zinf) ∧
        height (ι z) = k ∧ height (q.left (ι z)) = k := by
    intro z hz
    have hord : Z.ord φ z ≠ 0 := fun h0 => hz (by rw [h0]; simp)
    have hdeg : a1p_degree q.left (ι z) ≠ 0 := fun h0 => hz (by rw [h0]; simp)
    have hz1 : coheight z = 1 := by
      by_contra hne
      exact hord (Scheme.ord_eq_zero_of_coheight_neq_one hne φ)
    have hh : h z ∈ L.Z0 ∨ h z ∈ L.Zinf := by
      by_contra hne
      simp only [not_or] at hne
      obtain ⟨a, ha, hat⟩ := L.unit (h z) hne.1 hne.2
      exact hord (a3m_ord_pullbackFF_eq_zero h hgen L.t z a ha hat)
    have hhk : height (ι z) = k := (a3m_coheight_eq_one_iff T y k hk z).1 hz1
    have hpos : 0 < a1p_degree q.left (ι z) := Nat.pos_of_ne_zero hdeg
    exact ⟨hz1, hpos, hh, hhk, ((a1d_degree_pos_iff q (ι z)).1 hpos).trans hhk⟩
  have hfin : (Function.support fun z : Z =>
      (Z.ord φ z : ℚ) * (a1p_degree q.left (ι z) : ℚ)).Finite := by
    refine (a3m_ord_support_finite φ hφ).subset fun z hz => ?_
    intro h0
    apply hz
    simp only
    rw [h0]
    simp
  have hnonneg : ∀ x', (∀ r, y ⤳ r → height r = k → q.left r = x' → h₀ r ∉ L.Zinf) →
      ∀ z ∈ (ι ≫ q.left) ⁻¹' {x'}, 0 ≤ (Z.ord φ z : ℚ) * (a1p_degree q.left (ι z) : ℚ) := by
    intro x' hH z hzS
    by_cases hz : (Z.ord φ z : ℚ) * (a1p_degree q.left (ι z) : ℚ) = 0
    · rw [hz]
    obtain ⟨hz1, hpos, hh, hhk, -⟩ := hterm z hz
    have hc0 : h z ∈ L.Z0 := hh.resolve_right (hH (ι z) (hspec z) hhk hzS)
    obtain ⟨a, ha, hat⟩ := L.zero (h z) hc0
    have := a3m_ord_pullbackFF_pos h hgen L.t L.t_ne_zero z hz1 a ha hat
    positivity
  refine ⟨fun x' hx' => ?_, fun x' hH => ?_, fun x' hH ⟨r, hyr, hrk, hr0, hqr, hx'k⟩ => ?_⟩
  · rw [hc] at hx'
    obtain ⟨z, hzS, hz⟩ := exists_ne_zero_of_finsum_mem_ne_zero hx'
    obtain ⟨-, -, hh, hhk, hqk⟩ := hterm z hz
    have hqz : q.left (ι z) = x' := hzS
    exact ⟨ι z, hspec z, hhk, hh, hqz, hqz ▸ hqk⟩
  · rw [hc]
    exact finsum_nonneg fun z => finsum_nonneg fun hzS => hnonneg x' hH z hzS
  · rw [hc]
    refine finsum_cond_pos (hnonneg x' hH) ?_ (hfin.subset Set.inter_subset_left)
    · obtain ⟨z, rfl⟩ : r ∈ Set.range ι := by
        rw [range_cycleComponentι]
        exact specializes_iff_mem_closure.1 hyr
      have hz1 : coheight z = 1 := (a3m_coheight_eq_one_iff T y k hk z).2 hrk
      obtain ⟨a, ha, hat⟩ := L.zero (h z) hr0
      have hord := a3m_ord_pullbackFF_pos h hgen L.t L.t_ne_zero z hz1 a ha hat
      have hpos : 0 < a1p_degree q.left (ι z) :=
        (a1d_degree_pos_iff q (ι z)).2 (by rw [hqr, hx'k, hrk])
      refine ⟨z, hqr, ?_⟩
      positivity

end HodgeLean.Adapters
