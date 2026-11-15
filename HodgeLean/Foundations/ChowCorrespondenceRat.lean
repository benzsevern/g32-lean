import HodgeLean.Adapters.ChowCorrespondenceDefs
import HodgeLean.Adapters.CyclePushforwardDimension
import HodgeLean.Adapters.KleimanCoheightCharts

/-! # Rational equivalence: dimension of principal cycles and the point

Helpers for lane A2 (rational equivalence). On an integral scheme of finite type over `ℂ`,
`height z + coheight z` is the height of the generic point; the closed immersion
`cycleComponentι X w` preserves heights. So a principal cycle `[div φ]` on a `(k + 1)`-dimensional
subvariety is a `k`-cycle. On `Spec ℂ` every point has height `0`, so `Rat_k` is trivial there.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial HodgeLean.Foundations.Curves Order

namespace HodgeLean.Adapters

/-- On an integral scheme of finite type over `ℂ`, height plus coheight of a point is the height of
the generic point.
Source: Hartshorne, *Algebraic Geometry*, II, Exercise 3.20. -/
theorem a2r_height_add_coheight (Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType Y.hom]
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
abbrev a2r_component (X : Over (Spec ↧ℂ)) (w : X.left) : Over (Spec ↧ℂ) :=
  Over.mk (cycleComponentι X.left w ≫ X.hom)

instance a2r_component_locallyOfFiniteType (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (w : X.left) : LocallyOfFiniteType (a2r_component X w).hom := by
  change LocallyOfFiniteType (cycleComponentι X.left w ≫ X.hom)
  infer_instance

instance a2r_component_isIntegral (X : Over (Spec ↧ℂ)) (w : X.left) :
    IsIntegral (a2r_component X w).left :=
  inferInstanceAs (IsIntegral (cycleComponent X.left w))

/-- The closed immersion of `closure {w}` preserves heights. -/
theorem a2r_height_cycleComponentι (X : Scheme) (w : X) (z : cycleComponent X w) :
    height (cycleComponentι X w z) = height z := by
  rw [← height_orderIso (cycleComponentOrderIsoIic X w) z]
  exact (height_eq_of_strictMono (Subtype.val : Set.Iic w → X) (fun _ _ h => h)
    (fun a b hb => ⟨⟨b, hb.le.trans a.2⟩, hb, rfl⟩) (cycleComponentOrderIsoIic X w z)).symm

/-- The generic point of `closure {w}` maps to `w`. -/
theorem a2r_cycleComponentι_genericPoint (X : Scheme) (w : X) :
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
theorem a2r_height_cycleComponent_genericPoint (X : Scheme) (w : X) :
    height (genericPoint (cycleComponent X w)) = height w := by
  rw [← a2r_height_cycleComponentι, a2r_cycleComponentι_genericPoint]

/-- A point with a nonzero coefficient in `f_* c` is the image of a point of the support of `c`. -/
theorem a2r_exists_of_pushforward_ne_zero {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f]
    {R : Type*} [Semiring R] (c : AlgebraicCycle X R) (y : Y) (h : a1p_pushforward f c y ≠ 0) :
    ∃ x, f x = y ∧ c x ≠ 0 := by
  by_contra! hne
  apply h
  change ∑ᶠ x ∈ f ⁻¹' {y}, c x * (a1p_degree f x : R) = 0
  exact finsum_mem_eq_zero_of_forall_eq_zero fun x hx => by rw [hne x hx, zero_mul]

/-- `Rat_k X ≤ Z_k X`. -/
theorem a2r_ratEquivDim_le_dimCycles (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (R : Type*) [Ring R] (k : ℕ) :
    a2_ratEquivDim X.left R k ≤ a2_dimCycles X.left R k := by
  rw [a2_ratEquivDim, AddSubgroup.closure_le]
  rintro c ⟨w, φ, r, hw, -, rfl⟩ x hx
  have hx1 : a2_principalCycle X.left R w φ x ≠ 0 := by
    intro h0
    apply hx
    change r * _ = 0
    rw [h0, mul_zero]
  have hx2 : a1p_pushforward (cycleComponentι X.left w)
      (principalDivisor (cycleComponent X.left w) φ :
        AlgebraicCycle (cycleComponent X.left w) ℤ) x ≠ 0 := by
    intro h0
    apply hx1
    change ((_ : ℤ) : R) = 0
    rw [h0, Int.cast_zero]
  obtain ⟨z, rfl, hz⟩ := a2r_exists_of_pushforward_ne_zero _ _ _ hx2
  have hcoh : coheight z = 1 := (principalDivisor (cycleComponent X.left w) φ).2 hz
  have hsum := a2r_height_add_coheight (a2r_component X w) z
  change height z + coheight z = height (genericPoint (cycleComponent X.left w)) at hsum
  rw [a2r_height_cycleComponent_genericPoint, hw, hcoh] at hsum
  rw [a2r_height_cycleComponentι]
  have : height z + 1 = (k : ℕ∞) + 1 := by rw [hsum]; norm_cast
  exact WithTop.add_right_cancel ENat.one_ne_top this

/-- Every point of `Spec ℂ` has height `0`. -/
theorem a2r_height_spec_field (x : Spec ↧ℂ) : Order.height x = 0 := by
  rw [Order.height_eq_zero]
  intro y _
  exact le_of_eq (Subsingleton.elim x y)

/-- `Rat_k (Spec ℂ) = ⊥`. -/
theorem a2r_ratEquivDim_point (R : Type*) [Ring R] (k : ℕ) :
    a2_ratEquivDim (Spec ↧ℂ) R k = ⊥ := by
  rw [a2_ratEquivDim, AddSubgroup.closure_eq_bot_iff]
  rintro c ⟨w, φ, r, hw, -, -⟩
  rw [a2r_height_spec_field] at hw
  exact absurd hw (by exact_mod_cast (Nat.succ_ne_zero k).symm)

/-- For a scheme over `Spec ℂ`, the degree of a cycle is the coefficient of its pushforward to the
point.
Source: Stacks Project, Tag 0AZ2; Mathlib, `AlgebraicCycle.degree`. -/
theorem a2r_degree_eq_pushforward {X : Scheme} (f : X ⟶ Spec ↧ℂ) [CompactSpace X] [QuasiCompact f]
    {R : Type*} [CommRing R] (c : AlgebraicCycle X R) (p : Spec ↧ℂ) :
    AlgebraicCycle.degree f c = a1p_pushforward f c p := by
  rw [AlgebraicCycle.degree_apply]
  change _ = ∑ᶠ x ∈ f ⁻¹' {p}, c x * (a1p_degree f x : R)
  have : f ⁻¹' {p} = Set.univ := Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _
  rw [this, finsum_mem_univ]
  refine finsum_congr fun x => ?_
  rw [nsmul_eq_mul, mul_comm]
  rfl

end HodgeLean.Adapters
