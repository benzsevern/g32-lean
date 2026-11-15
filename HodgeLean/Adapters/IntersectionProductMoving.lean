import HodgeLean.Adapters.IntersectionProductMovingDimension
import HodgeLean.Adapters.IntersectionProductMovingGlue

/-! # Chow's moving lemma: the excess induction

Stage A3.2 of track A3. The moving lemma `a3i_moving` is reduced here to two geometric
statements about a smooth projective variety `X`:
* the dimension inequality for intersections (`a3m_coheight_component_le_of_smooth`, in
  `HodgeLean.Adapters.IntersectionProductMovingDimension`): every irreducible component of
  `closure {u} ∩ closure {v}` has codimension at most `codim u + codim v`;
* Roberts' step (`a3m_roberts_step`, in `HodgeLean.Adapters.IntersectionProductMovingRoberts`):
  a prime cycle of codimension `p` whose excess against a finite set of subvarieties is at most
  `k + 1` is rationally equivalent to a cycle of codimension `p` all of whose components have
  excess at most `k`.

The excess of `closure {u}` against `closure {v}` is measured by `a3m_ExcessLE`: every component
`closure {w}` of the intersection has `codim u + codim v ≤ codim w + k`. Excess `0` together with
the dimension inequality is proper intersection. The induction on `k` and the bookkeeping of
rational coefficients are proved below, as is the passage from a moving family over a pointed curve
to Roberts' step (`a3m_movable_of_family`).

Source: J. Roberts, *Chow's moving lemma*, in *Algebraic Geometry, Oslo 1970*, Wolters-Noordhoff
(1972), 89–96; Fulton, *Intersection Theory*, second edition, §11.4 and Example 11.4.1.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace HodgeLean.Adapters

universe u

/-! ## Rational multiples of cycles -/

/-- The cycle `r • c`, coefficientwise multiplication by `r`. -/
def a3m_smul {X : Scheme.{u}} (r : ℚ) (c : AlgebraicCycle X ℚ) : AlgebraicCycle X ℚ :=
  c.mapRange (r * ·) (mul_zero r)

@[simp] theorem a3m_smul_apply {X : Scheme.{u}} (r : ℚ) (c : AlgebraicCycle X ℚ) (x : X) :
    a3m_smul r c x = r * c x := rfl

/-- Multiplication by `r` as an additive endomorphism of cycles. -/
def a3m_smulHom (X : Scheme.{u}) (r : ℚ) : AlgebraicCycle X ℚ →+ AlgebraicCycle X ℚ where
  toFun := a3m_smul r
  map_zero' := by ext; simp
  map_add' c d := by ext; simp [mul_add]

theorem a3m_smul_sub {X : Scheme.{u}} (r : ℚ) (c d : AlgebraicCycle X ℚ) :
    a3m_smul r (c - d) = a3m_smul r c - a3m_smul r d :=
  (a3m_smulHom X r).map_sub c d

theorem a3m_smul_sum {X : Scheme.{u}} {ι : Type*} (s : Finset ι) (r : ℚ)
    (F : ι → AlgebraicCycle X ℚ) :
    a3m_smul r (∑ i ∈ s, F i) = ∑ i ∈ s, a3m_smul r (F i) :=
  map_sum (a3m_smulHom X r) F s

theorem a3m_sum_apply {X : Scheme.{u}} {ι : Type*} (s : Finset ι)
    (F : ι → AlgebraicCycle X ℚ) (x : X) : (∑ i ∈ s, F i) x = ∑ i ∈ s, F i x := by
  rw [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]

/-- A cycle with finite support is the sum of its coefficients times its points. -/
theorem a3m_eq_sum_single {X : Scheme.{u}} [DecidableEq X] (c : AlgebraicCycle X ℚ)
    (s : Finset X) (hs : ∀ x ∉ s, c x = 0) :
    c = ∑ x ∈ s, a3m_smul (c x) (Function.locallyFinsuppWithin.single x 1) := by
  ext y
  rw [a3m_sum_apply]
  simp only [a3m_smul_apply, Function.locallyFinsuppWithin.single_apply, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hy
  · rfl
  · exact hs y hy

/-! ## Closure properties -/

theorem a3m_smul_mem_ratEquivDim (X : Scheme.{u}) [IsLocallyNoetherian X] (k : ℕ) (r : ℚ)
    {c : AlgebraicCycle X ℚ} (hc : c ∈ a2_ratEquivDim X ℚ k) :
    a3m_smul r c ∈ a2_ratEquivDim X ℚ k := by
  change c ∈ (a2_ratEquivDim X ℚ k).comap (a3m_smulHom X r)
  refine (AddSubgroup.closure_le _).2 ?_ hc
  rintro _ ⟨w, φ, r', hw, hφ, rfl⟩
  refine AddSubgroup.subset_closure ⟨w, φ, r * r', hw, hφ, ?_⟩
  ext x
  simp [a3m_smulHom, Function.locallyFinsuppWithin.mapRange_apply, mul_assoc]

/-- `a3i_ratAll X` is stable under rational multiples. -/
theorem a3m_smul_mem_ratAll (X : Scheme.{u}) [IsLocallyNoetherian X] (r : ℚ)
    {c : AlgebraicCycle X ℚ} (hc : c ∈ a3i_ratAll X) : a3m_smul r c ∈ a3i_ratAll X := by
  change c ∈ (a3i_ratAll X).comap (a3m_smulHom X r)
  refine (show a3i_ratAll X ≤ _ from iSup_le fun k => ?_) hc
  intro c hc
  exact (le_iSup (fun k : ℕ => a2_ratEquivDim X ℚ k) k) (a3m_smul_mem_ratEquivDim X k r hc)

theorem a3m_smul_mem_codimCycles (X : Scheme.{u}) (p : ℕ) (r : ℚ)
    {c : AlgebraicCycle X ℚ} (hc : c ∈ a3i_codimCycles X ℚ p) :
    a3m_smul r c ∈ a3i_codimCycles X ℚ p := fun x hx =>
  hc x (fun h => hx (by simp [h]))

theorem a3m_single_mem_codimCycles (X : Scheme.{u}) [DecidableEq X] (p : ℕ) (x : X)
    (hx : Order.coheight x = p) :
    Function.locallyFinsuppWithin.single x (1 : ℚ) ∈ a3i_codimCycles X ℚ p := by
  intro y hy
  rw [Function.locallyFinsuppWithin.single_apply] at hy
  split_ifs at hy with h
  · rw [h, hx]
  · exact (hy rfl).elim

/-- A nonzero coefficient of a finite sum comes from a summand. -/
theorem a3m_exists_of_sum_apply_ne_zero {X : Scheme.{u}} {ι : Type*} (s : Finset ι)
    (F : ι → AlgebraicCycle X ℚ) (x : X) (h : (∑ i ∈ s, F i) x ≠ 0) :
    ∃ i ∈ s, F i x ≠ 0 := by
  rw [a3m_sum_apply] at h
  exact Finset.exists_ne_zero_of_sum_ne_zero h

/-- Cycles on a Noetherian scheme have finite support. -/
theorem a3m_support_finite {X : Scheme.{u}} [IsNoetherian X] (c : AlgebraicCycle X ℚ) :
    (Function.support c).Finite :=
  Function.locallyFinsupp.finite_support c

/-- On a locally Noetherian scheme every point has finite codimension. -/
theorem a3m_coheight_ne_top (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    Order.coheight x ≠ ⊤ := by
  have h := ringKrullDim_stalk_eq_coheight x
  have h2 := ringKrullDim_lt_top (R := X.presheaf.stalk x)
  intro htop
  rw [h, htop] at h2
  exact lt_irrefl _ h2

/-! ## Excess -/

/-- The excess of `closure {u}` against each `closure {v}`, `v ∈ S`, is at most `k`: every
irreducible component `closure {w}` of the scheme-theoretic intersection has
`codim u + codim v ≤ codim w + k`. With `k = 0` and the dimension inequality on a smooth variety
this is proper intersection.
Source: J. Roberts, *Chow's moving lemma* (1972), the excess `e(V, W)`; Fulton, *Intersection
Theory*, second edition, Example 11.4.1. -/
def a3m_ExcessLE (X : Scheme.{u}) (S : Set X) (u : X) (k : ℕ) : Prop :=
  ∀ v ∈ S, ∀ w : (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme,
    closure ({w} : Set (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme) ∈
      irreducibleComponents (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme →
    Order.coheight u + Order.coheight v ≤
      Order.coheight ((ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subschemeι w) + k

theorem a3m_excessLE_mono {X : Scheme.{u}} {S : Set X} {u : X} {k k' : ℕ} (hk : k ≤ k')
    (h : a3m_ExcessLE X S u k) : a3m_ExcessLE X S u k' := fun v hv w hw =>
  (h v hv w hw).trans (by gcongr)

/-- Every point has finite excess against a finite set, on a locally Noetherian scheme. -/
theorem a3m_exists_excessLE (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Set X)
    (hS : S.Finite) (u : X) : ∃ k, a3m_ExcessLE X S u k := by
  refine ⟨(Order.coheight u).toNat + ∑ v ∈ hS.toFinset, (Order.coheight v).toNat, ?_⟩
  intro v hv w _
  have hu := ENat.natCast_toNat (a3m_coheight_ne_top X u)
  have hv' := ENat.natCast_toNat (a3m_coheight_ne_top X v)
  have hle : (Order.coheight v).toNat ≤ ∑ v ∈ hS.toFinset, (Order.coheight v).toNat :=
    Finset.single_le_sum (f := fun v => (Order.coheight v).toNat) (fun _ _ => Nat.zero_le _)
      (hS.mem_toFinset.2 hv)
  calc Order.coheight u + Order.coheight v
      = (((Order.coheight u).toNat + (Order.coheight v).toNat : ℕ) : ℕ∞) := by
        rw [Nat.cast_add, hu, hv']
    _ ≤ (((Order.coheight u).toNat + ∑ v ∈ hS.toFinset, (Order.coheight v).toNat : ℕ) : ℕ∞) := by
        exact_mod_cast Nat.add_le_add_left hle _
    _ ≤ _ := le_add_self

/-- Excess `0` and the dimension inequality give proper intersection. -/
theorem a3m_meetProperly_of_excessLE_zero {X : Scheme.{u}} {S : Set X} {u v : X}
    (hineq : ∀ w : (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme,
      closure ({w} : Set (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme →
      Order.coheight ((ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subschemeι w) ≤
        Order.coheight u + Order.coheight v)
    (h : a3m_ExcessLE X S u 0) (hv : v ∈ S) : a3i_MeetProperly X u v := fun w hw =>
  le_antisymm (hineq w hw) (by simpa using h v hv w hw)

/-! ## The induction on the excess -/

section Induction

variable (X : Scheme.{u}) [IsNoetherian X] (S : Set X) (p : ℕ)

/-- A point `u` of codimension `p` can be moved to excess `k` against `S`: some cycle of
codimension `p`, rationally equivalent to `[closure {u}]`, has all its components of excess at
most `k`. -/
def a3m_Movable (k : ℕ) (u : X) : Prop :=
  ∃ γ ∈ a3i_codimCycles X ℚ p,
    γ - (by classical exact Function.locallyFinsuppWithin.single u 1) ∈ a3i_ratAll X ∧
      ∀ x, γ x ≠ 0 → a3m_ExcessLE X S x k

/-- Iterating a step that lowers the excess by one moves every point to excess `0`. -/
theorem a3m_movable_zero_of_step
    (hstep : ∀ (k : ℕ) (u : X), Order.coheight u = p → a3m_ExcessLE X S u (k + 1) →
      a3m_Movable X S p k u) :
    ∀ (k : ℕ) (u : X), Order.coheight u = p → a3m_ExcessLE X S u k → a3m_Movable X S p 0 u := by
  classical
  intro k
  induction k with
  | zero =>
    intro u hu he
    refine ⟨Function.locallyFinsuppWithin.single u 1,
      a3m_single_mem_codimCycles X p u hu, ?_, ?_⟩
    · convert (a3i_ratAll X).zero_mem using 1
      exact sub_self _
    · intro x hx
      rw [Function.locallyFinsuppWithin.single_apply] at hx
      split_ifs at hx with h
      · exact h ▸ he
      · exact (hx rfl).elim
  | succ k ih =>
    intro u hu he
    obtain ⟨γ, hγp, hγr, hγe⟩ := hstep k u hu he
    choose! g hgp hgr hge using ih
    set s := (a3m_support_finite γ).toFinset
    have hs : ∀ x ∉ s, γ x = 0 := fun x hx => by
      simpa [s] using hx
    refine ⟨∑ x ∈ s, a3m_smul (γ x) (g x), ?_, ?_, ?_⟩
    · refine AddSubgroup.sum_mem _ fun x hx => a3m_smul_mem_codimCycles X p _ ?_
      have hx' : γ x ≠ 0 := by simpa [s] using hx
      have hcx : Order.coheight x = p := hγp x hx'
      exact hgp x hcx (hγe x hx')
    · have hdec := a3m_eq_sum_single γ s hs
      have : (∑ x ∈ s, a3m_smul (γ x) (g x)) - Function.locallyFinsuppWithin.single u 1 =
          (∑ x ∈ s, a3m_smul (γ x) (g x - Function.locallyFinsuppWithin.single x 1)) +
            (γ - Function.locallyFinsuppWithin.single u 1) := by
        simp only [a3m_smul_sub, Finset.sum_sub_distrib]
        rw [← hdec]
        abel
      rw [this]
      refine add_mem (AddSubgroup.sum_mem _ fun x hx => a3m_smul_mem_ratAll X _ ?_) hγr
      have hx' : γ x ≠ 0 := by simpa [s] using hx
      exact hgr x (hγp x hx') (hγe x hx')
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := a3m_exists_of_sum_apply_ne_zero s _ y hy
      have hx' : γ x ≠ 0 := by simpa [s] using hx
      have hgy : g x y ≠ 0 := fun h => hxy (by simp [h])
      exact hge x (hγp x hx') (hγe x hx') y hgy

end Induction

/-- The moving lemma from the dimension inequality and Roberts' step, on a Noetherian scheme. -/
theorem a3m_moving_of_step (X : Scheme.{u}) [IsNoetherian X] (p : ℕ)
    (hineq : ∀ (u v : X) (w : (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme),
      closure ({w} : Set (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subscheme →
      Order.coheight ((ccm3_primeIdeal X u ⊔ ccm3_primeIdeal X v).subschemeι w) ≤
        Order.coheight u + Order.coheight v)
    (hstep : ∀ (S : Set X), S.Finite → ∀ (k : ℕ) (u : X), Order.coheight u = p →
      a3m_ExcessLE X S u (k + 1) → a3m_Movable X S p k u)
    (α β : AlgebraicCycle X ℚ) (hα : α ∈ a3i_codimCycles X ℚ p) :
    ∃ α' ∈ a3i_codimCycles X ℚ p, α' - α ∈ a3i_ratAll X ∧
      a3i_CyclesMeetProperly X α' β := by
  classical
  set S := Function.support β
  have hS : S.Finite := a3m_support_finite β
  have hmove : ∀ u : X, Order.coheight u = p → a3m_Movable X S p 0 u := fun u hu =>
    let ⟨k, hk⟩ := a3m_exists_excessLE X S hS u
    a3m_movable_zero_of_step X S p (hstep S hS) k u hu hk
  choose! g hgp hgr hge using hmove
  set s := (a3m_support_finite α).toFinset
  have hs : ∀ x ∉ s, α x = 0 := fun x hx => by simpa [s] using hx
  refine ⟨∑ x ∈ s, a3m_smul (α x) (g x), ?_, ?_, ?_⟩
  · refine AddSubgroup.sum_mem _ fun x hx => a3m_smul_mem_codimCycles X p _ ?_
    have hx' : α x ≠ 0 := by simpa [s] using hx
    exact hgp x (hα x hx')
  · have hdec := a3m_eq_sum_single α s hs
    have : (∑ x ∈ s, a3m_smul (α x) (g x)) - α =
        ∑ x ∈ s, a3m_smul (α x) (g x - Function.locallyFinsuppWithin.single x 1) := by
      simp only [a3m_smul_sub, Finset.sum_sub_distrib]
      rw [← hdec]
    rw [this]
    refine AddSubgroup.sum_mem _ fun x hx => a3m_smul_mem_ratAll X _ ?_
    have hx' : α x ≠ 0 := by simpa [s] using hx
    exact hgr x (hα x hx')
  · intro y v hy hv
    obtain ⟨x, hx, hxy⟩ := a3m_exists_of_sum_apply_ne_zero s _ y hy
    have hx' : α x ≠ 0 := by simpa [s] using hx
    have hgy : g x y ≠ 0 := fun h => hxy (by simp [h])
    exact a3m_meetProperly_of_excessLE_zero (hineq y v) (hge x (hα x hx') y hgy) hv

/-! ## Moving families -/

/-- A family moving `closure {u}` (of dimension `d` and codimension `p`) to excess `k` against
`S`: a proper `q : T → X`, a pointed curve `C` with a map `h₀ : T → C`, and finitely many
subvarieties `closure {y}` of `T` of dimension `d + 1` dominating `C`, such that
* some `closure {y}` contains a point of dimension `d` over `Z₀` lying over `u`;
* no point of any `closure {y}` over `Z_∞` lies over `u`;
* every point of dimension `d` of `X` under a point of some `closure {y}` over `Z₀` or `Z_∞`,
  other than `u`, has codimension `p` and excess at most `k` against `S`.
In Roberts' construction `T = X × ℙ¹`, the fibre over `Z₀ = {0}` is the cone `C_L(V) ∩ X` and
the fibre over `Z_∞ = {1}` a general translate of the cone met with `X`.
Source: J. Roberts, *Chow's moving lemma* (1972); Fulton, *Intersection Theory*, second
edition, §1.6 and Example 11.4.1. -/
structure a3m_MovingFamily (X : Over (Spec ↧ℂ)) (S : Set X.left) (p k d : ℕ) (u : X.left) where
  /-- The total space. -/
  T : Over (Spec ↧ℂ)
  [lft : LocallyOfFiniteType T.hom]
  [qc : QuasiCompact T.hom]
  [noeth : IsNoetherian T.left]
  /-- The proper map to `X`. -/
  q : T ⟶ X
  [proper : IsProper q.left]
  /-- The parameter curve. -/
  L : a3m_PointedCurve
  /-- The map to the parameter curve. -/
  h₀ : T.left ⟶ L.C
  /-- The generic points of the members of the family. -/
  Y : Finset T.left
  dom : ∀ y ∈ Y, h₀ y = genericPoint L.C
  dim : ∀ y ∈ Y, Order.height y = (d + 1 : ℕ)
  start : ∃ y ∈ Y, ∃ r, y ⤳ r ∧ Order.height r = d ∧ h₀ r ∈ L.Z0 ∧ q.left r = u
  avoid : ∀ y ∈ Y, ∀ r, y ⤳ r → h₀ r ∈ L.Zinf → q.left r ≠ u
  good : ∀ y ∈ Y, ∀ r, y ⤳ r → (h₀ r ∈ L.Z0 ∨ h₀ r ∈ L.Zinf) →
    Order.height (q.left r) = d → q.left r ≠ u →
      a3m_ExcessLE X.left S (q.left r) k ∧ Order.coheight (q.left r) = p

attribute [instance] a3m_MovingFamily.lft a3m_MovingFamily.qc a3m_MovingFamily.noeth
  a3m_MovingFamily.proper

/-- A moving family moves `closure {u}` to excess `k`. -/
theorem a3m_movable_of_family (X : Over (Spec ↧ℂ)) [IsNoetherian X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (S : Set X.left) (p k d : ℕ) (u : X.left)
    (hd : Order.height u = d) (F : a3m_MovingFamily X S p k d u) :
    a3m_Movable X.left S p k u := by
  classical
  have hglue := fun y (hy : y ∈ F.Y) =>
    a3m_family_glue F.q F.L F.h₀ d y (F.dom y hy) (F.dim y hy)
  choose! c hcR hc1 hc2 hc3 using hglue
  set C := ∑ y ∈ F.Y, c y
  have hCR : C ∈ a3i_ratAll X.left := AddSubgroup.sum_mem _ fun y hy =>
    (le_iSup (fun k : ℕ => a2_ratEquivDim X.left ℚ k) d) (hcR y hy)
  have havoid : ∀ y ∈ F.Y, ∀ r, y ⤳ r → Order.height r = d → F.q.left r = u →
      F.h₀ r ∉ F.L.Zinf := fun y hy r hyr _ hqr hinf => F.avoid y hy r hyr hinf hqr
  have hCu : 0 < C u := by
    rw [a3m_sum_apply]
    obtain ⟨y₀, hy₀, r, hyr, hrd, hr0, hqr⟩ := F.start
    refine Finset.sum_pos' (fun y hy => hc2 y hy u (havoid y hy)) ⟨y₀, hy₀, ?_⟩
    exact hc3 y₀ hy₀ u (havoid y₀ hy₀) ⟨r, hyr, hrd, hr0, hqr, hd⟩
  set γ := Function.locallyFinsuppWithin.single u (1 : ℚ) - a3m_smul (C u)⁻¹ C
  have hγu : γ u = 0 := by
    simp [γ, inv_mul_cancel₀ hCu.ne']
  have hγ : ∀ x, γ x ≠ 0 → a3m_ExcessLE X.left S x k ∧ Order.coheight x = p := by
    intro x hx
    have hxu : x ≠ u := fun h => hx (h ▸ hγu)
    have hCx : C x ≠ 0 := by
      intro h0
      apply hx
      simp [γ, hxu, h0]
    obtain ⟨y, hy, hyx⟩ := a3m_exists_of_sum_apply_ne_zero F.Y c x hCx
    obtain ⟨r, hyr, -, hr, hqr, hxd⟩ := hc1 y hy x hyx
    subst hqr
    exact F.good y hy r hyr hr hxd hxu
  refine ⟨γ, fun x hx => (hγ x hx).2, ?_, fun x hx => (hγ x hx).1⟩
  have : γ - Function.locallyFinsuppWithin.single u 1 = -a3m_smul (C u)⁻¹ C := by
    simp only [γ]
    abel
  rw [this]
  exact neg_mem (a3m_smul_mem_ratAll X.left _ hCR)

/-! ## Codimension zero -/

/-- On an irreducible scheme the generic point meets every point properly: its excess is `0`. -/
theorem a3m_excessLE_zero_of_coheight_eq_zero {X : Scheme.{u}} [IrreducibleSpace X] (S : Set X)
    (u : X) (hu : Order.coheight u = 0) : a3m_ExcessLE X S u 0 := by
  intro v _ w hw
  obtain ⟨-, hvw, hmin⟩ := a3m_component_spec u v w hw
  have hgen : u = genericPoint X := by
    have hmax : IsMax u := Order.coheight_eq_zero.1 hu
    have h1 : u ≤ genericPoint X := by
      rw [Scheme.le_iff_specializes]
      exact genericPoint_specializes u
    have h2 : genericPoint X ≤ u := hmax h1
    rw [Scheme.le_iff_specializes] at h1 h2
    exact (h2.antisymm h1).eq
  have huv : u ⤳ v := hgen ▸ genericPoint_specializes v
  have := hmin v huv specializes_rfl hvw
  rw [← this, hu, zero_add, Nat.cast_zero, add_zero]

end HodgeLean.Adapters
