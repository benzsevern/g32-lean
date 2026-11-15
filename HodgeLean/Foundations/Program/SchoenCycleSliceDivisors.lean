import HodgeLean.Foundations.Program.SchoenCycleResidueSlice
import Mathlib.LinearAlgebra.Projectivization.Basic

/-! # Divisors of the paired differential family
The linear family consists of genuine meromorphic differentials.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Manifold Filter Topology
open TauCeti.Contour
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every member of the paired differential family is linear on each
complex tangent fibre. -/
theorem s2e_pairedDifferentialLinear_fibre_linear
    (hE : Module.finrank ℂ E = 1) {r : ℕ} (w : Fin r → b4c_MeroForm E C hE)
    (θ : b3_HolForm E C) (a : Fin r → ℂ) :
    HurwitzPrymRR_IsLinear (s2e_pairedDifferentialLinear hE w (θ, a)) := by
  classical
  intro p b u v
  have hθ := θ.property.2 p b u v
  have hw (i : Fin r) := (w i).property.1 p b u v
  simp only [s2e_pairedDifferentialLinear, LinearMap.coprod_apply,
    Submodule.subtype_apply, Fintype.linearCombination_apply, Pi.add_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hθ]
  simp only [hw, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_left_comm]
  abel

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The differential family satisfies the existing meromorphic-form
interface, without assuming a pole bound. -/
theorem s2e_pairedDifferentialLinear_isMeroForm
    (hE : Module.finrank ℂ E = 1) {r : ℕ} (w : Fin r → b4c_MeroForm E C hE)
    (θ : b3_HolForm E C) (a : Fin r → ℂ) :
    b4c_IsMeroForm hE (s2e_pairedDifferentialLinear hE w (θ, a)) := by
  classical
  refine ⟨s2e_pairedDifferentialLinear_fibre_linear hE w θ a, ?_⟩
  intro p
  rw [s2e_pairedDifferentialLinear_loc]
  have hm (i : Fin r) : MeromorphicAt (a i • HurwitzPrymRR_loc hE (w i) p) 0 := by
    exact (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => a i) 0).meromorphicAt.smul
      ((w i).property.2 p)
  exact (RiemannRochEichler_loc_analytic hE θ p).meromorphicAt.add
    (MeromorphicAt.sum (s := Finset.univ) (fun i _ => hm i))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A nonzero parameter produces a differential with a nonzero germ,
using either a residue coordinate or a nonzero holomorphic differential. -/
theorem s2e_pairedDifferentialLinear_exists_finite_order
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (θ : b3_HolForm E C) (a : Fin r → ℂ) (hv : (θ, a) ≠ 0) :
    ∃ p, meromorphicOrderAt
      (HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w (θ, a)) p) 0 ≠ ⊤ := by
  classical
  letI : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  by_cases ha : a = 0
  · have hθ : θ ≠ 0 := by
      intro hzero
      exact hv (Prod.ext hzero ha)
    let p : C := Classical.arbitrary C
    refine ⟨p, ?_⟩
    have he : s2e_pairedDifferentialLinear hE w (θ, a) =
        (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) := by
      simp only [s2e_pairedDifferentialLinear, LinearMap.coprod_apply,
        Submodule.subtype_apply, Fintype.linearCombination_apply, ha,
        Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
    rw [he]
    exact RiemannRochAna_hol_order_ne_top hE θ hθ p
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
    change a j ≠ 0 at hj
    have hcoord : b4c_res (hE := hE) (s2e_pairedDifferentialLinear hE w (θ, a)) (x j) = a j := by
      simpa only [mul_one] using s2e_pairedDifferentialLinear_residue_coordinate hE w x 1 hres θ a j
    refine ⟨x j, ?_⟩
    intro htop
    have hz : b4c_res (hE := hE) (s2e_pairedDifferentialLinear hE w (θ, a)) (x j) = 0 := by
      apply residue_eq_zero_of_meromorphicOrderAt_nonneg
      rw [htop]
      exact le_top
    exact hj (hcoord.symm.trans hz)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The divisor of a nonzero paired differential has the canonical degree
of the original curve. -/
theorem s2e_pairedDifferentialLinear_divisor_degree
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (θ : b3_HolForm E C) (a : Fin r → ℂ) (hv : (θ, a) ≠ 0) :
    b4c_deg (b4c_divForm (hE := hE) (s2e_pairedDifferentialLinear hE w (θ, a))) =
      2 * (Module.finrank ℂ (b3_HolForm E C) : ℤ) - 2 := by
  letI : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  let v : b4c_MeroForm E C hE :=
    ⟨s2e_pairedDifferentialLinear hE w (θ, a), s2e_pairedDifferentialLinear_isMeroForm hE w θ a⟩
  have hnonzero : (v : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0 := by
    intro hzero
    apply hv
    apply s2e_pairedDifferentialLinear_injective hE w x hres
    simpa only [map_zero] using hzero
  exact b4c_deg_canonical_aux hE v hnonzero
    (s2e_pairedDifferentialLinear_exists_finite_order hE w x hres θ a hv)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Multiplying a differential by a nonzero scalar preserves its divisor. -/
theorem s2e_divForm_const_smul
    (hE : Module.finrank ℂ E = 1) (f : TangentBundle 𝓘(ℂ, E) C → ℂ)
    (c : ℂ) (hc : c ≠ 0) :
    b4c_divForm (hE := hE) (c • f) = b4c_divForm (hE := hE) f := by
  have he : b4c_ordForm (hE := hE) (c • f) = b4c_ordForm (hE := hE) f := by
    funext p
    unfold b4c_ordForm
    have hloc : HurwitzPrymRR_loc hE (c • f) p = c • HurwitzPrymRR_loc hE f p := rfl
    rw [hloc, meromorphicOrderAt_const_smul_eq_meromorphicOrderAt hc]
  unfold b4c_divForm
  split_ifs with hcf hf hf
  · ext p
    simpa only [Finsupp.onFinset_apply] using congrFun he p
  · exact (hf (by rwa [he] at hcf)).elim
  · exact (hcf (by rwa [he])).elim
  · rfl

/-- The marked simple pole divisor, with multiplicities given by the actual
finite list of marked points.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, pp. 13–14. -/
def s2e_markedPoleDivisor {n : ℕ} (y : Fin n → C) : C →₀ ℤ := by
  classical
  exact ∑ i, Finsupp.single (y i) 1

example (y : Fin 0 → C) : s2e_markedPoleDivisor y = 0 := by
  simp only [s2e_markedPoleDivisor, Finset.univ_eq_empty, Finset.sum_empty]

/-- Distinct marked points each have multiplicity one in the pole divisor. -/
theorem s2e_markedPoleDivisor_apply_of_injective
    {n : ℕ} (y : Fin n → C) (hy : Function.Injective y) (j : Fin n) :
    s2e_markedPoleDivisor y (y j) = 1 := by
  classical
  simp only [s2e_markedPoleDivisor, Finsupp.finset_sum_apply, Finsupp.single_apply,
    hy.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The marked pole divisor has no coefficients outside its marked points. -/
theorem s2e_markedPoleDivisor_apply_outside
    {n : ℕ} (y : Fin n → C) (p : C) (hp : p ∉ Set.range y) :
    s2e_markedPoleDivisor y p = 0 := by
  classical
  rw [s2e_markedPoleDivisor, Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [Finsupp.single_apply, ite_eq_right (show y i ≠ p from fun h => hp ⟨i, h⟩)]

/-- The degree counts the marked points with their actual multiplicities. -/
theorem s2e_markedPoleDivisor_degree
    {n : ℕ} (y : Fin n → C) : b4c_deg (s2e_markedPoleDivisor y) = (n : ℤ) := by
  classical
  let d : (C →₀ ℤ) →+ ℤ :=
    { toFun := b4c_deg
      map_zero' := by simp [b4c_deg]
      map_add' := RiemannRochAna_deg_add }
  change d (∑ i, Finsupp.single (y i) 1) = (n : ℤ)
  rw [map_sum]
  change (∑ i, b4c_deg (Finsupp.single (y i) (1 : ℤ))) = (n : ℤ)
  simp only [b4c_deg, Finsupp.sum_single_index, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- Add the marked simple poles to the divisor of the actual differential.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, pp. 13–14. -/
def s2e_adjustedDifferentialDivisor
    (hE : Module.finrank ℂ E = 1) {r n : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (y : Fin n → C)
    (v : b3_HolForm E C × (Fin r → ℂ)) : C →₀ ℤ :=
  b4c_divForm (hE := hE) (s2e_pairedDifferentialLinear hE w v) + s2e_markedPoleDivisor y

example (hE : Module.finrank ℂ E = 1) {r n : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (y : Fin n → C)
    (v : b3_HolForm E C × (Fin r → ℂ)) :
    s2e_adjustedDifferentialDivisor hE w y v =
      b4c_divForm (hE := hE) (s2e_pairedDifferentialLinear hE w v) + s2e_markedPoleDivisor y := rfl

/-- The adjusted divisor is constant on nonzero scalar multiples of the
parameter vector. -/
theorem s2e_adjustedDifferentialDivisor_smul
    (hE : Module.finrank ℂ E = 1) {r n : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (y : Fin n → C)
    (v : b3_HolForm E C × (Fin r → ℂ)) (c : ℂ) (hc : c ≠ 0) :
    s2e_adjustedDifferentialDivisor hE w y (c • v) =
      s2e_adjustedDifferentialDivisor hE w y v := by
  unfold s2e_adjustedDifferentialDivisor
  rw [map_smul, s2e_divForm_const_smul hE _ c hc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Adding the marked simple poles gives an effective divisor for every
nonzero member of the paired differential family. -/
theorem s2e_adjustedDifferentialDivisor_effective
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {r n : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (y : Fin n → C) (hy : Function.Injective y)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ (HurwitzPrymRR_loc hE (w i) p) 0)
    (v : b3_HolForm E C × (Fin r → ℂ)) (hv : v ≠ 0) :
    ∀ p, 0 ≤ s2e_adjustedDifferentialDivisor hE w y v p := by
  classical
  letI : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  rcases v with ⟨θ, a⟩
  let f : b4c_MeroForm E C hE :=
    ⟨s2e_pairedDifferentialLinear hE w (θ, a), s2e_pairedDifferentialLinear_isMeroForm hE w θ a⟩
  have hg := s2e_pairedDifferentialLinear_exists_finite_order hE w x hres θ a hv
  have hfinite := b4c_meroForm_orderSupport_finite_aux hE f
  have hcoe (p : C) :
      ((b4c_divForm (hE := hE) (s2e_pairedDifferentialLinear hE w (θ, a)) p : ℤ) : WithTop ℤ) =
        meromorphicOrderAt (HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w (θ, a)) p) 0 :=
    RiemannRochAna_coe_divForm_apply hE _ hfinite p (b4c_meroForm_order_ne_top hE f hg p)
  intro p
  change (0 : ℤ) ≤ b4c_divForm (hE := hE) (s2e_pairedDifferentialLinear hE w (θ, a)) p +
    s2e_markedPoleDivisor y p
  by_cases hp : p ∈ Set.range y
  · obtain ⟨j, rfl⟩ := hp
    rw [s2e_markedPoleDivisor_apply_of_injective y hy j]
    have ho := (s2e_pairedDifferentialLinear_simple_poles hE w horder θ a (y j)).2
    have hc : (-1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) := by norm_cast
    rw [← hcoe (y j), hc, WithTop.coe_le_coe] at ho
    omega
  · rw [s2e_markedPoleDivisor_apply_outside y p hp, add_zero]
    have ho := (s2e_pairedDifferentialLinear_analyticAt hE w θ a p
      (fun i => hout i p hp)).meromorphicOrderAt_nonneg
    rw [← hcoe p] at ho
    exact WithTop.coe_le_coe.mp ho

/-- The selected genus equation makes every nonzero adjusted divisor have
the exact degree of the retained symmetric power. -/
theorem s2e_adjustedDifferentialDivisor_degree
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {k r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (y : Fin (2 * r) → C)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C) + 2 * r)
    (v : b3_HolForm E C × (Fin r → ℂ)) (hv : v ≠ 0) :
    b4c_deg (s2e_adjustedDifferentialDivisor hE w y v) = (2 * k : ℕ) := by
  rcases v with ⟨θ, a⟩
  rw [s2e_adjustedDifferentialDivisor, RiemannRochAna_deg_add,
    s2e_pairedDifferentialLinear_divisor_degree hE w x hres θ a hv,
    s2e_markedPoleDivisor_degree]
  have hg : (2 : ℤ) * (k : ℤ) + 2 =
      2 * (Module.finrank ℂ (b3_HolForm E C) : ℤ) + 2 * (r : ℤ) := by exact_mod_cast hgenus
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  omega

/-- The adjusted divisor attached to a projective differential parameter.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, pp. 13–14. -/
def s2e_projectiveDifferentialDivisor
    (hE : Module.finrank ℂ E = 1) {r n : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (y : Fin n → C) :
    Projectivization ℂ (b3_HolForm E C × (Fin r → ℂ)) → (C →₀ ℤ) :=
  Projectivization.lift (fun v => s2e_adjustedDifferentialDivisor hE w y v.val)
    (by
      intro a b t hab
      have ht : t ≠ 0 := by
        intro hzero
        apply a.property
        rw [hab, hzero, zero_smul]
      rw [hab]
      exact s2e_adjustedDifferentialDivisor_smul hE w y b.val t ht)

example (hE : Module.finrank ℂ E = 1) {r n : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (y : Fin n → C)
    (v : b3_HolForm E C × (Fin r → ℂ)) (hv : v ≠ 0) :
    s2e_projectiveDifferentialDivisor hE w y (Projectivization.mk ℂ v hv) =
      s2e_adjustedDifferentialDivisor hE w y v := rfl

/-- The projective divisor assignment retains effectivity without a chosen
nonzero representative. -/
theorem s2e_projectiveDifferentialDivisor_effective
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {r n : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (y : Fin n → C) (hy : Function.Injective y)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ (HurwitzPrymRR_loc hE (w i) p) 0)
    (z : Projectivization ℂ (b3_HolForm E C × (Fin r → ℂ))) :
    ∀ p, 0 ≤ s2e_projectiveDifferentialDivisor hE w y z p := by
  refine Quotient.inductionOn z ?_
  intro v
  exact s2e_adjustedDifferentialDivisor_effective hE w x hres y hy horder hout v.val v.property

/-- The projective divisor assignment has the retained symmetric-power
degree at every projective parameter. -/
theorem s2e_projectiveDifferentialDivisor_degree
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {k r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (y : Fin (2 * r) → C)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C) + 2 * r)
    (z : Projectivization ℂ (b3_HolForm E C × (Fin r → ℂ))) :
    b4c_deg (s2e_projectiveDifferentialDivisor hE w y z) = (2 * k : ℕ) := by
  refine Quotient.inductionOn z ?_
  intro v
  exact s2e_adjustedDifferentialDivisor_degree hE w x hres y hgenus v.val v.property

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Each divisor coefficient of a nonzero family member is the actual
finite meromorphic order of its local differential coefficient. -/
theorem s2e_pairedDifferentialLinear_divisor_order
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (θ : b3_HolForm E C) (a : Fin r → ℂ) (hv : (θ, a) ≠ 0) (p : C) :
    ((b4c_divForm (hE := hE) (s2e_pairedDifferentialLinear hE w (θ, a)) p : ℤ) : WithTop ℤ) =
      meromorphicOrderAt (HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w (θ, a)) p) 0 := by
  letI : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  let f : b4c_MeroForm E C hE :=
    ⟨s2e_pairedDifferentialLinear hE w (θ, a), s2e_pairedDifferentialLinear_isMeroForm hE w θ a⟩
  exact RiemannRochAna_coe_divForm_apply hE f
    (b4c_meroForm_orderSupport_finite_aux hE f) p
    (b4c_meroForm_order_ne_top hE f
      (s2e_pairedDifferentialLinear_exists_finite_order hE w x hres θ a hv) p)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Incidence of the adjusted divisor with a marked point is equivalent
to vanishing of the actual residue there. -/
theorem s2e_adjustedDifferentialDivisor_marked_incidence
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {r n : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (y : Fin n → C) (hy : Function.Injective y)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE (w i) p) 0)
    (θ : b3_HolForm E C) (a : Fin r → ℂ) (hv : (θ, a) ≠ 0) (j : Fin n) :
    0 < s2e_adjustedDifferentialDivisor hE w y (θ, a) (y j) ↔
      b4c_res (hE := hE) (s2e_pairedDifferentialLinear hE w (θ, a)) (y j) = 0 := by
  have hm := s2e_pairedDifferentialLinear_simple_poles hE w horder θ a (y j)
  have hi := (RiemannRochEichler_simple_pole_removable hm.1 hm.2).trans
    hm.1.meromorphicOrderAt_nonneg_iff.symm
  change b4c_res (hE := hE) (s2e_pairedDifferentialLinear hE w (θ, a)) (y j) = 0 ↔
    (0 : WithTop ℤ) ≤ meromorphicOrderAt
      (HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w (θ, a)) (y j)) 0 at hi
  rw [← s2e_pairedDifferentialLinear_divisor_order hE w x hres θ a hv (y j)] at hi
  change b4c_res (hE := hE) (s2e_pairedDifferentialLinear hE w (θ, a)) (y j) = 0 ↔
    ((0 : ℤ) : WithTop ℤ) ≤
      ((b4c_divForm (hE := hE) (s2e_pairedDifferentialLinear hE w (θ, a)) (y j) : ℤ) : WithTop ℤ) at hi
  rw [WithTop.coe_le_coe] at hi
  change (0 : ℤ) < b4c_divForm (hE := hE) (s2e_pairedDifferentialLinear hE w (θ, a)) (y j) +
      s2e_markedPoleDivisor y (y j) ↔ _
  rw [s2e_markedPoleDivisor_apply_of_injective y hy j]
  constructor
  · intro h
    exact hi.mpr (by omega)
  · intro h
    have hd := hi.mp h
    omega

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Both points in a marked pair occur in the adjusted divisor exactly on
the same residue-coordinate hyperplane. -/
theorem s2e_adjustedDifferentialDivisor_paired_incidence
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (y : Fin (2 * r) → C)
    (hy : Function.Injective y)
    (hmatrix : ∀ i j,
      b4c_res (hE := hE) (w i) (y ⟨2 * j.val, by omega⟩) = (if i = j then -1 else 0) ∧
      b4c_res (hE := hE) (w i) (y ⟨2 * j.val + 1, by omega⟩) = (if i = j then 1 else 0))
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE (w i) p) 0)
    (θ : b3_HolForm E C) (a : Fin r → ℂ) (hv : (θ, a) ≠ 0) (j : Fin r) :
    (0 < s2e_adjustedDifferentialDivisor hE w y (θ, a) (y ⟨2 * j.val, by omega⟩) ↔ a j = 0) ∧
    (0 < s2e_adjustedDifferentialDivisor hE w y (θ, a) (y ⟨2 * j.val + 1, by omega⟩) ↔ a j = 0) := by
  have hl : ∀ (i j : Fin r), b4c_res (hE := hE) (w i) (y ⟨2 * j.val, by omega⟩) =
      if i = j then (-1 : ℂ) else 0 := fun i j => (hmatrix i j).1
  have hr : ∀ (i j : Fin r), b4c_res (hE := hE) (w i) (y ⟨2 * j.val + 1, by omega⟩) =
      if i = j then (1 : ℂ) else 0 := fun i j => (hmatrix i j).2
  have hf := s2e_adjustedDifferentialDivisor_marked_incidence hE w
    (fun i : Fin r => y ⟨2 * i.val + 1, by omega⟩) hr y hy horder θ a hv
    ⟨2 * j.val, by omega⟩
  have hs := s2e_adjustedDifferentialDivisor_marked_incidence hE w
    (fun i : Fin r => y ⟨2 * i.val + 1, by omega⟩) hr y hy horder θ a hv
    ⟨2 * j.val + 1, by omega⟩
  rw [s2e_pairedDifferentialLinear_residue_coordinate hE w
    (fun i : Fin r => y ⟨2 * i.val, by omega⟩) (-1) hl θ a j] at hf
  rw [s2e_pairedDifferentialLinear_residue_coordinate hE w
    (fun i : Fin r => y ⟨2 * i.val + 1, by omega⟩) 1 hr θ a j] at hs
  exact ⟨by simpa only [mul_neg_one, neg_eq_zero] using hf,
    by simpa only [mul_one] using hs⟩

end HodgeLean.Foundations.Program
