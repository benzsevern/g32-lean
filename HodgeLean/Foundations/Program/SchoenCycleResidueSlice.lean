import HodgeLean.Foundations.Program.RiemannRoch
import HodgeLean.Foundations.Program.SchoenCycleMeromorphicBounds

/-! # Differential residue coordinates for the paired slice
Third-kind differentials supply the independent paired residue coordinates.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Manifold Filter Topology
open TauCeti.Contour
open scoped ContDiff BigOperators
namespace HodgeLean.Foundations.Program

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- Two distinct points carry opposite unit residues on a differential
analytic everywhere else and with at most simple poles. -/
theorem s2e_regular_two_point_differential
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (p q : C) (hpq : p ≠ q) :
    ∃ w : b4c_MeroForm E C hE,
      b4c_res (hE := hE) w p = -1 ∧ b4c_res (hE := hE) w q = 1 ∧
      (∀ x, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE w x) 0) ∧
      ∀ x, x ≠ p → x ≠ q → AnalyticAt ℂ (HurwitzPrymRR_loc hE w x) 0 := by
  obtain ⟨w, hp, hq, ho, hout⟩ := RiemannRochEichler_third_kind hE p q hpq
  obtain ⟨v, he, hva, _⟩ := RiemannRochEichler_regularize_off_poles hE w ({p, q} : Set C)
    (by intro x hx; exact hout x (fun h => hx (Or.inl h)) (fun h => hx (Or.inr h)))
  refine ⟨v, (residue_congr_nhdsNE (he p)).trans hp,
    (residue_congr_nhdsNE (he q)).trans hq, ?_, ?_⟩
  · intro x
    rw [meromorphicOrderAt_congr (he x)]
    exact ho x
  · intro x hxp hxq
    exact hva x (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using (And.intro hxp hxq))

/-- Distinct paired points give meromorphic differentials with the identity
paired residue matrix and no poles outside their respective pairs. -/
theorem s2e_paired_residue_differentials
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (r : ℕ) (y : Fin (2 * r) → C)
    (hy : Function.Injective y) :
    ∃ w : Fin r → b4c_MeroForm E C hE,
      (∀ i x, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE (w i) x) 0) ∧
      (∀ i x, x ≠ y ⟨2 * i.val, by omega⟩ → x ≠ y ⟨2 * i.val + 1, by omega⟩ →
        AnalyticAt ℂ (HurwitzPrymRR_loc hE (w i) x) 0) ∧
      ∀ i j,
        b4c_res (hE := hE) (w i) (y ⟨2 * j.val, by omega⟩) = (if i = j then -1 else 0) ∧
        b4c_res (hE := hE) (w i) (y ⟨2 * j.val + 1, by omega⟩) = (if i = j then 1 else 0) := by
  classical
  have hpq (i : Fin r) : y ⟨2 * i.val, by omega⟩ ≠ y ⟨2 * i.val + 1, by omega⟩ := by
    intro he
    have h := congrArg Fin.val (hy he)
    dsimp only at h
    omega
  choose w hw using fun i => s2e_regular_two_point_differential hE
    (y ⟨2 * i.val, by omega⟩) (y ⟨2 * i.val + 1, by omega⟩) (hpq i)
  refine ⟨w, (fun i => (hw i).2.2.1), (fun i => (hw i).2.2.2), ?_⟩
  intro i j
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, ite_eq_left rfl]
    exact And.intro (hw i).1 (hw i).2.1
  · rw [ite_eq_right hij, ite_eq_right hij]
    constructor
    · apply residue_eq_zero_of_analyticAt
      apply (hw i).2.2.2
      · intro he
        have h := congrArg Fin.val (hy he)
        have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
        dsimp only at h
        omega
      · intro he
        have h := congrArg Fin.val (hy he)
        dsimp only at h
        omega
    · apply residue_eq_zero_of_analyticAt
      apply (hw i).2.2.2
      · intro he
        have h := congrArg Fin.val (hy he)
        dsimp only at h
        omega
      · intro he
        have h := congrArg Fin.val (hy he)
        have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
        dsimp only at h
        omega

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Residues of finite meromorphic differential combinations are computed
by the same finite combination of their residues. -/
theorem s2e_residue_linear_combination
    (hE : Module.finrank ℂ E = 1) {ι : Type*} [Fintype ι]
    (w : ι → b4c_MeroForm E C hE) (a : ι → ℂ) (p : C) :
    b4c_res (hE := hE) (∑ i, a i • (w i : TangentBundle 𝓘(ℂ, E) C → ℂ)) p =
      ∑ i, a i * b4c_res (hE := hE) (w i) p := by
  classical
  have hloc : HurwitzPrymRR_loc hE
      (∑ i, a i • (w i : TangentBundle 𝓘(ℂ, E) C → ℂ)) p =
      ∑ i, (fun z => a i * HurwitzPrymRR_loc hE (w i) p z) := by
    funext z
    simp only [HurwitzPrymRR_loc, b4cov_coef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  unfold b4c_res
  rw [hloc, residue_sum (f := fun i z => a i * HurwitzPrymRR_loc hE (w i) p z) Finset.univ (fun i _ => (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => a i) 0).meromorphicAt.mul
    ((w i).property.2 p))]
  simp only [residue_const_mul]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A differential family with identity residue coordinates is independent
modulo the holomorphic differentials. -/
theorem s2e_residue_coordinates_mod_holomorphic
    (hE : Module.finrank ℂ E = 1) {r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (a : Fin r → ℂ) (θ : b3_HolForm E C)
    (he : (∑ i, a i • (w i : TangentBundle 𝓘(ℂ, E) C → ℂ)) = θ) :
    a = 0 := by
  classical
  funext j
  change a j = 0
  have hz : b4c_res (hE := hE) θ (x j) = 0 :=
    residue_eq_zero_of_analyticAt (RiemannRochEichler_loc_analytic hE θ (x j))
  have h := congrArg (fun f : TangentBundle 𝓘(ℂ, E) C → ℂ =>
    b4c_res (hE := hE) f (x j)) he
  rw [s2e_residue_linear_combination hE w a (x j), hz] at h
  simpa only [hres, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using h

/-- The linear family obtained from holomorphic differentials and the chosen
paired third-kind differentials.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, pp. 13–14. -/
def s2e_pairedDifferentialLinear
    (hE : Module.finrank ℂ E = 1) {r : ℕ} (w : Fin r → b4c_MeroForm E C hE) :
    (b3_HolForm E C × (Fin r → ℂ)) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, E) C → ℂ) :=
  (b3_HolForm E C).subtype.coprod
    (Fintype.linearCombination ℂ (fun i => (w i : TangentBundle 𝓘(ℂ, E) C → ℂ)))

example (hE : Module.finrank ℂ E = 1) {r : ℕ} (w : Fin r → b4c_MeroForm E C hE) :
    s2e_pairedDifferentialLinear hE w 0 = 0 := map_zero _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Independent paired residue coordinates make the whole holomorphic and
third-kind differential family injective. -/
theorem s2e_pairedDifferentialLinear_injective
    (hE : Module.finrank ℂ E = 1) {r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0) :
    Function.Injective (s2e_pairedDifferentialLinear hE w) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨θ, a⟩ hz
  simp only [s2e_pairedDifferentialLinear, LinearMap.coprod_apply,
    Submodule.subtype_apply, Fintype.linearCombination_apply] at hz
  have he : (∑ i, a i • (w i : TangentBundle 𝓘(ℂ, E) C → ℂ)) =
      ((-θ : b3_HolForm E C) : TangentBundle 𝓘(ℂ, E) C → ℂ) := by
    change (∑ i, a i • (w i : TangentBundle 𝓘(ℂ, E) C → ℂ)) = -θ.1
    calc
      _ = -θ.1 + (θ.1 + ∑ i, a i • (w i : TangentBundle 𝓘(ℂ, E) C → ℂ)) := by
        rw [← add_assoc, neg_add_cancel, zero_add]
      _ = -θ.1 := by rw [hz, add_zero]
  have ha := s2e_residue_coordinates_mod_holomorphic hE w x hres a (-θ) he
  have hθ : θ = 0 := by
    apply Subtype.ext
    change (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) = 0
    simpa only [ha, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] using hz
  exact Prod.ext hθ ha

/-- The differential family has one dimension per paired residue coordinate
in addition to the holomorphic genus contribution. -/
theorem s2e_pairedDifferentialLinear_finrank
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0) :
    Module.finrank ℂ (LinearMap.range (s2e_pairedDifferentialLinear hE w)) =
      Module.finrank ℂ (b3_HolForm E C) + r := by
  letI : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  letI := b3Forms_holForm_finiteDimensional (C := C) hE
  rw [LinearMap.finrank_range_of_inj (s2e_pairedDifferentialLinear_injective hE w x hres),
    Module.finrank_prod, Module.finrank_fin_fun]

/-- The selected genus equation supplies an actual differential family of
dimension `k + 1`, with independent paired residues and the specified poles. -/
theorem s2e_paired_slice_differential_family
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (k r : ℕ) (y : Fin (2 * r) → C)
    (hy : Function.Injective y)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C) + 2 * r) :
    ∃ w : Fin r → b4c_MeroForm E C hE,
      (∀ i x, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE (w i) x) 0) ∧
      (∀ i x, x ≠ y ⟨2 * i.val, by omega⟩ → x ≠ y ⟨2 * i.val + 1, by omega⟩ →
        AnalyticAt ℂ (HurwitzPrymRR_loc hE (w i) x) 0) ∧
      (∀ i j,
        b4c_res (hE := hE) (w i) (y ⟨2 * j.val, by omega⟩) = (if i = j then -1 else 0) ∧
        b4c_res (hE := hE) (w i) (y ⟨2 * j.val + 1, by omega⟩) = (if i = j then 1 else 0)) ∧
      Function.Injective (s2e_pairedDifferentialLinear hE w) ∧
      Module.finrank ℂ (LinearMap.range (s2e_pairedDifferentialLinear hE w)) = k + 1 := by
  obtain ⟨w, horder, hout, hmatrix⟩ := s2e_paired_residue_differentials hE r y hy
  have hres : ∀ i j, b4c_res (hE := hE) (w i) (y ⟨2 * j.val + 1, by omega⟩) =
      if i = j then 1 else 0 := fun i j => (hmatrix i j).2
  refine ⟨w, horder, hout, hmatrix,
    s2e_pairedDifferentialLinear_injective hE w _ hres, ?_⟩
  rw [s2e_pairedDifferentialLinear_finrank hE w _ hres]
  omega

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The local coefficient of the paired family is its actual holomorphic
coefficient plus the finite combination of third-kind coefficients. -/
theorem s2e_pairedDifferentialLinear_loc
    (hE : Module.finrank ℂ E = 1) {r : ℕ} (w : Fin r → b4c_MeroForm E C hE)
    (θ : b3_HolForm E C) (a : Fin r → ℂ) (p : C) :
    HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w (θ, a)) p =
      HurwitzPrymRR_loc hE θ p + ∑ i, a i • HurwitzPrymRR_loc hE (w i) p := by
  classical
  funext z
  simp only [s2e_pairedDifferentialLinear, LinearMap.coprod_apply,
    Submodule.subtype_apply, Fintype.linearCombination_apply, HurwitzPrymRR_loc,
    b4cov_coef, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every member of the differential family is meromorphic with at most
simple poles when its chosen third-kind generators have that property. -/
theorem s2e_pairedDifferentialLinear_simple_poles
    (hE : Module.finrank ℂ E = 1) {r : ℕ} (w : Fin r → b4c_MeroForm E C hE)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE (w i) p) 0)
    (θ : b3_HolForm E C) (a : Fin r → ℂ) (p : C) :
    MeromorphicAt (HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w (θ, a)) p) 0 ∧
      (-1 : WithTop ℤ) ≤ meromorphicOrderAt
        (HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w (θ, a)) p) 0 := by
  classical
  rw [s2e_pairedDifferentialLinear_loc]
  have hm (i : Fin r) : MeromorphicAt (a i • HurwitzPrymRR_loc hE (w i) p) 0 := by
    exact (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => a i) 0).meromorphicAt.smul
      ((w i).property.2 p)
  have ho (i : Fin r) : (-1 : WithTop ℤ) ≤
      meromorphicOrderAt (a i • HurwitzPrymRR_loc hE (w i) p) 0 := by
    by_cases hc : a i = 0
    · rw [hc, zero_smul]
      change (-1 : WithTop ℤ) ≤ meromorphicOrderAt (fun _ : ℂ => (0 : ℂ)) 0
      rw [meromorphicOrderAt_const, ite_eq_left rfl]
      exact le_top
    · rw [meromorphicOrderAt_const_smul_eq_meromorphicOrderAt hc]
      exact horder i p
  have hsum := MeromorphicAt.sum (s := Finset.univ) (fun i _ => hm i)
  have hsumorder := s2e_meromorphic_order_sum_lower_bound Finset.univ
    (fun i => a i • HurwitzPrymRR_loc hE (w i) p) 0 (-1)
    (fun i _ => hm i) (fun i _ => ho i)
  have hhol := RiemannRochEichler_loc_analytic hE θ p
  refine ⟨hhol.meromorphicAt.add hsum, ?_⟩
  have hn : (-1 : WithTop ℤ) ≤ 0 := by
    have hc : (-1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) := by norm_cast
    rw [hc, show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_le_coe]
    omega
  exact (le_min (hn.trans hhol.meromorphicOrderAt_nonneg) hsumorder).trans
    (meromorphicOrderAt_add hhol.meromorphicAt hsum)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Where every chosen third-kind generator is analytic, every member of
the paired differential family is analytic as well. -/
theorem s2e_pairedDifferentialLinear_analyticAt
    (hE : Module.finrank ℂ E = 1) {r : ℕ} (w : Fin r → b4c_MeroForm E C hE)
    (θ : b3_HolForm E C) (a : Fin r → ℂ) (p : C)
    (ha : ∀ i, AnalyticAt ℂ (HurwitzPrymRR_loc hE (w i) p) 0) :
    AnalyticAt ℂ (HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w (θ, a)) p) 0 := by
  classical
  rw [s2e_pairedDifferentialLinear_loc]
  exact (RiemannRochEichler_loc_analytic hE θ p).add
    (Finset.analyticAt_sum Finset.univ (fun i _ => analyticAt_const.smul (ha i)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The paired residue matrix recovers the actual coefficient of every
member of the holomorphic and third-kind differential family. -/
theorem s2e_pairedDifferentialLinear_residue_coordinate
    (hE : Module.finrank ℂ E = 1) {r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C) (c : ℂ)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then c else 0)
    (θ : b3_HolForm E C) (a : Fin r → ℂ) (j : Fin r) :
    b4c_res (hE := hE) (s2e_pairedDifferentialLinear hE w (θ, a)) (x j) = a j * c := by
  classical
  have hm (i : Fin r) : MeromorphicAt (a i • HurwitzPrymRR_loc hE (w i) (x j)) 0 := by
    exact (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => a i) 0).meromorphicAt.smul
      ((w i).property.2 (x j))
  have hsum := MeromorphicAt.sum (s := Finset.univ) (fun i _ => hm i)
  have hhol := RiemannRochEichler_loc_analytic hE θ (x j)
  unfold b4c_res at hres ⊢
  rw [s2e_pairedDifferentialLinear_loc, residue_add hhol.meromorphicAt hsum,
    residue_eq_zero_of_analyticAt hhol, zero_add,
    residue_sum (f := fun i => a i • HurwitzPrymRR_loc hE (w i) (x j)) Finset.univ (fun i _ => hm i)]
  simp only [residue_const_smul, smul_eq_mul, hres, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end HodgeLean.Foundations.Program
