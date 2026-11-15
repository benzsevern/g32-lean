import HodgeLean.Foundations.Program.PathCoverFamilyDefs
import HodgeLean.Foundations.Program.MarkedRootCoverLoops
import HodgeLean.Foundations.Program.MarkedRootCover

/-! # B6-5: positive circles at an admissible centre

Separation of the finite marks of an admissible configuration `c`, and two positive loop
families on the polydisc about `c` that the radial push of B6-2a fixes pointwise: circles of
radius `2 r` (`r = b6t_radius c`) about the finite marks, and one outer circle about `0`.
On a compact Galois cover free off the marks of a configuration `s` of the polydisc, lifts of
these loops detect the rotation generators over the marks of `s`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- The sum in the radius of the polydisc about `c`. -/
def b65z_radiusSum (c : Fin 10 → ℂ) : ℝ :=
  ∑ i : Fin 10, (‖c i‖⁻¹ + ‖c i - 1‖⁻¹ +
    ∑ j : Fin 10, if i = j then 0 else (dist (c i) (c j))⁻¹)

theorem b65z_radius_eq (c : Fin 10 → ℂ) :
    b6t_radius c = (4 * (1 + b65z_radiusSum c))⁻¹ := rfl

theorem b65z_term_nonneg (c : Fin 10 → ℂ) (i : Fin 10) :
    0 ≤ ‖c i‖⁻¹ + ‖c i - 1‖⁻¹ + ∑ j : Fin 10, if i = j then (0 : ℝ) else (dist (c i) (c j))⁻¹ := by
  have : 0 ≤ ∑ j : Fin 10, if i = j then (0 : ℝ) else (dist (c i) (c j))⁻¹ :=
    Finset.sum_nonneg fun j _ ↦ by split_ifs <;> positivity
  positivity

theorem b65z_term_le (c : Fin 10 → ℂ) (i : Fin 10) :
    ‖c i‖⁻¹ + ‖c i - 1‖⁻¹ + (∑ j : Fin 10, if i = j then (0 : ℝ) else (dist (c i) (c j))⁻¹) ≤
      b65z_radiusSum c :=
  Finset.single_le_sum (f := fun i ↦ ‖c i‖⁻¹ + ‖c i - 1‖⁻¹ +
    ∑ j : Fin 10, if i = j then (0 : ℝ) else (dist (c i) (c j))⁻¹)
    (fun k _ ↦ b65z_term_nonneg c k) (Finset.mem_univ i)

theorem b65z_norm_inv_le (c : Fin 10 → ℂ) (i : Fin 10) : ‖c i‖⁻¹ ≤ b65z_radiusSum c := by
  have h := b65z_term_le c i
  have h1 : 0 ≤ ∑ j : Fin 10, if i = j then (0 : ℝ) else (dist (c i) (c j))⁻¹ :=
    Finset.sum_nonneg fun j _ ↦ by split_ifs <;> positivity
  have h2 : 0 ≤ ‖c i - 1‖⁻¹ := by positivity
  linarith

theorem b65z_norm_sub_one_inv_le (c : Fin 10 → ℂ) (i : Fin 10) :
    ‖c i - 1‖⁻¹ ≤ b65z_radiusSum c := by
  have h := b65z_term_le c i
  have h1 : 0 ≤ ∑ j : Fin 10, if i = j then (0 : ℝ) else (dist (c i) (c j))⁻¹ :=
    Finset.sum_nonneg fun j _ ↦ by split_ifs <;> positivity
  have h2 : 0 ≤ ‖c i‖⁻¹ := by positivity
  linarith

theorem b65z_dist_inv_le (c : Fin 10 → ℂ) (i j : Fin 10) (hij : i ≠ j) :
    (dist (c i) (c j))⁻¹ ≤ b65z_radiusSum c := by
  have h := b65z_term_le c i
  have h1 : (dist (c i) (c j))⁻¹ ≤
      ∑ k : Fin 10, if i = k then (0 : ℝ) else (dist (c i) (c k))⁻¹ := by
    have := Finset.single_le_sum (f := fun k ↦ if i = k then (0 : ℝ) else (dist (c i) (c k))⁻¹)
      (fun k _ ↦ by split_ifs <;> positivity) (Finset.mem_univ j)
    simpa [hij] using this
  have h2 : 0 ≤ ‖c i‖⁻¹ := by positivity
  have h3 : 0 ≤ ‖c i - 1‖⁻¹ := by positivity
  linarith

theorem b65z_quarter (c : Fin 10 → ℂ) (D : ℝ) (hD : 0 < D) (hle : D⁻¹ ≤ b65z_radiusSum c) :
    4 * b6t_radius c < D := by
  rw [b65z_radius_eq]
  have hS : 0 < b65z_radiusSum c := lt_of_lt_of_le (inv_pos.mpr hD) hle
  rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (by norm_num : (4 : ℝ) ≠ 0), one_mul]
  have h1 : D⁻¹ < 1 + b65z_radiusSum c := by linarith
  exact (inv_lt_comm₀ (by linarith) hD).mpr h1

theorem b65z_radius_lt_quarter (c : Fin 10 → ℂ) (hc : c ∈ b6_chart) :
    4 * b6t_radius c < 1 := by
  have hc0 := (((b6_chart_coordinates c).mp hc).2 0).1
  have hS : 0 < b65z_radiusSum c :=
    lt_of_lt_of_le (inv_pos.mpr (norm_pos_iff.mpr hc0)) (b65z_norm_inv_le c 0)
  rw [b65z_radius_eq, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by norm_num : (4 : ℝ) ≠ 0),
    one_mul]
  exact inv_lt_one_of_one_lt₀ (by linarith)

theorem b65z_fin12_cases (j : Fin 12) :
    (∃ i : Fin 10, j = Fin.castAdd 2 i) ∨ ∃ i : Fin 2, j = Fin.natAdd 10 i :=
  Fin.addCases (m := 10) (n := 2) (motive := fun j ↦
    (∃ i : Fin 10, j = Fin.castAdd 2 i) ∨ ∃ i : Fin 2, j = Fin.natAdd 10 i)
    (fun i ↦ Or.inl ⟨i, rfl⟩) (fun i ↦ Or.inr ⟨i, rfl⟩) j

/-- **Separation of the finite marks.** Distinct finite marks of an admissible configuration are
more than `4 r` apart, `r = b6t_radius c`. -/
theorem b65z_mark_sep (c : Fin 10 → ℂ) (hc : c ∈ b6_chart) (j k : Fin 12) (hjk : j ≠ k) :
    4 * b6t_radius c < dist (mr_fin c j) (mr_fin c k) := by
  have hco := (b6_chart_coordinates c).mp hc
  have hpos : 0 < dist (mr_fin c j) (mr_fin c k) := by
    apply dist_pos.mpr
    intro h
    apply hjk
    have h' : b6_branch c j.castSucc = b6_branch c k.castSucc := by
      rw [mr_branch_castSucc, mr_branch_castSucc, h]
    exact Fin.castSucc_injective _ (hc h')
  rcases b65z_fin12_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
    rcases b65z_fin12_cases k with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> simp only [mr_fin, Fin.append_left, Fin.append_right] at hpos ⊢
  · have hjk' : j ≠ k := fun h ↦ hjk (by rw [h])
    exact b65z_quarter c _ hpos (b65z_dist_inv_le c j k hjk')
  · fin_cases k
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, dist_zero_right] at hpos ⊢
      exact b65z_quarter c _ hpos (b65z_norm_inv_le c j)
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, dist_eq_norm] at hpos ⊢
      exact b65z_quarter c _ hpos (b65z_norm_sub_one_inv_le c j)
  · rw [dist_comm] at hpos ⊢
    fin_cases j
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, dist_zero_right] at hpos ⊢
      exact b65z_quarter c _ hpos (b65z_norm_inv_le c k)
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, dist_eq_norm] at hpos ⊢
      exact b65z_quarter c _ hpos (b65z_norm_sub_one_inv_le c k)
  · fin_cases j <;> fin_cases k
    · exact absurd rfl hjk
    · simpa using b65z_radius_lt_quarter c hc
    · simpa using b65z_radius_lt_quarter c hc
    · exact absurd rfl hjk

/-- A finite mark of a configuration in the polydisc about `c` lies within `r` of the mark of
`c`. -/
theorem b65z_mark_near (c t : Fin 10 → ℂ) (ht : t ∈ b6t_polydisc c) (j : Fin 12) :
    dist (mr_fin t j) (mr_fin c j) < b6t_radius c := by
  rcases b65z_fin12_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simpa [mr_fin, Fin.append_left] using ht j
  · simpa [mr_fin, Fin.append_right] using b65z_radius_pos c

/-- The circle of radius `2 r` about a point within `r` of a finite mark of `c` stays more than
`r` away from every finite mark of `c`. -/
theorem b65z_circle_far (c : Fin 10 → ℂ) (hc : c ∈ b6_chart) (j : Fin 12) (p : ℂ)
    (hp : dist p (mr_fin c j) < b6t_radius c) (u : ℂ) (hu : ‖u‖ = 1) (k : Fin 12) :
    b6t_radius c < dist (p + 2 * (b6t_radius c : ℂ) * u) (mr_fin c k) := by
  have hr := b65z_radius_pos c
  have hpu : dist (p + 2 * (b6t_radius c : ℂ) * u) p = 2 * b6t_radius c := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_mul, norm_mul, hu, Complex.norm_real,
      Real.norm_of_nonneg hr.le]
    norm_num
  by_cases hkj : k = j
  · subst hkj
    have := dist_triangle (p + 2 * (b6t_radius c : ℂ) * u) (mr_fin c k) p
    rw [dist_comm (mr_fin c k) p] at this
    linarith
  · have hsep := b65z_mark_sep c hc j k (Ne.symm hkj)
    have := dist_triangle4 (mr_fin c j) p (p + 2 * (b6t_radius c : ℂ) * u) (mr_fin c k)
    rw [dist_comm (mr_fin c j) p] at this
    have hpu' : dist p (p + 2 * (b6t_radius c : ℂ) * u) = 2 * b6t_radius c := by
      rw [dist_comm]; exact hpu
    linarith

/-- The same circle avoids the thirteen marks of every configuration of the polydisc. -/
theorem b65z_circle_avoid (c : Fin 10 → ℂ) (hc : c ∈ b6_chart) (s : Fin 10 → ℂ)
    (hs : s ∈ b6t_polydisc c) (j : Fin 12) (p : ℂ) (hp : dist p (mr_fin c j) < b6t_radius c)
    (u : ℂ) (hu : ‖u‖ = 1) :
    ((p + 2 * (b6t_radius c : ℂ) * u : ℂ) : OnePoint ℂ) ∈ b6t_punctured s := by
  rintro ⟨i, hi⟩
  induction i using Fin.lastCases with
  | last => rw [mr_branch_last] at hi; exact OnePoint.infty_ne_coe _ hi
  | cast k =>
    rw [mr_branch_castSucc] at hi
    have hz := OnePoint.coe_injective hi
    have h1 := b65z_circle_far c hc j p hp u hu k
    have h2 := b65z_mark_near c s hs k
    rw [← hz] at h1
    linarith

/-- The same circle lies outside every branch disc of `c` with its boundary, so the radial push
of B6-2a fixes it pointwise. -/
theorem b65z_circle_fixed (c : Fin 10 → ℂ) (hc : c ∈ b6_chart) (j : Fin 12) (p : ℂ)
    (hp : dist p (mr_fin c j) < b6t_radius c) (u : ℂ) (hu : ‖u‖ = 1) :
    ((p + 2 * (b6t_radius c : ℂ) * u : ℂ) : OnePoint ℂ) ∉ ⋃ k : Fin 10,
      ((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall (c k) (b6t_radius c) := by
  simp only [Set.mem_iUnion, Set.mem_image, not_exists, not_and]
  intro k z hz hzp
  have h1 := b65z_circle_far c hc j p hp u hu (Fin.castAdd 2 k)
  rw [← OnePoint.coe_injective hzp] at h1
  simp only [mr_fin, Fin.append_left] at h1
  exact absurd (Metric.mem_closedBall.mp hz) (not_le.mpr h1)

/-- The radius of the outer circle about `0` for the polydisc about `c`. -/
def b65z_outerRadius (c : Fin 10 → ℂ) : ℝ := 3 + ∑ i : Fin 10, ‖c i‖

theorem b65z_norm_le_sum (c : Fin 10 → ℂ) (i : Fin 10) : ‖c i‖ ≤ ∑ i : Fin 10, ‖c i‖ :=
  Finset.single_le_sum (f := fun i ↦ ‖c i‖) (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)

/-- Every finite mark of every configuration of the polydisc lies inside the outer circle,
with margin `1`. -/
theorem b65z_mark_bound (c : Fin 10 → ℂ) (hc : c ∈ b6_chart) (s : Fin 10 → ℂ)
    (hs : s ∈ b6t_polydisc c) (k : Fin 12) :
    ‖mr_fin s k‖ < b65z_outerRadius c - 1 := by
  have hsum : 0 ≤ ∑ i : Fin 10, ‖c i‖ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hq := b65z_radius_lt_quarter c hc
  have hnear := b65z_mark_near c s hs k
  rcases b65z_fin12_cases k with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · simp only [mr_fin, Fin.append_left] at hnear ⊢
    have h1 := norm_le_norm_add_norm_sub' (s k) (c k)
    rw [← dist_eq_norm] at h1
    have h2 := b65z_norm_le_sum c k
    unfold b65z_outerRadius
    linarith
  · unfold b65z_outerRadius
    simp only [mr_fin, Fin.append_right]
    fin_cases k <;> simp <;> linarith

/-- The outer circle avoids the thirteen marks of every configuration of the polydisc. -/
theorem b65z_outer_avoid (c : Fin 10 → ℂ) (hc : c ∈ b6_chart) (s : Fin 10 → ℂ)
    (hs : s ∈ b6t_polydisc c) (z : ℂ) (hz : ‖z‖ = b65z_outerRadius c) :
    ((z : ℂ) : OnePoint ℂ) ∈ b6t_punctured s := by
  rintro ⟨i, hi⟩
  induction i using Fin.lastCases with
  | last => rw [mr_branch_last] at hi; exact OnePoint.infty_ne_coe _ hi
  | cast k =>
    rw [mr_branch_castSucc] at hi
    have hz' := OnePoint.coe_injective hi
    have h1 := b65z_mark_bound c hc s hs k
    rw [hz', hz] at h1
    linarith

/-- The outer circle lies outside every branch disc of `c` with its boundary. -/
theorem b65z_outer_fixed (c : Fin 10 → ℂ) (hc : c ∈ b6_chart) (z : ℂ)
    (hz : ‖z‖ = b65z_outerRadius c) :
    ((z : ℂ) : OnePoint ℂ) ∉ ⋃ k : Fin 10,
      ((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall (c k) (b6t_radius c) := by
  simp only [Set.mem_iUnion, Set.mem_image, not_exists, not_and]
  intro k w hw hwz
  rw [OnePoint.coe_injective hwz] at hw
  have h1 := Metric.mem_closedBall.mp hw
  rw [dist_eq_norm] at h1
  have h2 := norm_sub_norm_le z (c k)
  have h3 := b65z_norm_le_sum c k
  have hq := b65z_radius_lt_quarter c hc
  have hr := b65z_radius_pos c
  unfold b65z_outerRadius at hz
  linarith

/-- One positive turn of the unit circle, based at `1`. -/
def b65z_turn : Path (1 : Circle) 1 where
  toFun x := Circle.exp ((x : ℝ) * (2 * Real.pi))
  continuous_toFun := Circle.exp.continuous.comp (continuous_subtype_val.mul continuous_const)
  source' := by simp
  target' := by simp

/-- The circle of radius `w` about `q`, as a map from the unit circle to a punctured sphere. -/
def b65z_circleMap (s : Fin 10 → ℂ) (q : ℂ) (w : ℝ)
    (h : ∀ u : Circle, ((q + (u : ℂ) * (w : ℂ) : ℂ) : OnePoint ℂ) ∈ b6t_punctured s) :
    C(Circle, b6t_punctured s) :=
  ⟨fun u ↦ ⟨_, h u⟩, (OnePoint.continuous_coe.comp (continuous_const.add
    (continuous_subtype_val.mul continuous_const))).subtype_mk _⟩

theorem b65z_circleMap_turn (s : Fin 10 → ℂ) (q : ℂ) (w : ℝ)
    (h : ∀ u : Circle, ((q + (u : ℂ) * (w : ℂ) : ℂ) : OnePoint ℂ) ∈ b6t_punctured s)
    (x : unitInterval) :
    ((b65z_circleMap s q w h (b65z_turn x) : b6t_punctured s) : OnePoint ℂ) =
      ((q + Complex.exp ((((x : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) * (w : ℂ) : ℂ) :
        OnePoint ℂ) := by
  change ((q + ((Circle.exp ((x : ℝ) * (2 * Real.pi)) : Circle) : ℂ) * (w : ℂ) : ℂ) :
    OnePoint ℂ) = _
  rw [Circle.coe_exp]

/-- The circle of radius `2 r` about a point within `r` of a finite mark of `c` avoids the marks
of `s`. -/
theorem b65z_circle_mem (c : Fin 10 → ℂ) (hc : c ∈ b6_chart) (s : Fin 10 → ℂ)
    (hs : s ∈ b6t_polydisc c) (j : Fin 12) (p : ℂ) (hp : dist p (mr_fin c j) < b6t_radius c)
    (u : Circle) :
    ((p + (u : ℂ) * ((2 * b6t_radius c : ℝ) : ℂ) : ℂ) : OnePoint ℂ) ∈ b6t_punctured s := by
  have h := b65z_circle_avoid c hc s hs j p hp u (Circle.norm_coe u)
  convert h using 3
  push_cast
  ring

/-- **Positive circles about a moving mark.** On a compact Galois cover of the sphere, free off
the marks of `s`, take a lift of the circle of radius `2 r` about the finite mark `j` of `s`
and a lift of the circle of the same radius about any point within `r` of the mark of `c`. If
the second lift ends at `l •` its start, then `l` is the rotation generator at a point over the
mark of `s`. The two circles are freely homotopic in the punctured sphere by moving the centre.
Source: `RiemannRochTop_rotGen_affine_circle`, `RiemannRochTop_rotGen_of_homotopy`;
`b65z_circle_avoid`. -/
theorem b65z_circle_rotGen (c : Fin 10 → ℂ) (hc : c ∈ b6_chart) (s : Fin 10 → ℂ)
    (hs : s ∈ b6t_polydisc c) (j : Fin 12) (p : ℂ) (hp : dist p (mr_fin c j) < b6t_radius c)
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    {G : Type} [Group G] [Finite G] [MulAction G C] [FaithfulSMul G C]
    (hG : ∀ k : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ k • x))
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hgal : b4_IsGaloisCover G f)
    (hfree : ∀ x, f x ∉ Set.range (b6_branch s) → MulAction.stabilizer G x = ⊥)
    (Δ : C(unitInterval, C)) (k : G)
    (hΔ : ∀ x : unitInterval, f (Δ x) = ((mr_fin s j +
      Complex.exp ((((x : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) *
        ((2 * b6t_radius c : ℝ) : ℂ) : ℂ) : OnePoint ℂ))
    (hΔend : Δ 1 = k • Δ 0)
    (Γ : C(unitInterval, C)) (l : G)
    (hΓ : ∀ x : unitInterval, f (Γ x) = ((p +
      Complex.exp ((((x : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) *
        ((2 * b6t_radius c : ℝ) : ℂ) : ℂ) : OnePoint ℂ))
    (hΓend : Γ 1 = l • Γ 0) :
    ∃ q, f q = ((mr_fin s j : ℂ) : OnePoint ℂ) ∧ b4_IsRotGen ℂ q l := by
  have hr := b65z_radius_pos c
  have hsj := b65z_mark_near c s hs j
  let B : Set (OnePoint ℂ) := Set.range (b6_branch s)
  have hB : B.Finite := Set.finite_range _
  let w : ℝ := 2 * b6t_radius c
  -- the centre path from the mark of `s` to `p` stays within `r` of the mark of `c`
  have hcen : ∀ a : unitInterval,
      dist (mr_fin s j + (a : ℝ) • (p - mr_fin s j)) (mr_fin c j) < b6t_radius c := by
    intro a
    have hconv := convex_ball (mr_fin c j) (b6t_radius c)
    have h1 : mr_fin s j ∈ Metric.ball (mr_fin c j) (b6t_radius c) := hsj
    have h2 : p ∈ Metric.ball (mr_fin c j) (b6t_radius c) := hp
    have h3 := hconv.add_smul_sub_mem h1 h2 ⟨a.2.1, a.2.2⟩
    exact h3
  let J := b65z_circleMap s (mr_fin s j) w (b65z_circle_mem c hc s hs j _ hsj)
  let K := b65z_circleMap s p w (b65z_circle_mem c hc s hs j _ hp)
  have hHmem : ∀ z : unitInterval × Circle,
      ((mr_fin s j + (z.1 : ℝ) • (p - mr_fin s j) + (z.2 : ℂ) * (w : ℂ) : ℂ) : OnePoint ℂ) ∈
        b6t_punctured s := fun z ↦ b65z_circle_mem c hc s hs j _ (hcen z.1) z.2
  let H : ContinuousMap.Homotopy J K :=
    { toFun := fun z ↦ ⟨_, hHmem z⟩
      continuous_toFun := (OnePoint.continuous_coe.comp ((continuous_const.add
        ((continuous_subtype_val.comp continuous_fst).smul continuous_const)).add
        ((continuous_subtype_val.comp continuous_snd).mul continuous_const))).subtype_mk _
      map_zero_left := fun u ↦ by
        apply Subtype.ext
        simp [J, b65z_circleMap]
        rfl
      map_one_left := fun u ↦ by
        apply Subtype.ext
        simp [K, b65z_circleMap]
        rfl }
  -- positivity of the circle about the mark of `s`
  let d : Path (J 1) (J 1) := b65z_turn.map J.continuous
  have hd : ∀ x, (d x : OnePoint ℂ) = ((mr_fin s j +
      Complex.exp ((((x : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) * (w : ℂ) : ℂ) :
        OnePoint ℂ) := fun x ↦ b65z_circleMap_turn s _ w _ x
  have havoid : ∀ z : ℂ, ‖z‖ < 3 * b6t_radius c - dist (mr_fin s j) (mr_fin c j) → z ≠ 0 →
      ((mr_fin s j + z : ℂ) : OnePoint ℂ) ∉ B := by
    intro z hz hz0 hmem
    obtain ⟨i, hi⟩ := hmem
    induction i using Fin.lastCases with
    | last => rw [mr_branch_last] at hi; exact OnePoint.infty_ne_coe _ hi
    | cast k' =>
      rw [mr_branch_castSucc] at hi
      have hz' := OnePoint.coe_injective hi
      by_cases hkj : k' = j
      · subst hkj
        apply hz0
        linear_combination -hz'
      · have hsep := b65z_mark_sep c hc j k' (Ne.symm hkj)
        have hk' := b65z_mark_near c s hs k'
        have := dist_triangle4 (mr_fin c j) (mr_fin s j) (mr_fin s k') (mr_fin c k')
        have hd2 : dist (mr_fin s j) (mr_fin s k') = ‖z‖ := by
          rw [hz', dist_eq_norm, sub_add_cancel_left, norm_neg]
        rw [dist_comm (mr_fin c j) (mr_fin s j)] at this
        linarith
  have hw : ‖((w : ℝ) : ℂ)‖ < 3 * b6t_radius c - dist (mr_fin s j) (mr_fin c j) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    dsimp only [w]
    linarith
  have hw0 : ((w : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; dsimp only [w]; positivity
  have hc2 : FundamentalGroup.fromPath ⟦d⟧ =
      FundamentalGroup.fromPath ⟦((Path.refl (J 1)).trans d).trans (Path.refl (J 1)).symm⟧ := by
    rw [Path.refl_symm]
    apply congrArg FundamentalGroup.fromPath
    apply Quotient.sound
    exact (((Path.Homotopic.refl_trans _).hcomp (Path.Homotopic.refl _)).trans
      (Path.Homotopic.trans_refl _)).symm
  obtain ⟨q₀, hq₀, hk⟩ := RiemannRochTop_rotGen_affine_circle (by simp) hG f hf hgal B hB hfree
    (mr_fin s j) _ havoid _ hw hw0 (Path.refl (J 1)) d hd d hc2 Δ k
    (fun x ↦ (hΔ x).trans (hd x).symm) hΔend
  obtain ⟨q, hq, hl⟩ := RiemannRochTop_rotGen_of_homotopy (by simp) hG f hf hgal B hfree H 1
    b65z_turn Δ k (fun x ↦ (hΔ x).trans (b65z_circleMap_turn s _ w _ x).symm) hΔend q₀ hk
    Γ l (fun x ↦ (hΓ x).trans (b65z_circleMap_turn s _ w _ x).symm) hΓend
  exact ⟨q, hq.trans hq₀, hl⟩

theorem b65z_outerRadius_ge (c : Fin 10 → ℂ) : 3 ≤ b65z_outerRadius c := by
  have : 0 ≤ ∑ i : Fin 10, ‖c i‖ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  unfold b65z_outerRadius
  linarith

/-- **The positive loop about `∞`.** On a compact Galois cover of the sphere, free off the
marks of `s`, a lift of the clockwise circle of radius `b65z_outerRadius c` about `0` ending at
`l •` its start gives the rotation generator `l` at a point over `∞`.
Source: `RiemannRochTop_rotGen_infinity_circle`, `RiemannRochTop_infinity_disk_avoids`;
`b65z_mark_bound`. -/
theorem b65z_outer_rotGen (c : Fin 10 → ℂ) (hc : c ∈ b6_chart) (s : Fin 10 → ℂ)
    (hs : s ∈ b6t_polydisc c)
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    {G : Type} [Group G] [Finite G] [MulAction G C] [FaithfulSMul G C]
    (hG : ∀ k : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ k • x))
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hgal : b4_IsGaloisCover G f)
    (hfree : ∀ x, f x ∉ Set.range (b6_branch s) → MulAction.stabilizer G x = ⊥)
    (Γ : C(unitInterval, C)) (l : G)
    (hΓ : ∀ x : unitInterval, f (Γ x) = ((Complex.exp
      ((((unitInterval.symm x : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) *
        ((b65z_outerRadius c : ℝ) : ℂ) : ℂ) : OnePoint ℂ))
    (hΓend : Γ 1 = l • Γ 0) :
    ∃ q, f q = OnePoint.infty ∧ b4_IsRotGen ℂ q l := by
  let B : Set (OnePoint ℂ) := Set.range (b6_branch s)
  have hB : B.Finite := Set.finite_range _
  let M := b65z_outerRadius c
  have hM := b65z_outerRadius_ge c
  have hmem : ∀ u : Circle, ((0 + (u : ℂ) * (M : ℂ) : ℂ) : OnePoint ℂ) ∈ b6t_punctured s := by
    intro u
    apply b65z_outer_avoid c hc s hs
    rw [zero_add, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  let J := b65z_circleMap s 0 M hmem
  let d : Path (J 1) (J 1) := b65z_turn.map J.continuous
  have hd : ∀ x, (d x : OnePoint ℂ) = ((0 +
      Complex.exp ((((x : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) * (M : ℂ) : ℂ) :
        OnePoint ℂ) := fun x ↦ b65z_circleMap_turn s _ M _ x
  have hbound : ∀ b : ℂ, (b : OnePoint ℂ) ∈ B → ‖b - 0‖ < M - 1 := by
    rintro b ⟨i, hi⟩
    induction i using Fin.lastCases with
    | last => rw [mr_branch_last] at hi; exact absurd hi (OnePoint.infty_ne_coe _)
    | cast k =>
      rw [mr_branch_castSucc] at hi
      rw [sub_zero, ← OnePoint.coe_injective hi]
      exact b65z_mark_bound c hc s hs k
  have havoid := RiemannRochTop_infinity_disk_avoids B 0 (M - 1) (by linarith) hbound
  have hw : ‖((M : ℝ) : ℂ)⁻¹‖ < (M - 1)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    exact inv_strictAnti₀ (by linarith) (by linarith)
  have hw0 : ((M : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; linarith
  have hc2 : FundamentalGroup.fromPath ⟦d.symm⟧ =
      FundamentalGroup.fromPath ⟦((Path.refl (J 1)).trans d.symm).trans
        (Path.refl (J 1)).symm⟧ := by
    rw [Path.refl_symm]
    apply congrArg FundamentalGroup.fromPath
    apply Quotient.sound
    exact (((Path.Homotopic.refl_trans _).hcomp (Path.Homotopic.refl _)).trans
      (Path.Homotopic.trans_refl _)).symm
  exact RiemannRochTop_rotGen_infinity_circle (by simp) hG f hf hgal B hB hfree 0 _ havoid _ hw
    hw0 (Path.refl (J 1)) d hd d.symm hc2 Γ l
    (fun x ↦ (hΓ x).trans (by
      change _ = ((d (unitInterval.symm x) : b6t_punctured s) : OnePoint ℂ)
      rw [hd, zero_add])) hΓend

end HodgeLean.Foundations.Program
