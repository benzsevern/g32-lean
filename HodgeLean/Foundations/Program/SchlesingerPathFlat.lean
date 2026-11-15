import HodgeLean.Foundations.Program.SchlesingerPathLax

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

theorem b65p_coefficient_parameter_hasDerivAt
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] (t : ℂ → ι → ℂ)
    (A : ℂ → ι → E →L[ℂ] E) (v : ι → ℂ) (B : ι → E →L[ℂ] E)
    (θ x : ℂ) (ht : ∀ q, HasDerivAt (fun z ↦ t z q) (v q) θ)
    (hA : ∀ q, HasDerivAt (fun z ↦ A z q) (B q) θ)
    (hx : ∀ q, x ≠ t θ q) :
    HasDerivAt (fun z ↦ b65p_coefficient E (t z) (A z) x)
      (∑ q, ((v q / (x - t θ q) ^ 2) • A θ q +
        (x - t θ q)⁻¹ • B q)) θ := by
  unfold b65p_coefficient
  apply HasDerivAt.congr_deriv
    (HasDerivAt.fun_sum (u := Finset.univ) (fun q _ ↦
      (((hasDerivAt_const θ x).sub (ht q)).inv
        (sub_ne_zero.mpr (hx q))).smul (hA q)))
  congr 1
  funext q
  simp [add_comm]

theorem b65p_verticalCoefficient_spatial_hasDerivAt
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] (t v : ι → ℂ) (A : ι → E →L[ℂ] E)
    (x : ℂ) (hx : ∀ q, x ≠ t q) :
    HasDerivAt (b65p_verticalCoefficient E t v A)
      (∑ q, (v q / (x - t q) ^ 2) • A q) x := by
  unfold b65p_verticalCoefficient
  convert (HasDerivAt.fun_sum (u := Finset.univ) (fun q _ ↦
    ((hasDerivAt_const x (v q)).div
      ((hasDerivAt_id x).sub_const (t q))
      (sub_ne_zero.mpr (hx q))).smul_const (A q))).neg using 1
  congr 1
  simp only [id_eq, mul_one, zero_mul, zero_sub, neg_div, neg_smul, Finset.sum_neg_distrib,
    neg_neg]

theorem b65p_partial_fraction_pair (a b x u v : ℂ)
    (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b) :
    ((x - a)⁻¹ - (x - b)⁻¹) * ((u - v) / (a - b)) =
      (u - v) * (x - a)⁻¹ * (x - b)⁻¹ := by
  field_simp [sub_ne_zero.mpr hab, sub_ne_zero.mpr hxa, sub_ne_zero.mpr hxb]
  <;> ring

theorem b65p_curvature_pair (a b x u v : ℂ)
    (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b) :
    (x - a)⁻¹ * ((u - v) / (a - b)) + v * (x - a)⁻¹ * (x - b)⁻¹ =
      (x - b)⁻¹ * ((v - u) / (b - a)) + u * (x - b)⁻¹ * (x - a)⁻¹ := by
  have h := b65p_partial_fraction_pair a b x u v hab hxa hxb
  have hr : (v - u) / (b - a) = (u - v) / (a - b) := by
    rw [← neg_sub u v, ← neg_sub a b, neg_div_neg_eq]
  rw [hr]
  linear_combination h

theorem b65p_curvature_sum (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t v : ι → ℂ) (A : ι → E →L[ℂ] E) (x : ℂ)
    (hinj : Function.Injective t) (hx : ∀ q, x ≠ t q) :
    (∑ p, (x - t p)⁻¹ • b65p_schlesingerField E v t A p) =
      -(∑ p, ∑ q, (v q * (x - t p)⁻¹ * (x - t q)⁻¹) •
        (A q * A p - A p * A q)) := by
  apply eq_neg_iff_add_eq_zero.mpr
  unfold b65p_schlesingerField
  simp only [Finset.smul_sum, ← Finset.sum_add_distrib]
  rw [← Fintype.sum_prod_type (fun a : ι × ι ↦
    (x - t a.1)⁻¹ • (if a.2 = a.1 then 0 else
      ((v a.1 - v a.2) / (t a.1 - t a.2)) • (A a.2 * A a.1 - A a.1 * A a.2)) +
    (v a.2 * (x - t a.1)⁻¹ * (x - t a.2)⁻¹) •
      (A a.2 * A a.1 - A a.1 * A a.2))]
  apply Finset.sum_ninvolution Prod.swap
  · rintro ⟨p, q⟩
    by_cases hpq : q = p
    · subst q; simp
    · have hr := b65p_curvature_pair (t p) (t q) x (v p) (v q)
        (fun h ↦ hpq (hinj h).symm) (hx p) (hx q)
      simp only [Prod.swap, if_neg hpq, if_neg (Ne.symm hpq), smul_smul]
      rw [← add_smul, ← add_smul, ← neg_sub (A q * A p) (A p * A q),
        smul_neg, hr, add_neg_cancel]
  · rintro ⟨p, q⟩ h heq
    have hpq : q = p := congrArg Prod.fst heq
    subst q
    simp at h
  · intro a; exact Finset.mem_univ _
  · intro a; exact Prod.swap_swap a

theorem b65p_coefficient_commutator (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι : Type*} [Fintype ι]
    (t v : ι → ℂ) (A : ι → E →L[ℂ] E) (x : ℂ) :
    b65p_verticalCoefficient E t v A x * b65p_coefficient E t A x -
      b65p_coefficient E t A x * b65p_verticalCoefficient E t v A x =
      -(∑ p, ∑ q, (v q * (x - t p)⁻¹ * (x - t q)⁻¹) •
        (A q * A p - A p * A q)) := by
  have hleft : b65p_verticalCoefficient E t v A x * b65p_coefficient E t A x =
      -(∑ p, ∑ q, (v q * (x - t p)⁻¹ * (x - t q)⁻¹) • (A q * A p)) := by
    unfold b65p_verticalCoefficient b65p_coefficient
    rw [neg_mul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    simp only [smul_mul_smul_comm, div_eq_mul_inv]
    congr 1
    ring
  have hright : b65p_coefficient E t A x * b65p_verticalCoefficient E t v A x =
      -(∑ p, ∑ q, (v q * (x - t p)⁻¹ * (x - t q)⁻¹) • (A p * A q)) := by
    unfold b65p_verticalCoefficient b65p_coefficient
    rw [mul_neg, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    simp only [smul_mul_smul_comm, div_eq_mul_inv]
    congr 1
    ring
  rw [hleft, hright]
  simp only [smul_sub, Finset.sum_sub_distrib, neg_sub, neg_sub_neg]

theorem b65p_schlesinger_curvature (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t v : ι → ℂ) (A : ι → E →L[ℂ] E) (x : ℂ)
    (hinj : Function.Injective t) (hx : ∀ q, x ≠ t q) :
    (∑ p, (x - t p)⁻¹ • b65p_schlesingerField E v t A p) =
      b65p_verticalCoefficient E t v A x * b65p_coefficient E t A x -
        b65p_coefficient E t A x * b65p_verticalCoefficient E t v A x := by
  rw [b65p_curvature_sum E t v A x hinj hx, b65p_coefficient_commutator]

theorem b65p_schlesinger_flatness (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℂ → ι → ℂ) (A : ℂ → ι → E →L[ℂ] E)
    (v : ι → ℂ) (θ x : ℂ)
    (ht : ∀ q, HasDerivAt (fun z ↦ t z q) (v q) θ)
    (hA : ∀ q, HasDerivAt (fun z ↦ A z q)
      (b65p_schlesingerField E v (t θ) (A θ) q) θ)
    (hinj : Function.Injective (t θ)) (hx : ∀ q, x ≠ t θ q) :
    deriv (fun z ↦ b65p_coefficient E (t z) (A z) x) θ -
      deriv (b65p_verticalCoefficient E (t θ) v (A θ)) x =
      b65p_verticalCoefficient E (t θ) v (A θ) x * b65p_coefficient E (t θ) (A θ) x -
        b65p_coefficient E (t θ) (A θ) x * b65p_verticalCoefficient E (t θ) v (A θ) x := by
  rw [(b65p_coefficient_parameter_hasDerivAt E t A v
    (b65p_schlesingerField E v (t θ) (A θ)) θ x ht hA hx).deriv,
    (b65p_verticalCoefficient_spatial_hasDerivAt E (t θ) v (A θ) x hx).deriv,
    Finset.sum_add_distrib, add_sub_cancel_left,
    b65p_schlesinger_curvature E (t θ) v (A θ) x hinj hx]

end HodgeLean.Foundations.Program
