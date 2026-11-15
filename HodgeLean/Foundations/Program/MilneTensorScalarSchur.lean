import HodgeLean.Foundations.Program.MilneTensorScalarChart

noncomputable section
namespace HodgeLean.Foundations.Program
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

def m1b_scalarCross (Q : LinearMap.BilinForm ℂ (ℂ × W)) : W →ₗ[ℂ] ℂ :=
  (Q (1, 0)).comp (LinearMap.inr ℂ ℂ W)

def m1b_scalarRestriction (Q : LinearMap.BilinForm ℂ (ℂ × W)) :
    LinearMap.BilinForm ℂ W :=
  Q.compl₁₂ (LinearMap.inr ℂ ℂ W) (LinearMap.inr ℂ ℂ W)

def m1b_scalarSchur (Q : LinearMap.BilinForm ℂ (ℂ × W)) (a : ℂˣ) :
    LinearMap.BilinForm ℂ W :=
  m1b_scalarRestriction Q - a.inv •
    (LinearMap.mul ℂ ℂ).compl₁₂ (m1b_scalarCross Q) (m1b_scalarCross Q)

theorem m1b_symmetric_scalar_decomposition (Q : LinearMap.BilinForm ℂ (ℂ × W))
    (hs : ∀ x y, Q x y = Q y x) (x y : ℂ × W) :
    Q x y = Q (1, 0) (1, 0) * x.1 * y.1 + x.1 * m1b_scalarCross Q y.2 +
      y.1 * m1b_scalarCross Q x.2 + m1b_scalarRestriction Q x.2 y.2 := by
  have hx : x = x.1 • (1, (0 : W)) + (0, x.2) := by
    ext <;> simp
  have hy : y = y.1 • (1, (0 : W)) + (0, y.2) := by
    ext <;> simp
  calc
    Q x y = Q (x.1 • (1, 0) + (0, x.2)) (y.1 • (1, 0) + (0, y.2)) :=
      congrArg₂ (fun u v => Q u v) hx hy
    _ = _ := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul]
      rw [hs (0, x.2) (1, 0)]
      change _ = Q (1, 0) (1, 0) * x.1 * y.1 + x.1 * Q (1, 0) (0, y.2) +
        y.1 * Q (1, 0) (0, x.2) + Q (0, x.2) (0, y.2)
      ring

theorem m1b_scalar_schur_transport (Q : LinearMap.BilinForm ℂ (ℂ × W))
    (hs : ∀ x y, Q x y = Q y x) (a : ℂˣ) (ha : Q (1, 0) (1, 0) = a.val) :
    m1b_formTransport Q (m1b_scalarShearEquiv (-a.inv • m1b_scalarCross Q)).symm =
      m1b_prodBilin (a.val • LinearMap.mul ℂ ℂ) (m1b_scalarSchur Q a) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change Q (x.1 + (-a.inv) * m1b_scalarCross Q x.2, x.2)
    (y.1 + (-a.inv) * m1b_scalarCross Q y.2, y.2) = _
  simp only [neg_mul, ← sub_eq_add_neg]
  rw [m1b_symmetric_scalar_decomposition Q hs, ha]
  change a.val * (x.1 - a.inv * m1b_scalarCross Q x.2) *
      (y.1 - a.inv * m1b_scalarCross Q y.2) +
    (x.1 - a.inv * m1b_scalarCross Q x.2) * m1b_scalarCross Q y.2 +
    (y.1 - a.inv * m1b_scalarCross Q y.2) * m1b_scalarCross Q x.2 +
    m1b_scalarRestriction Q x.2 y.2 =
      a.val * (x.1 * y.1) + (m1b_scalarRestriction Q x.2 y.2 -
        a.inv * (m1b_scalarCross Q x.2 * m1b_scalarCross Q y.2))
  have hi : a.val * a.inv = 1 := a.val_inv
  linear_combination
    (a.inv * m1b_scalarCross Q x.2 * m1b_scalarCross Q y.2 -
      x.1 * m1b_scalarCross Q y.2 - y.1 * m1b_scalarCross Q x.2) * hi

theorem m1b_scalar_schur_nondegenerate (Q : LinearMap.BilinForm ℂ (ℂ × W))
    (hs : ∀ x y, Q x y = Q y x) (hQ : Q.Nondegenerate)
    (a : ℂˣ) (ha : Q (1, 0) (1, 0) = a.val) : (m1b_scalarSchur Q a).Nondegenerate := by
  have h := m1b_nondegenerate_transport
    (m1b_scalarShearEquiv (-a.inv • m1b_scalarCross Q)).symm Q hQ
  change (m1b_formTransport Q
    (m1b_scalarShearEquiv (-a.inv • m1b_scalarCross Q)).symm).Nondegenerate at h
  rw [m1b_scalar_schur_transport Q hs a ha] at h
  constructor
  · intro x hx
    have hx0 : ((0, x) : ℂ × W) = 0 := h.1 _ (by
      intro y
      change a.val * (0 * y.1) + m1b_scalarSchur Q a x y.2 = 0
      rw [zero_mul, mul_zero, zero_add, hx])
    exact congrArg Prod.snd hx0
  · intro y hy
    have hy0 : ((0, y) : ℂ × W) = 0 := h.2 _ (by
      intro x
      change a.val * (x.1 * 0) + m1b_scalarSchur Q a x.2 y = 0
      rw [mul_zero, mul_zero, zero_add, hy])
    exact congrArg Prod.snd hy0

theorem m1b_scalar_schur_symmetric (Q : LinearMap.BilinForm ℂ (ℂ × W))
    (hs : ∀ x y, Q x y = Q y x) (a : ℂˣ) (x y : W) :
    m1b_scalarSchur Q a x y = m1b_scalarSchur Q a y x := by
  change Q (0, x) (0, y) - a.inv * (m1b_scalarCross Q x * m1b_scalarCross Q y) =
    Q (0, y) (0, x) - a.inv * (m1b_scalarCross Q y * m1b_scalarCross Q x)
  rw [hs (0, x) (0, y), mul_comm (m1b_scalarCross Q x) (m1b_scalarCross Q y)]

theorem m1b_scalar_chart_realizes (B : LinearMap.BilinForm ℂ W)
    (Q : LinearMap.BilinForm ℂ (ℂ × W)) (hs : ∀ x y, Q x y = Q y x)
    (a t : ℂˣ) (ha : Q (1, 0) (1, 0) = a.val) (ht : t.val ^ 2 = a.val)
    (e : W ≃ₗ[ℂ] W) (he : m1b_formTransport B e = m1b_scalarSchur Q a) :
    m1b_formTransport (m1b_prodBilin (LinearMap.mul ℂ ℂ) B)
      (m1b_scalarChartEquiv t (a.inv • m1b_scalarCross Q) e).symm = Q := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change m1b_prodBilin (LinearMap.mul ℂ ℂ) B
    (m1b_scalarChartEquiv t (a.inv • m1b_scalarCross Q) e x)
    (m1b_scalarChartEquiv t (a.inv • m1b_scalarCross Q) e y) = Q x y
  rw [m1b_scalar_chart_pairing, ht, he, m1b_symmetric_scalar_decomposition Q hs, ha]
  change a.val * x.1 * y.1 + a.val * x.1 * (a.inv * m1b_scalarCross Q y.2) +
    a.val * y.1 * (a.inv * m1b_scalarCross Q x.2) +
    a.val * (a.inv * m1b_scalarCross Q x.2) * (a.inv * m1b_scalarCross Q y.2) +
    (m1b_scalarRestriction Q x.2 y.2 - a.inv * (m1b_scalarCross Q x.2 * m1b_scalarCross Q y.2)) =
      a.val * x.1 * y.1 + x.1 * m1b_scalarCross Q y.2 +
        y.1 * m1b_scalarCross Q x.2 + m1b_scalarRestriction Q x.2 y.2
  have hi : a.val * a.inv = 1 := a.val_inv
  linear_combination
    (x.1 * m1b_scalarCross Q y.2 + y.1 * m1b_scalarCross Q x.2 +
      a.inv * m1b_scalarCross Q x.2 * m1b_scalarCross Q y.2) * hi

theorem m1b_symmetric_scalar_chart_exists [FiniteDimensional ℂ W]
    (B : LinearMap.BilinForm ℂ W) (hB : B.Nondegenerate)
    (hsB : ∀ x y, B x y = B y x)
    (Q : LinearMap.BilinForm ℂ (ℂ × W)) (hQ : Q.Nondegenerate)
    (hsQ : ∀ x y, Q x y = Q y x) (a : ℂˣ) (ha : Q (1, 0) (1, 0) = a.val) :
    ∃ (t : ℂˣ) (e : W ≃ₗ[ℂ] W), t.val ^ 2 = a.val ∧
      m1b_formTransport B e = m1b_scalarSchur Q a ∧
      m1b_formTransport (m1b_prodBilin (LinearMap.mul ℂ ℂ) B)
        (m1b_scalarChartEquiv t (a.inv • m1b_scalarCross Q) e).symm = Q := by
  obtain ⟨e, he⟩ := m1b_symmetric_forms_same_orbit B (m1b_scalarSchur Q a) hB
    (m1b_scalar_schur_nondegenerate Q hsQ hQ a ha) hsB (m1b_scalar_schur_symmetric Q hsQ a)
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq a.val (n := 2) (by decide)
  have ht0 : t ≠ 0 := by
    intro hz
    have hh : a.val = 0 := by rw [← ht, hz]; norm_num
    exact a.ne_zero hh
  refine ⟨Units.mk0 t ht0, e, ht, he, ?_⟩
  exact m1b_scalar_chart_realizes B Q hsQ a (Units.mk0 t ht0) ha ht e he

end HodgeLean.Foundations.Program
