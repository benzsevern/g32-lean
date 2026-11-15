import HodgeLean.Foundations.Program.MilneTensorPairedExpansion

noncomputable section
namespace HodgeLean.Foundations.Program
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

set_option maxHeartbeats 400000 in
theorem m1b_pair_schur_decomposition
    (Q : LinearMap.BilinForm ℂ ((Fin 2 → ℂ) × W)) (ha : ∀ x, Q x x = 0)
    (a : ℂˣ) (hp : Q (Pi.single 0 1, 0) (Pi.single 1 1, 0) = a.val)
    (x y : (Fin 2 → ℂ) × W) :
    Q x y = a.val * m1b_pairForm (x.1 + m1b_pairShear Q a x.2)
      (y.1 + m1b_pairShear Q a y.2) + m1b_pairSchur Q a x.2 y.2 := by
  rw [m1b_alternating_pair_decomposition Q ha x y, hp]
  change _ = a.val *
    ((x.1 0 + -a.inv * m1b_pairCross Q 1 x.2) *
      (y.1 1 + a.inv * m1b_pairCross Q 0 y.2) -
    (x.1 1 + a.inv * m1b_pairCross Q 0 x.2) *
      (y.1 0 + -a.inv * m1b_pairCross Q 1 y.2)) +
    (m1b_pairRestriction Q x.2 y.2 + a.inv *
      (m1b_pairCross Q 1 x.2 * m1b_pairCross Q 0 y.2 -
        m1b_pairCross Q 0 x.2 * m1b_pairCross Q 1 y.2))
  rw [Units.inv_eq_val_inv, Units.val_inv_eq_inv_val]
  field_simp
  <;> ring

theorem m1b_pair_schur_transport
    (Q : LinearMap.BilinForm ℂ ((Fin 2 → ℂ) × W)) (ha : ∀ x, Q x x = 0)
    (a : ℂˣ) (hp : Q (Pi.single 0 1, 0) (Pi.single 1 1, 0) = a.val) :
    m1b_formTransport Q (m1b_blockShearEquiv (-m1b_pairShear Q a)).symm =
      m1b_prodBilin (a.val • m1b_pairForm) (m1b_pairSchur Q a) := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change Q (x.1 + -(m1b_pairShear Q a x.2), x.2)
    (y.1 + -(m1b_pairShear Q a y.2), y.2) =
      a.val * m1b_pairForm x.1 y.1 + m1b_pairSchur Q a x.2 y.2
  rw [m1b_pair_schur_decomposition Q ha a hp]
  change a.val * m1b_pairForm (x.1 + -(m1b_pairShear Q a x.2) + m1b_pairShear Q a x.2)
    (y.1 + -(m1b_pairShear Q a y.2) + m1b_pairShear Q a y.2) +
      m1b_pairSchur Q a x.2 y.2 = _
  simp [add_assoc]

theorem m1b_pair_schur_alternating
    (Q : LinearMap.BilinForm ℂ ((Fin 2 → ℂ) × W)) (ha : ∀ x, Q x x = 0)
    (a : ℂˣ) (w : W) : m1b_pairSchur Q a w w = 0 := by
  change Q (0, w) (0, w) + a.inv *
    (m1b_pairCross Q 1 w * m1b_pairCross Q 0 w -
      m1b_pairCross Q 0 w * m1b_pairCross Q 1 w) = 0
  rw [ha]
  ring

theorem m1b_pair_schur_nondegenerate
    (Q : LinearMap.BilinForm ℂ ((Fin 2 → ℂ) × W)) (ha : ∀ x, Q x x = 0)
    (hQ : Q.Nondegenerate) (a : ℂˣ)
    (hp : Q (Pi.single 0 1, 0) (Pi.single 1 1, 0) = a.val) :
    (m1b_pairSchur Q a).Nondegenerate := by
  have h := m1b_nondegenerate_transport (m1b_blockShearEquiv (-m1b_pairShear Q a)).symm Q hQ
  change (m1b_formTransport Q (m1b_blockShearEquiv (-m1b_pairShear Q a)).symm).Nondegenerate at h
  rw [m1b_pair_schur_transport Q ha a hp] at h
  constructor
  · intro x hx
    have hx0 : ((0, x) : (Fin 2 → ℂ) × W) = 0 := h.1 _ (by
      intro y
      change a.val * m1b_pairForm 0 y.1 + m1b_pairSchur Q a x y.2 = 0
      rw [map_zero, LinearMap.zero_apply, mul_zero, zero_add, hx])
    exact congrArg Prod.snd hx0
  · intro y hy
    have hy0 : ((0, y) : (Fin 2 → ℂ) × W) = 0 := h.2 _ (by
      intro x
      change a.val * m1b_pairForm x.1 0 + m1b_pairSchur Q a x.2 y = 0
      rw [map_zero, mul_zero, zero_add, hy])
    exact congrArg Prod.snd hy0

end HodgeLean.Foundations.Program
