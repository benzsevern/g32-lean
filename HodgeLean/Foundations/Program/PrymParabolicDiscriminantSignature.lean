import HodgeLean.Foundations.Program.PrymParabolicDiscriminantDefs
noncomputable section
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Foundations.WeilHermitian
open HodgeLean.Foundations.HermitianForm
open Matrix
namespace HodgeLean.Foundations.Program

theorem hg7_matrix_value {n : ℕ} (M : Matrix (Fin n) (Fin n) hp_K)
    (x y : Fin n → hp_K) : hp_matrixForm M x y = star x ⬝ᵥ (M *ᵥ y) := by
  rw [apply_eq_star_dotProduct_toMatrix₂_mulVec (Pi.basisFun _ _)]
  simp only [hp_matrixForm, LinearMap.toMatrix₂_toLinearMapₛₗ₂,
    show ⇑((Pi.basisFun hp_K (Fin n)).repr x) = x from funext (Pi.basisFun_repr hp_K (Fin n) x),
    show ⇑((Pi.basisFun hp_K (Fin n)).repr y) = y from funext (Pi.basisFun_repr hp_K (Fin n) y)]

theorem hg7_matrix_pullback {n : ℕ} (M A : Matrix (Fin n) (Fin n) hp_K)
    (x y : Fin n → hp_K) :
    hp_matrixForm M (A *ᵥ x) (A *ᵥ y) = hp_matrixForm (Aᴴ * M * A) x y := by
  simp only [hg7_matrix_value, star_mulVec, dotProduct_mulVec, vecMul_vecMul,
    Matrix.mul_assoc]

theorem hg7_signature_rat_equiv {W W' : Type*} [AddCommGroup W] [AddCommGroup W']
    [Module hp_K W] [Module hp_K W'] [Module ℚ W] [Module ℚ W']
    [IsScalarTower ℚ hp_K W] [IsScalarTower ℚ hp_K W']
    (h : W →ₗ⋆[hp_K] W →ₗ[hp_K] hp_K)
    (h' : W' →ₗ⋆[hp_K] W' →ₗ[hp_K] hp_K) (e : W ≃ₗ[ℚ] W')
    (he : ∀ x, (h' (e x) (e x)).re = (h x x).re) :
    hermSignature h = hermSignature h' := by
  let q := (hermQuadForm h).baseChange ℝ
  let q' := (hermQuadForm h').baseChange ℝ
  let er := e.baseChange ℚ ℝ _ _
  have heq : QuadraticMap.Equivalent q q' := by
    refine ⟨{ toLinearEquiv := er, map_app' := fun z => ?_ }⟩
    have hforms : q'.comp er.toLinearMap = q := by
      apply baseChange_ext
      intro x
      simp [q, q', er, hermQuadForm_apply, he]
    exact DFunLike.congr_fun hforms z
  simp only [hermSignature, Prod.mk.injEq]
  exact ⟨congrArg (fun n => n / 2) heq.sigPos_eq,
    congrArg (fun n => n / 2) heq.sigNeg_eq⟩

theorem hg7_signature_conjugate {n : ℕ} (M : Matrix (Fin n) (Fin n) hp_K) :
    hermSignature (hp_matrixForm (M.map (starRingEnd hp_K))) =
      hermSignature (hp_matrixForm M) := by
  let e : (Fin n → hp_K) ≃ₗ[ℚ] (Fin n → hp_K) :=
    { toFun := star, invFun := star, left_inv := star_star, right_inv := star_star
      map_add' := star_add, map_smul' := fun c x => by simp }
  symm
  apply hg7_signature_rat_equiv _ _ e
  intro x
  have he : hp_matrixForm (M.map (starRingEnd hp_K)) (star x) (star x) =
      star (hp_matrixForm M x x) := by
    simp only [hg7_matrix_value, dotProduct, Matrix.mulVec, Finset.mul_sum,
      Pi.star_apply, Matrix.map_apply, starRingEnd_apply, star_sum, star_mul, star_star]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  change (hp_matrixForm (M.map (starRingEnd hp_K)) (star x) (star x)).re = _
  simpa only [QuadraticAlgebra.re_star, mul_zero, zero_mul, add_zero] using
    congrArg QuadraticAlgebra.re he

theorem hg7_signature_inverse_transpose {n : ℕ} (M : Matrix (Fin n) (Fin n) hp_K)
    (hm : M.IsHermitian) (hd : M.det ≠ 0) :
    hermSignature (hp_matrixForm M⁻¹.transpose) = hermSignature (hp_matrixForm M) := by
  have hT : IsUnit M.transpose.det := by rw [det_transpose]; exact isUnit_iff_ne_zero.2 hd
  have hD : IsUnit M⁻¹.transpose.det := by
    rw [det_transpose, det_nonsing_inv, Ring.inverse_eq_inv]
    exact isUnit_iff_ne_zero.2 (inv_ne_zero hd)
  let e := Matrix.toLinearEquiv (Pi.basisFun hp_K (Fin n)) M⁻¹.transpose hD
  have he : ∀ x y, hp_matrixForm M.transpose (e x) (e y) =
      hp_matrixForm M⁻¹.transpose x y := by
    intro x y
    change hp_matrixForm M.transpose
      (Matrix.toLin (Pi.basisFun _ _) (Pi.basisFun _ _) M⁻¹.transpose x)
      (Matrix.toLin (Pi.basisFun _ _) (Pi.basisFun _ _) M⁻¹.transpose y) = _
    rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply, Matrix.toLin'_apply,
      hg7_matrix_pullback, hm.inv.transpose.eq, transpose_nonsing_inv,
      Matrix.nonsing_inv_mul _ hT, Matrix.one_mul]
  have hsig := HermitianClass.hermSignature_eq_of_equiv _ _ _ _ e he
  have hc : M.map (starRingEnd hp_K) = M.transpose := by
    apply Matrix.ext
    intro i j
    exact congrFun (congrFun hm.eq j) i
  exact hsig.trans (hc ▸ hg7_signature_conjugate M)

theorem hg7_signature_positive_h0 (c : ℚ) (hc : 0 < c) :
    hermSignature ((c : hp_K) • hp_h0Form) = (3, 3) := by
  let d : Fin 6 → ℚ := ![1, 1, 1, -1, -1, -2]
  have heq : diagForm (a := -3) (b := 0) (fun i => c * d i) =
      (c : hp_K) • b60_H := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp only [LinearMap.smul_apply, smul_eq_mul, b60_H, diagForm_apply,
      map_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change star (x i) * ((c : hp_K) * (d i : hp_K)) * y i =
      (c : hp_K) * (star (x i) * (d i : hp_K) * y i)
    ring
  obtain ⟨g, hg⟩ := hp_h0_landherr
  have he : ∀ x y, diagForm (a := -3) (b := 0) (fun i => c * d i) (g x) (g y) =
      ((c : hp_K) • hp_h0Form) x y := by
    intro x y
    rw [heq]
    change (c : hp_K) * b60_H (g x) (g y) = (c : hp_K) * hp_h0Form x y
    rw [hg]
  rw [HermitianClass.hermSignature_eq_of_equiv _ _ _ _ g he,
    hermSignature_diagForm (by norm_num)]
  have hp : {i | 0 < c * d i} = {i | 0 < d i} := by
    ext i
    exact mul_pos_iff_of_pos_left hc
  have hn : {i | c * d i < 0} = {i | d i < 0} := by
    ext i
    change c * d i < 0 ↔ d i < 0
    constructor <;> intro h <;> nlinarith
  rw [hp, hn, ← hermSignature_diagForm (by norm_num : (-3 : ℚ) < 0) d]
  exact hermSignature_diag_F1569

end HodgeLean.Foundations.Program
