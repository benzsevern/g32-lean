import HodgeLean.Foundations.Program.ParabolicPolarizationBridgeDefs

/-! # Proof obligations for the H1 parabolic-polarization bridge -/

noncomputable section
open Matrix
open scoped TensorProduct
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.WeilHermitian
open HodgeLean.Foundations.HermitianForm
namespace HodgeLean.Foundations.Program

/-! ## `ζ` and the complex embedding -/

/-- `ζ = -1/2 + (1/2) √-3` in coordinates. -/
theorem hp_zeta_eq : hp_zeta = ⟨-1/2, 1/2⟩ := by
  rw [hp_zeta, div_eq_iff two_ne_zero]
  ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_ofNat,
    QuadraticAlgebra.im_ofNat]

/-- `ζ² + ζ + 1 = 0` in `K`. -/
theorem hp_zeta_rel : hp_zeta ^ 2 + hp_zeta + 1 = 0 := by
  rw [hp_zeta_eq]
  ext <;> simp [pow_two, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> norm_num

/-- `φ(x + y√-3) = x + √3 y i`. -/
theorem hp_toComplex_apply (z : QuadraticAlgebra ℚ (-3) 0) :
    hp_toComplex z = ⟨z.re, Real.sqrt 3 * z.im⟩ := by
  change (z.re • (1 : ℂ) + z.im • ((Real.sqrt 3 : ℂ) * Complex.I)) = _
  apply Complex.ext <;> simp [Rat.smul_def]; ring

theorem hp_toComplex_re (z : QuadraticAlgebra ℚ (-3) 0) : (hp_toComplex z).re = z.re := by
  rw [hp_toComplex_apply]

/-- The embedding commutes with conjugation. -/
theorem hp_toComplex_star (z : QuadraticAlgebra ℚ (-3) 0) :
    hp_toComplex (star z) = (starRingEnd ℂ) (hp_toComplex z) := by
  rw [hp_toComplex_apply, hp_toComplex_apply]
  apply Complex.ext <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]

theorem hp_toComplex_zeta_aux :
    hp_toComplex hp_zeta ^ 2 + hp_toComplex hp_zeta + 1 = 0 := by
  simpa using congrArg hp_toComplex hp_zeta_rel

theorem hp_h0_map_complex_aux :
    (g32H0 hp_zeta).map hp_toComplex = g32H0 (hp_toComplex hp_zeta) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g32H0, map_ofNat]

/-! ## The signature bridge -/

/-- `ℝ²` as `ℂ`, `v ↦ v₀ + c v₁ i`, for `c ≠ 0`.
Source: the real basis `(1, c i)` of `ℂ`. -/
def hp_cplx (c : ℝ) (hc : c ≠ 0) : (Fin 2 → ℝ) ≃ₗ[ℝ] ℂ where
  toFun v := ⟨v 0, c * v 1⟩
  invFun z := ![z.re, z.im / c]
  map_add' v w := by apply Complex.ext <;> simp; ring
  map_smul' r v := by apply Complex.ext <;> simp; ring
  left_inv v := by
    funext j
    fin_cases j
    · simp
    · simp [hc]
  right_inv z := by
    apply Complex.ext
    · simp
    · simp [mul_div_cancel₀ _ hc]

/-- `ℝ^{n × 2}` as `ℂⁿ`, by `hp_cplx` in each coordinate.
Source: the real basis `(1, c i)` of `ℂ` in each coordinate. -/
def hp_cplxN (n : ℕ) (c : ℝ) (hc : c ≠ 0) : (Fin n × Fin 2 → ℝ) ≃ₗ[ℝ] (Fin n → ℂ) :=
  (LinearEquiv.curry ℝ ℝ (Fin n) (Fin 2)).trans
    (LinearEquiv.piCongrRight fun _ => hp_cplx c hc)

theorem hp_cplxN_symm_apply (n : ℕ) (w : Fin n → ℂ) (i : Fin n) :
    (hp_cplxN n 1 one_ne_zero).symm w (i, 0) = (w i).re ∧
      (hp_cplxN n 1 one_ne_zero).symm w (i, 1) = (w i).im := by
  simp [hp_cplxN, hp_cplx]

theorem hp_sqrt3_ne : Real.sqrt 3 ≠ 0 := by positivity

/-- The real isomorphism `ℝ ⊗_ℚ Kⁿ ≃ ℂⁿ`, `r ⊗ x ↦ r · φ(x)`.
Source: the coordinates `(re, im)` of `K = ℚ(√-3)` (`HermitianForm.tupleEquiv`) followed by
`x + y√-3 ↦ x + √3 y i`. -/
def hp_realify (n : ℕ) : ℝ ⊗[ℚ] (Fin n → QuadraticAlgebra ℚ (-3) 0) ≃ₗ[ℝ] (Fin n → ℂ) :=
  ((tupleEquiv (a := -3) (ι := Fin n)).baseChange ℚ ℝ _ _).trans
    ((TensorProduct.piScalarRight ℚ ℝ ℝ (Fin n × Fin 2)).trans
      (hp_cplxN n (Real.sqrt 3) hp_sqrt3_ne))

theorem hp_realify_tmul (n : ℕ) (x : Fin n → QuadraticAlgebra ℚ (-3) 0) :
    hp_realify n (1 ⊗ₜ x) = fun i => hp_toComplex (x i) := by
  funext i
  rw [hp_toComplex_apply]
  apply Complex.ext <;>
    simp [hp_realify, hp_cplxN, hp_cplx, tupleEquiv, LinearEquiv.baseChange_tmul]

/-- Multiplication by a unitary matrix, as a real linear equivalence of `ℂⁿ`.
Source: Mathlib `Matrix.unitaryGroup`. -/
def hp_unitaryEquiv {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (Fin n → ℂ) ≃ₗ[ℝ] (Fin n → ℂ) :=
  LinearEquiv.ofLinearMap
    (f := (Matrix.mulVecLin (U : Matrix (Fin n) (Fin n) ℂ)).restrictScalars ℝ)
    (g := (Matrix.mulVecLin (star U : Matrix (Fin n) (Fin n) ℂ)).restrictScalars ℝ)
    (LinearMap.ext fun v => by simp [Matrix.mulVec_mulVec])
    (LinearMap.ext fun v => by simp [Matrix.mulVec_mulVec])

theorem hp_unitaryEquiv_symm_apply {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (v : Fin n → ℂ) :
    (hp_unitaryEquiv U).symm v = (star U : Matrix (Fin n) (Fin n) ℂ) *ᵥ v := rfl

/-- The real part of `vᴴ A v` in the eigenbasis of a Hermitian `A`: with `w = Uᴴ v`, it is
`∑ λᵢ |wᵢ|²`. -/
theorem hp_re_dotProduct_eigen {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (v : Fin n → ℂ) :
    (star v ⬝ᵥ (A *ᵥ v)).re = ∑ i, hA.eigenvalues i *
      (((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) i).re ^ 2 +
        ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) i).im ^ 2) := by
  set U : Matrix (Fin n) (Fin n) ℂ := ↑hA.eigenvectorUnitary
  set w := star U *ᵥ v
  have hspec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  have hv : star v ⬝ᵥ (A *ᵥ v) = star w ⬝ᵥ
      (diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ w) := by
    conv_lhs => rw [hspec]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.star_mulVec]
    simp [w, U, Matrix.star_eq_conjTranspose]
  rw [hv, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.mulVec_diagonal]
  ring

/-- The complex image of `hp_matrixForm M x y` is `φ(x)ᴴ (φ M) φ(y)`. -/
theorem hp_toComplex_matrixForm {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (QuadraticAlgebra ℚ (-3) 0))
    (x y : Fin n → QuadraticAlgebra ℚ (-3) 0) :
    hp_toComplex (hp_matrixForm M x y) =
      star (fun i => hp_toComplex (x i)) ⬝ᵥ
        (M.map hp_toComplex *ᵥ fun i => hp_toComplex (y i)) := by
  simp only [hp_matrixForm, Matrix.toLinearMapₛₗ₂_apply, Pi.basisFun_repr, map_sum,
    dotProduct, mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hs : hp_toComplex ((starRingEnd _) (x i)) = star (hp_toComplex (x i)) :=
    hp_toComplex_star (x i)
  simp only [smul_eq_mul, map_mul, hs]
  ring

/-- Over `ℝ`, the rational form `x ↦ h x x` of `hp_matrixForm M` is the weighted sum of squares
with each complex eigenvalue of `φ M` taken twice. -/
theorem hp_realQuad_equivalent {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (QuadraticAlgebra ℚ (-3) 0))
    (hA : (M.map hp_toComplex).IsHermitian) :
    QuadraticMap.Equivalent ((hermQuadForm (hp_matrixForm M)).baseChange ℝ)
      (QuadraticMap.weightedSumSquares ℝ fun k : Fin n × Fin 2 => hA.eigenvalues k.1) := by
  let e := (hp_realify n).trans
    ((hp_unitaryEquiv hA.eigenvectorUnitary).symm.trans (hp_cplxN n 1 one_ne_zero).symm)
  have hforms :
      (QuadraticMap.weightedSumSquares ℝ fun k : Fin n × Fin 2 => hA.eigenvalues k.1).comp
        e.toLinearMap = (hermQuadForm (hp_matrixForm M)).baseChange ℝ := by
    apply baseChange_ext
    intro x
    rw [QuadraticForm.baseChange_tmul, hermQuadForm_apply, mul_one, Rat.smul_def, mul_one,
      ← hp_toComplex_re, hp_toComplex_matrixForm, hp_re_dotProduct_eigen hA]
    simp only [QuadraticMap.comp_apply, LinearEquiv.coe_coe, e, LinearEquiv.trans_apply,
      hp_realify_tmul, hp_unitaryEquiv_symm_apply, QuadraticMap.weightedSumSquares_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, (hp_cplxN_symm_apply _ _ _).1,
      (hp_cplxN_symm_apply _ _ _).2]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  exact ⟨{ toLinearEquiv := e, map_app' := fun m => DFunLike.congr_fun hforms m }⟩

/-- Halving a count over `Fin n × Fin 2` that ignores the second coordinate. -/
theorem hp_ncard_prod_two {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    {k : Fin n × Fin 2 | p k.1}.ncard / 2 = (Finset.univ.filter p).card := by
  have h : {k : Fin n × Fin 2 | p k.1} = {i | p i} ×ˢ Set.univ := by
    ext k; simp
  rw [h, Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin,
    Nat.mul_div_cancel _ two_pos, ← Set.ncard_coe_finset]
  congr 1
  ext i; simp

theorem hp_hermSignature_matrixForm_aux {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (QuadraticAlgebra ℚ (-3) 0))
    (A : Matrix (Fin n) (Fin n) ℂ) (hMA : M.map hp_toComplex = A) (hA : A.IsHermitian) :
    hermSignature (hp_matrixForm M) =
      ((Finset.univ.filter fun i => 0 < hA.eigenvalues i).card,
        (Finset.univ.filter fun i => hA.eigenvalues i < 0).card) := by
  subst hMA
  have he := hp_realQuad_equivalent M hA
  rw [hermSignature, QuadraticForm.sigPos_of_equiv_weightedSumSquares he,
    QuadraticForm.sigNeg_of_equiv_weightedSumSquares he]
  exact Prod.ext (hp_ncard_prod_two fun i => 0 < hA.eigenvalues i)
    (hp_ncard_prod_two fun i => hA.eigenvalues i < 0)

/-! ## The convention bridge -/

theorem hp_toMatrix₂_of_isometry_aux {W : Type*} [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] {n : ℕ}
    (H : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0)
    (M : Matrix (Fin n) (Fin n) (QuadraticAlgebra ℚ (-3) 0))
    (f : W ≃ₗ[QuadraticAlgebra ℚ (-3) 0] (Fin n → QuadraticAlgebra ℚ (-3) 0))
    (hf : ∀ x y, hp_matrixForm M (f x) (f y) = H x y) :
    LinearMap.toMatrix₂ ((Pi.basisFun _ (Fin n)).map f.symm)
      ((Pi.basisFun _ (Fin n)).map f.symm) H = M := by
  refine Matrix.ext fun i j => ?_
  rw [LinearMap.toMatrix₂_apply, Module.Basis.map_apply, Module.Basis.map_apply, ← hf]
  simp only [LinearEquiv.apply_symm_apply]
  have h := congrFun (congrFun (show LinearMap.toMatrix₂ (Pi.basisFun _ (Fin n))
    (Pi.basisFun _ (Fin n)) (hp_matrixForm M) = M from
      LinearMap.toMatrix₂_toLinearMapₛₗ₂ _ _ _) i) j
  rw [LinearMap.toMatrix₂_apply] at h
  exact h

/-! ## The printed form on `K⁶` -/

theorem hp_h0_toMatrix₂ :
    LinearMap.toMatrix₂ (Pi.basisFun _ (Fin 6)) (Pi.basisFun _ (Fin 6)) hp_h0Form =
      g32H0 hp_zeta :=
  LinearMap.toMatrix₂_toLinearMapₛₗ₂ _ _ _

theorem hp_h0_det : (g32H0 hp_zeta).det = -2 / 81 :=
  papers_g32_h0_det _ hp_zeta_rel

theorem hp_h0_isSymm_aux : hp_h0Form.IsSymm := by
  rw [LinearMap.isSymm_iff_isHermitian_toMatrix (Pi.basisFun _ (Fin 6)), hp_h0_toMatrix₂,
    hp_zeta_eq]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    ext <;> simp [g32H0, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat, QuadraticAlgebra.norm_def] <;>
    norm_num

theorem hp_h0_nondegenerate_aux : hp_h0Form.Nondegenerate := by
  rw [nondegenerate_iff_gramDet_ne_zero hp_h0_isSymm_aux (Pi.basisFun _ (Fin 6)), gramDet,
    hp_h0_toMatrix₂, hp_h0_det]
  norm_num

theorem hp_h0_hermSignature_aux : hermSignature hp_h0Form = (3, 3) := by
  have hs := papers_g32_h0_signature _ hp_toComplex_zeta_aux
  rw [show hp_h0Form = hp_matrixForm (g32H0 hp_zeta) from rfl,
    hp_hermSignature_matrixForm_aux (g32H0 hp_zeta) _ hp_h0_map_complex_aux
      (papers_g32_h0_isHermitian _ hp_toComplex_zeta_aux), hs.1, hs.2]

theorem hp_h0_gramDet : gramDet hp_h0Form (Pi.basisFun _ (Fin 6)) = -2 / 81 := by
  rw [gramDet, hp_h0_toMatrix₂, hp_h0_det]

theorem hp_h0_gramDetℚ : gramDetℚ hp_h0Form (Pi.basisFun _ (Fin 6)) = -2 / 81 := by
  have h : (-2 / 81 : QuadraticAlgebra ℚ (-3) 0) = algebraMap ℚ _ (-2 / 81) := by simp
  rw [gramDetℚ, hp_h0_gramDet, h, QuadraticAlgebra.algebraMap_re]

theorem hp_h0_detClass_aux :
    detClass hp_h0Form hp_h0_isSymm_aux hp_h0_nondegenerate_aux = classNegTwo := by
  rw [detClass_eq hp_h0_isSymm_aux hp_h0_nondegenerate_aux (Pi.basisFun _ (Fin 6)), classNegTwo,
    ← classes_F1569.1]
  exact congrArg (fun u : ℚˣ => (u : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)))
    (Units.ext hp_h0_gramDetℚ)

theorem hp_h0_landherr_aux :
    ∃ g : (Fin 6 → QuadraticAlgebra ℚ (-3) 0) ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
        (Fin 6 → QuadraticAlgebra ℚ (-3) 0),
      ∀ x y, b60_H (g x) (g y) = hp_h0Form x y := by
  obtain ⟨g, hg⟩ := HermitianClass.hermClass_rank_six_standard _ hp_h0Form hp_h0_isSymm_aux
    hp_h0_nondegenerate_aux (by simp) hp_h0_hermSignature_aux hp_h0_detClass_aux
  exact ⟨g, hg⟩

/-! ## The bridge -/

theorem hp_parabolic_of_disc_aux (P : g32t_Sixfold) (h : g32t_PolarizedWeil P)
    (hd : g32t_disc h = classNegTwo) :
    let hT := torusCohomology_cupProductOf P.X
    letI := hT.finite
    let E := polarizationForm hT h.nondegenerate
    let J := ⟨P.W.J, P.W.J_sq⟩
    let H := weilHermitian E J
      (by simpa [E, polarizationForm] using
        (isRosatiSkew_iff_dualForm h.nondegenerate P.W.J).1 h.rosati)
    ∃ e : Module.Basis (Fin 6) (QuadraticAlgebra ℚ (-3) 0) (WithJ (HQ P.X 1) J),
      LinearMap.toMatrix₂ e e H = g32H0 hp_zeta := by
  intro hT E J H
  have hP : g32t_IsMember P := (g32t_isMember_iff P).2 ⟨h, hd⟩
  obtain ⟨f, hf⟩ := b60c_landherr P hP
  obtain ⟨g, hg⟩ := hp_h0_landherr_aux
  refine ⟨_, hp_toMatrix₂_of_isometry_aux H (g32H0 hp_zeta) (f.trans g.symm) fun x y => ?_⟩
  change hp_h0Form (g.symm (f x)) (g.symm (f y)) = H x y
  rw [← hg, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact hf x y

theorem hp_parabolicPolarization_of_disc_aux (P : g32t_Sixfold) (h : g32t_PolarizedWeil P)
    (hd : g32t_disc h = classNegTwo) :
    g32d_ParabolicPolarization h := by
  obtain ⟨e, he⟩ := hp_parabolic_of_disc_aux P h hd
  exact ⟨⟨1, one_pos⟩, e, by simpa [hp_zeta] using he⟩

end HodgeLean.Foundations.Program
