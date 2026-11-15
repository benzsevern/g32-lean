import HodgeLean.Foundations.HodgeGroupAlgebraicGk
import HodgeLean.Foundations.MatrixAlgGroupLieIdentityComponent

/-! # `G_k` for `R = ℚ[J]` need not be connected (Track G2)

On `V = ℚ⁴` with `J = [[0,0,-1,0],[0,0,0,-1],[1,0,0,0],[0,1,0,0]]` (`J² = -1`, `d = 1`) and
`E` with Gram matrix `Ω = [[0,0,0,-1],[0,0,1,1/2],[0,1,0,0],[-1,-1/2,0,0]]`, the form `E` is
nondegenerate (`det Ω = 1`) and `J` is `E`-skew, but `E` is neither alternating nor symmetric.
On `V_ℂ = V₊ ⊕ V₋` the two pairings `V₊ × V₋ → ℂ` and `V₋ × V₊ → ℂ` given by `E` differ by the
unipotent operator `T = [[1,1],[0,1]]` on `V₊`, so `G_k ≅ {G ∈ SL₂(ℂ) | G T = T G} = {±(1 + s N)}`.
In coordinates, every point of `G_k` has `g₀₀ = ±1`, and both signs occur (`1` and `-1`), so
`G_k` is not Zariski connected.

This is a counterexample to the frozen statement `g2_gkGroup_isConnected_adjoin` of
`docs/specs/HodgeGroupAlgebraic.md` (statement 9), whose argument identifies `G_k` with `SL(V₊)`
through one of the two pairings only. The identification, and connectedness, hold when `E` is
alternating (or symmetric), where the two pairings agree up to sign.
-/

noncomputable section
set_option maxHeartbeats 400000

namespace HodgeLean.Foundations

open MvPolynomial

/-- The matrix of `J`. -/
def g2k_cexJ : Matrix (Fin 4) (Fin 4) ℚ := !![0, 0, -1, 0; 0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 0]

/-- The Gram matrix of `E`. -/
def g2k_cexΩ : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 0, 0, -1; 0, 0, 1, 1 / 2; 0, 1, 0, 0; -1, -1 / 2, 0, 0]

/-- The endomorphism `J` of `ℚ⁴`. -/
def g2k_cexJl : Module.End ℚ (Fin 4 → ℚ) := Matrix.toLin' g2k_cexJ

/-- The bilinear form `E` on `ℚ⁴`. -/
def g2k_cexE : LinearMap.BilinForm ℚ (Fin 4 → ℚ) := Matrix.toBilin' g2k_cexΩ

theorem g2k_cexJ_mul_self : g2k_cexJ * g2k_cexJ = (-1 : ℚ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g2k_cexJ, Matrix.mul_apply, Fin.sum_univ_four]

theorem g2k_cex_hJ : g2k_cexJl * g2k_cexJl = (-(1 : ℚ)) • (1 : Module.End ℚ (Fin 4 → ℚ)) := by
  rw [g2k_cexJl, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, g2k_cexJ_mul_self, map_smul,
    Matrix.toLin'_one]
  rfl

theorem g2k_cexΩ_det : g2k_cexΩ.det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [g2k_cexΩ, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix]
  have h : (Fin.succAbove (3 : Fin 4) 2 : Fin 4) = 2 := by decide
  rw [h]
  norm_num

theorem g2k_cex_hE : g2k_cexE.Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' _ (by rw [g2k_cexΩ_det]; norm_num)

theorem g2k_cex_hskew : ∀ x y, g2k_cexE (g2k_cexJl x) y = -g2k_cexE x (g2k_cexJl y) := by
  intro x y
  simp only [g2k_cexE, g2k_cexJl, Matrix.toBilin'_apply, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_four, g2k_cexΩ, g2k_cexJ]
  simp
  ring

/-- `E` is neither alternating nor symmetric. -/
theorem g2k_cexE_not_alt_not_symm :
    ¬ g2k_cexE.IsAlt ∧ ¬ g2k_cexE.IsSymm := by
  constructor
  · intro h
    have := h (Pi.single 1 1 + Pi.single 2 1)
    simp [g2k_cexE, Matrix.toBilin'_apply, Fin.sum_univ_four, g2k_cexΩ, Pi.single_apply] at this
  · intro h
    have := h.eq (Pi.single 1 1) (Pi.single 3 1)
    simp [g2k_cexE, g2k_cexΩ] at this
    norm_num at this

/-- The determinant of a `4 × 4` matrix. -/
theorem g2k_det_fin_four {K : Type*} [CommRing K] (A : Matrix (Fin 4) (Fin 4) K) :
    A.det =
      A 0 0 * (A 1 1 * (A 2 2 * A 3 3 - A 2 3 * A 3 2) - A 1 2 * (A 2 1 * A 3 3 - A 2 3 * A 3 1) +
          A 1 3 * (A 2 1 * A 3 2 - A 2 2 * A 3 1)) -
        A 0 1 * (A 1 0 * (A 2 2 * A 3 3 - A 2 3 * A 3 2) -
          A 1 2 * (A 2 0 * A 3 3 - A 2 3 * A 3 0) + A 1 3 * (A 2 0 * A 3 2 - A 2 2 * A 3 0)) +
        A 0 2 * (A 1 0 * (A 2 1 * A 3 3 - A 2 3 * A 3 1) -
          A 1 1 * (A 2 0 * A 3 3 - A 2 3 * A 3 0) + A 1 3 * (A 2 0 * A 3 1 - A 2 1 * A 3 0)) -
        A 0 3 * (A 1 0 * (A 2 1 * A 3 2 - A 2 2 * A 3 1) -
          A 1 1 * (A 2 0 * A 3 2 - A 2 2 * A 3 0) + A 1 2 * (A 2 0 * A 3 1 - A 2 1 * A 3 0)) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp [Fin.succAbove, Fin.lt_def]
  ring

local notation "Jc" => (!![0, 0, -1, 0; 0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 0] :
  Matrix (Fin 4) (Fin 4) ℂ)

theorem g2k_cex_Jm : g2k_Jm (Pi.basisFun ℚ (Fin 4)) g2k_cexJl = Jc := by
  rw [g2k_Jm, LinearMap.toMatrix_eq_toMatrix', g2k_cexJl, LinearMap.toMatrix'_toLin']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g2k_cexJ]

theorem g2k_cex_Ωm : (LinearMap.BilinForm.toMatrix (Pi.basisFun ℚ (Fin 4)) g2k_cexE).map
    (algebraMap ℚ ℂ) = !![0, 0, 0, -1; 0, 0, 1, 1 / 2; 0, 1, 0, 0; -1, -1 / 2, 0, 0] := by
  rw [LinearMap.BilinForm.toMatrix_basisFun, g2k_cexE, LinearMap.BilinForm.toMatrix'_toBilin']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g2k_cexΩ]

theorem g2k_cex_P : g2k_P (Pi.basisFun ℚ (Fin 4)) g2k_cexJl 1 =
    !![1 / 2, 0, Complex.I / 2, 0; 0, 1 / 2, 0, Complex.I / 2; -Complex.I / 2, 0, 1 / 2, 0;
      0, -Complex.I / 2, 0, 1 / 2] := by
  rw [g2k_P, g2k_cex_Jm, g2k_c]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply] <;> ring

theorem g2k_I_pow_three : Complex.I ^ 3 = -Complex.I := by
  rw [pow_succ, Complex.I_sq]; ring

theorem g2k_I_pow_four : Complex.I ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num

/-- **On the example, every point of `G_k` has `g₀₀ = ±1`.** -/
theorem g2k_cex_sq (g : Matrix.GeneralLinearGroup (Fin 4) ℂ)
    (hg : g ∈ g2_gkGroup (Pi.basisFun ℚ (Fin 4)) g2k_cexE (Algebra.adjoin ℚ {g2k_cexJl})
      g2k_cexJl 1) :
    (g : Matrix (Fin 4) (Fin 4) ℂ) 0 0 ^ 2 = 1 := by
  obtain ⟨-, h2, h3, h4, -⟩ :=
    (g2k_mem_gkGroup_iff (Pi.basisFun ℚ (Fin 4)) g2k_cexE _ g2k_cexJl one_pos g2k_cex_hJ g).mp hg
  rw [g2k_cex_Jm] at h2
  rw [g2k_cex_Ωm] at h3
  rw [g2k_cex_P] at h4
  set G := (g : Matrix (Fin 4) (Fin 4) ℂ) with hGdef
  have hc : ∀ i j, (G * Jc) i j = (Jc * G) i j := fun i j => by rw [h2]
  have c00 := hc 0 0
  have c01 := hc 0 1
  have c02 := hc 0 2
  have c03 := hc 0 3
  have c10 := hc 1 0
  have c11 := hc 1 1
  have c12 := hc 1 2
  have c13 := hc 1 3
  simp [Matrix.mul_apply, Fin.sum_univ_four] at c00 c01 c02 c03 c10 c11 c12 c13
  have hG : G = !![G 0 0, G 0 1, -G 2 0, -G 2 1; G 1 0, G 1 1, -G 3 0, -G 3 1;
      G 2 0, G 2 1, G 0 0, G 0 1; G 3 0, G 3 1, G 1 0, G 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;>
      first | (linear_combination c00) | (linear_combination c01) | (linear_combination c02) | (linear_combination c03) | (linear_combination c10) | (linear_combination c11) | (linear_combination c12) | (linear_combination c13) | (linear_combination -c00) | (linear_combination -c01) | (linear_combination -c02) | (linear_combination -c03) | (linear_combination -c10) | (linear_combination -c11) | (linear_combination -c12) | (linear_combination -c13)
  rw [hG] at h3 h4
  have i00 := congrFun (congrFun h3 0) 0
  have i01 := congrFun (congrFun h3 0) 1
  have i02 := congrFun (congrFun h3 0) 2
  have i03 := congrFun (congrFun h3 0) 3
  have i10 := congrFun (congrFun h3 1) 0
  have i11 := congrFun (congrFun h3 1) 1
  have i12 := congrFun (congrFun h3 1) 2
  have i13 := congrFun (congrFun h3 1) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four] at i00 i01 i02 i03 i10 i11 i12 i13
  rw [g2k_det_fin_four] at h4
  simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] at h4
  have s0 : -2*(G 0 0)*(G 3 0) + 2*(G 1 0)*(G 2 0) = 0 := by linear_combination i00
  have s1 : -(G 0 0)*(G 3 1) - (G 0 1)*(G 3 0) + (G 1 0)*(G 2 1) + (G 1 0)*(G 3 1)/2 + (G 1 1)*(G 2 0) - (G 1 1)*(G 3 0)/2 = 0 := by linear_combination i01
  have s2 : (G 1 0)^2/2 + (G 3 0)^2/2 = 0 := by linear_combination i02
  have s3 : -(G 0 0)*(G 1 1) + (G 0 1)*(G 1 0) + (G 1 0)*(G 1 1)/2 - (G 2 0)*(G 3 1) + (G 2 1)*(G 3 0) + (G 3 0)*(G 3 1)/2 + 1 = 0 := by linear_combination i03
  have s4 : -(G 0 0)*(G 3 1) - (G 0 1)*(G 3 0) + (G 1 0)*(G 2 1) - (G 1 0)*(G 3 1)/2 + (G 1 1)*(G 2 0) + (G 1 1)*(G 3 0)/2 = 0 := by linear_combination i10
  have s5 : -2*(G 0 1)*(G 3 1) + 2*(G 1 1)*(G 2 1) = 0 := by linear_combination i11
  have s6 : (G 0 0)*(G 1 1) - (G 0 1)*(G 1 0) + (G 1 0)*(G 1 1)/2 + (G 2 0)*(G 3 1) - (G 2 1)*(G 3 0) + (G 3 0)*(G 3 1)/2 - 1 = 0 := by linear_combination i12
  have s7 : (G 1 1)^2/2 + (G 3 1)^2/2 - 1/2 = 0 := by linear_combination i13
  have s12 : (G 0 0)*(G 1 1) + Complex.I*(G 0 0)*(G 3 1) - (G 0 1)*(G 1 0) - Complex.I*(G 0 1)*(G 3 0) - Complex.I*(G 1 0)*(G 2 1) + Complex.I*(G 1 1)*(G 2 0) - (G 2 0)*(G 3 1) + (G 2 1)*(G 3 0) - 1 = 0 := by
    linear_combination (norm := skip) h4
    ring_nf
    simp only [Complex.I_sq, g2k_I_pow_three, g2k_I_pow_four]
    ring_nf
  linear_combination (norm := skip) (Complex.I*(G 0 0)*(G 0 1)/2 - (G 0 0)*(G 2 1)/2 + (G 0 1)*(G 3 1) + Complex.I*(G 1 1)^2/8 + Complex.I*(G 2 1)*(G 3 1) + Complex.I*(G 3 1)^2/8) * s0 + (-Complex.I*(G 0 0)^2/4 - Complex.I*(G 0 0)*(G 0 1) + (G 0 0)*(G 2 0)/4 + (G 0 0)*(G 2 1) - (G 0 0)*(G 3 1)/2 + Complex.I*(G 0 1)*(G 1 0)/2 - (G 0 1)*(G 2 0) - (G 0 1)*(G 3 0) - Complex.I*(G 2 0)*(G 2 1) - Complex.I*(G 2 0)*(G 3 1)/2 - Complex.I*(G 2 1)*(G 3 0)/2) * s1 + (-2*(G 0 1)^2 - (G 0 1)*(G 1 1) - 2*Complex.I*(G 0 1)*(G 2 1) - Complex.I*(G 0 1)*(G 3 1)/2 - Complex.I*(G 1 1)*(G 2 1)/2) * s2 + (-(G 0 0)^2/4 + 2*(G 0 0)*(G 0 1) - (G 0 0)*(G 1 1)/2 - Complex.I*(G 0 0)*(G 2 0)/4 + 2*Complex.I*(G 0 0)*(G 2 1) + (G 0 1)*(G 1 0) + Complex.I*(G 0 1)*(G 3 0)/2 + Complex.I*(G 1 0)*(G 2 1)/2 - Complex.I*(G 1 1)*(G 2 0)/2 - 1/4) * s3 + (-Complex.I*(G 0 0)^2/4 + Complex.I*(G 0 0)*(G 0 1) + Complex.I*(G 0 0)*(G 1 1)/2 + (G 0 0)*(G 2 0)/4 - (G 0 0)*(G 2 1) - (G 0 0)*(G 3 1)/2 + (G 0 1)*(G 2 0) + Complex.I*(G 2 0)*(G 2 1)) * s4 + (-Complex.I*(G 0 0)*(G 1 0) + (G 0 0)*(G 3 0)) * s5 + ((G 0 0)^2/4 + 2*(G 0 0)*(G 0 1) + (G 0 0)*(G 1 1)/2 + Complex.I*(G 0 0)*(G 2 0)/4 + 2*Complex.I*(G 0 0)*(G 2 1) + Complex.I*(G 0 0)*(G 3 1)/2 + 1/4) * s6 + (-2*(G 0 0)^2 - 2*Complex.I*(G 0 0)*(G 2 0)) * s7 + (-(G 0 0)^2/2 + Complex.I*(G 0 0)*(G 2 0)/2 + 1/2) * s12
  ring_nf
  simp only [Complex.I_sq, g2k_I_pow_three, g2k_I_pow_four]
  ring_nf

theorem g2k_cex_neg_one_mem :
    (-1 : Matrix.GeneralLinearGroup (Fin 4) ℂ) ∈ g2_gkGroup (Pi.basisFun ℚ (Fin 4)) g2k_cexE
      (Algebra.adjoin ℚ {g2k_cexJl}) g2k_cexJl 1 := by
  rw [g2k_mem_gkGroup_iff (Pi.basisFun ℚ (Fin 4)) g2k_cexE _ g2k_cexJl one_pos g2k_cex_hJ,
    Units.val_neg, Units.val_one, g2k_cex_P]
  refine ⟨fun r _ => by rw [neg_one_mul, mul_neg_one], by rw [neg_one_mul, mul_neg_one], by simp,
    ?_, ?_⟩
  · rw [g2k_det_fin_four]
    simp [Matrix.one_apply]
    ring_nf
    simp only [Complex.I_sq, g2k_I_pow_four, neg_neg]
  · rw [g2k_det_fin_four]
    simp [Matrix.one_apply]
    ring_nf
    simp only [Complex.I_sq, g2k_I_pow_four, neg_neg]

set_option warn.classDefReducibility false in
attribute [local instance] g1_zariski in
/-- **`G_k` for `R = ℚ[J]` is not connected in general.** The data of the example satisfy every
hypothesis of the frozen statement `g2_gkGroup_isConnected_adjoin` (`d = 1 > 0`, `J² = -1`,
`E` nondegenerate, `J` skew for `E`), and `G_k` is not Zariski connected: it is covered by the
disjoint closed sets `g₀₀ = 1` (containing `1`) and `g₀₀ = -1` (containing `-1`). -/
theorem g2k_gkGroup_adjoin_not_isConnected :
    0 < (1 : ℚ) ∧ g2k_cexJl * g2k_cexJl = (-(1 : ℚ)) • (1 : Module.End ℚ (Fin 4 → ℚ)) ∧
      g2k_cexE.Nondegenerate ∧
      (∀ x y, g2k_cexE (g2k_cexJl x) y = -g2k_cexE x (g2k_cexJl y)) ∧
      ¬ IsConnected (g2_gkGroup (Pi.basisFun ℚ (Fin 4)) g2k_cexE
        (Algebra.adjoin ℚ {g2k_cexJl}) g2k_cexJl 1) := by
  refine ⟨one_pos, g2k_cex_hJ, g2k_cex_hE, g2k_cex_hskew, fun hconn => ?_⟩
  have hpre := isPreconnected_closed_iff.mp hconn.isPreconnected
  set S := g2_gkGroup (Pi.basisFun ℚ (Fin 4)) g2k_cexE (Algebra.adjoin ℚ {g2k_cexJl}) g2k_cexJl 1
  let t : Set (Matrix.GeneralLinearGroup (Fin 4) ℂ) := g1_zeroSet {X (0, 0) - 1}
  let t' : Set (Matrix.GeneralLinearGroup (Fin 4) ℂ) := g1_zeroSet {X (0, 0) + 1}
  have hmem : ∀ g, g ∈ t ↔ (g : Matrix (Fin 4) (Fin 4) ℂ) 0 0 = 1 := fun g => by
    simp [t, g1_zeroSet, g1_coords, sub_eq_zero]
  have hmem' : ∀ g, g ∈ t' ↔ (g : Matrix (Fin 4) (Fin 4) ℂ) 0 0 = -1 := fun g => by
    simp [t', g1_zeroSet, g1_coords, add_eq_zero_iff_eq_neg]
  have hcover : S ⊆ t ∪ t' := by
    intro g hg
    have h := g2k_cex_sq g hg
    have : ((g : Matrix (Fin 4) (Fin 4) ℂ) 0 0 - 1) * ((g : Matrix (Fin 4) (Fin 4) ℂ) 0 0 + 1) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · exact Or.inl ((hmem g).mpr (sub_eq_zero.mp h1))
    · exact Or.inr ((hmem' g).mpr (add_eq_zero_iff_eq_neg.mp h1))
  have h1 : (S ∩ t).Nonempty :=
    ⟨1, (g2k_isRatAlgSubgroup_gkGroup _ _ _ _ one_pos g2k_cex_hJ).2.1, (hmem 1).mpr (by simp)⟩
  have h2 : (S ∩ t').Nonempty :=
    ⟨-1, g2k_cex_neg_one_mem, (hmem' _).mpr (by simp)⟩
  obtain ⟨g, -, hgt, hgt'⟩ := hpre t t' (g1_isClosed_zeroSet _) (g1_isClosed_zeroSet _) hcover h1 h2
  have e1 := (hmem g).mp hgt
  have e2 := (hmem' g).mp hgt'
  rw [e1] at e2
  norm_num at e2

end HodgeLean.Foundations
