import HodgeLean.Foundations.Program.PrymParabolicGeometricMarkingDefs

/-! # Algebra for the H7 geometric transport

Linear algebra on the saturated rational cellular lattice: the Weil form of a restricted integral
form on pure tensors, skewness from centre invariance, and the scale identity of statement 1 from
an isotypic duality relation with a fixed Schur constant.
HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Foundations.WeilHermitian
open HodgeLean.Foundations.HermitianForm
namespace HodgeLean.Foundations.Program

/-- The Weil form of the restriction on pure tensors is the integral Weil value `hga_cellWeil`. -/
theorem hg7g_cellH_tmul (B : LinearMap.BilinForm ℤ (hg2_H1 ℤ b4b_root))
    (hskew : ∀ x y, (hg7g_cellForm B).baseChange ℚ (hg7_cellAction.1 x) y =
      -(hg7g_cellForm B).baseChange ℚ x (hg7_cellAction.1 y)) (a w : hg6_cellLattice) :
    hg7g_cellH B hskew ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a))
      ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ w)) = hga_cellWeil B a w := by
  ext
  · change (hg7g_cellForm B).baseChange ℚ ((1 : ℚ) ⊗ₜ a) (hg6_cellJ ((1 : ℚ) ⊗ₜ w)) = _
    rw [show hg6_cellJ ((1 : ℚ) ⊗ₜ w) = (1 : ℚ) ⊗ₜ hg6_cellOperator w from rfl,
      LinearMap.BilinForm.baseChange_tmul]
    simp [hga_cellWeil, hg7g_cellForm]
  · change (hg7g_cellForm B).baseChange ℚ ((1 : ℚ) ⊗ₜ a) ((1 : ℚ) ⊗ₜ w) = _
    rw [LinearMap.BilinForm.baseChange_tmul]
    simp [hga_cellWeil, hg7g_cellForm]

/-- A rational pure tensor is a rational multiple of `1 ⊗ a` in the `K`-structure. -/
theorem hg7g_tmul_eq_smul (q : ℚ) (a : hg6_cellLattice) :
    (WithJ.equiv hg7_cellAction).symm (q ⊗ₜ a) =
      (algebraMap ℚ hp_K q) • (WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a) := by
  rw [algebraMap_smul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

local notation "𝕎" => WithJ (ℚ ⊗[ℤ] hg6_cellLattice) hg7_cellAction

/-- A conjugate-linear map on the rational cellular lattice is determined by its values on
integral pure tensors. -/
theorem hg7g_semilinear_ext {M : Type*} [AddCommGroup M] [Module hp_K M]
    (f g : 𝕎 →ₗ⋆[hp_K] M) (h : ∀ a : hg6_cellLattice, f ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a)) = g ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a))) : f = g := by
  refine LinearMap.ext fun x ↦ ?_
  have h2 : ∀ u : ℚ ⊗[ℤ] hg6_cellLattice,
      f ((WithJ.equiv hg7_cellAction).symm u) = g ((WithJ.equiv hg7_cellAction).symm u) := by
    intro u
    induction u using TensorProduct.inductionOn with
    | tmul q b => rw [hg7g_tmul_eq_smul q b, f.map_smulₛₗ, g.map_smulₛₗ, h]
    | add u w hu hw =>
      rw [LinearEquiv.map_add]
      exact (f.map_add _ _).trans ((congrArg₂ (· + ·) hu hw).trans (g.map_add _ _).symm)
  have h3 := h2 ((WithJ.equiv hg7_cellAction) x)
  rwa [LinearEquiv.symm_apply_apply] at h3

/-- A linear map on the rational cellular lattice is determined by its values on integral pure
tensors. -/
theorem hg7g_linear_ext {M : Type*} [AddCommGroup M] [Module hp_K M]
    (f g : 𝕎 →ₗ[hp_K] M) (h : ∀ a : hg6_cellLattice, f ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a)) = g ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a))) : f = g := by
  refine LinearMap.ext fun x ↦ ?_
  have h2 : ∀ u : ℚ ⊗[ℤ] hg6_cellLattice,
      f ((WithJ.equiv hg7_cellAction).symm u) = g ((WithJ.equiv hg7_cellAction).symm u) := by
    intro u
    induction u using TensorProduct.inductionOn with
    | tmul q b => rw [hg7g_tmul_eq_smul q b, f.map_smul, g.map_smul, h]
    | add u w hu hw =>
      rw [LinearEquiv.map_add]
      exact (f.map_add _ _).trans ((congrArg₂ (· + ·) hu hw).trans (g.map_add _ _).symm)
  have h3 := h2 ((WithJ.equiv hg7_cellAction) x)
  rwa [LinearEquiv.symm_apply_apply] at h3

/-- Two sesquilinear forms on the rational cellular lattice agreeing on integral pure tensors
agree. -/
theorem hg7g_sesq_ext (H H' : 𝕎 →ₗ⋆[hp_K] 𝕎 →ₗ[hp_K] hp_K)
    (h : ∀ a b : hg6_cellLattice, H ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a)) ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ b)) = H' ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a)) ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ b))) :
    ∀ x y, H x y = H' x y := by
  have h1 : H = H' := hg7g_semilinear_ext H H' fun a ↦
    hg7g_linear_ext (H ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a))) (H' ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a))) (h a)
  intro x y
  rw [h1]

/-- A function on the rational cellular lattice that is additive and commutes with rational
scalars is determined by its values on integral pure tensors. -/
theorem hg7g_additive_ext (f g : 𝕎 → hp_K)
    (hf : ∀ x y, f (x + y) = f x + f y) (hg : ∀ x y, g (x + y) = g x + g y)
    (hfs : ∀ (q : ℚ) x, f (algebraMap ℚ hp_K q • x) = algebraMap ℚ hp_K q * f x)
    (hgs : ∀ (q : ℚ) x, g (algebraMap ℚ hp_K q • x) = algebraMap ℚ hp_K q * g x)
    (h : ∀ a : hg6_cellLattice, f ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a)) =
      g ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a))) : ∀ x, f x = g x := by
  have h2 : ∀ u : ℚ ⊗[ℤ] hg6_cellLattice,
      f ((WithJ.equiv hg7_cellAction).symm u) = g ((WithJ.equiv hg7_cellAction).symm u) := by
    intro u
    induction u using TensorProduct.inductionOn with
    | tmul q b => rw [hg7g_tmul_eq_smul q b, hfs, hgs, h]
    | add u w hu hw =>
      have e1 : (WithJ.equiv hg7_cellAction).symm (u + w) =
          (WithJ.equiv hg7_cellAction).symm u + (WithJ.equiv hg7_cellAction).symm w :=
        map_add _ _ _
      rw [e1]
      exact (hf _ _).trans ((congrArg₂ (· + ·) hu hw).trans (hg _ _).symm)
  intro x
  have h3 := h2 ((WithJ.equiv hg7_cellAction) x)
  rwa [LinearEquiv.symm_apply_apply] at h3

/-- The coefficients of the functional `H x` in the coordinates of H7's evaluation, namely
`H x (ev⁻¹ eᵢ)`.
Source: Bourbaki, *Algebra*, Ch. II, §2 (coordinates of a linear form); `hg7_evaluation`,
`hg7_evaluation_bijective`. -/
def hg7g_coeff (H : 𝕎 →ₗ⋆[hp_K] 𝕎 →ₗ[hp_K] hp_K) (x : 𝕎) : Fin 6 → hp_K := fun i ↦
  H x ((LinearEquiv.ofBijective hg7_evaluation hg7_evaluation_bijective).symm (Pi.single i 1))

example (H : 𝕎 →ₗ⋆[hp_K] 𝕎 →ₗ[hp_K] hp_K) : hg7g_coeff H 0 = 0 := by
  funext i
  simp [hg7g_coeff]

/-- `H x y` is the coefficient vector of `H x` against the evaluation of `y`. -/
theorem hg7g_coeff_expand (H : 𝕎 →ₗ⋆[hp_K] 𝕎 →ₗ[hp_K] hp_K) (x y : 𝕎) :
    H x y = hg7g_coeff H x ⬝ᵥ hg7_evaluation y := by
  let e := LinearEquiv.ofBijective hg7_evaluation hg7_evaluation_bijective
  have hy : y = e.symm (∑ i, hg7_evaluation y i • Pi.single i (1 : hp_K)) := by
    have hs : (∑ i, hg7_evaluation y i • Pi.single i (1 : hp_K)) = e y := by
      rw [show e y = hg7_evaluation y from rfl]
      conv_rhs => rw [← Finset.univ_sum_single (hg7_evaluation y)]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    rw [hs, LinearEquiv.symm_apply_apply]
  conv_lhs => rw [hy]
  rw [map_sum, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [LinearEquiv.map_smul, LinearMap.map_smul, smul_eq_mul, mul_comm]
  rfl

theorem hg7g_coeff_smul (H : 𝕎 →ₗ⋆[hp_K] 𝕎 →ₗ[hp_K] hp_K) (z : hp_K) (x : 𝕎) :
    hg7g_coeff H (z • x) = star z • hg7g_coeff H x := by
  funext i
  simp only [hg7g_coeff, LinearMap.map_smulₛₗ₂, starRingEnd_apply,
    Pi.smul_apply]

theorem hg7g_coeff_add (H : 𝕎 →ₗ⋆[hp_K] 𝕎 →ₗ[hp_K] hp_K) (x y : 𝕎) :
    hg7g_coeff H (x + y) = hg7g_coeff H x + hg7g_coeff H y := by
  funext i
  simp only [hg7g_coeff, map_add, LinearMap.add_apply, Pi.add_apply]

/-- For a left-nondegenerate form every coefficient vector occurs. -/
theorem hg7g_coeff_surjective (H : 𝕎 →ₗ⋆[hp_K] 𝕎 →ₗ[hp_K] hp_K)
    (hnd : ∀ x, (∀ y, H x y = 0) → x = 0) (v : Fin 6 → hp_K) :
    ∃ y, hg7g_coeff H y = v := by
  let ℓ : 𝕎 →ₗ[hp_K] (Fin 6 → hp_K) :=
    { toFun := fun x ↦ star (hg7g_coeff H x)
      map_add' := fun x y ↦ by rw [hg7g_coeff_add, star_add]
      map_smul' := fun z x ↦ by
        rw [hg7g_coeff_smul, star_smul, star_star]
        rfl }
  have hi : Function.Injective ℓ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [Submodule.mem_bot]
    have h0 : hg7g_coeff H x = 0 := by
      have h1 : star (hg7g_coeff H x) = 0 := hx
      simpa using congrArg star h1
    refine hnd x fun y ↦ ?_
    rw [hg7g_coeff_expand, h0, zero_dotProduct]
  have hd : Module.finrank hp_K 𝕎 = Module.finrank hp_K (Fin 6 → hp_K) := by
    rw [b64b_rank_six _ (Classical.choice hg6_cellLattice_basis) hg7_cellAction,
      Module.finrank_fin_fun]
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).1 hi (star v)
  refine ⟨y, ?_⟩
  have h1 : star (hg7g_coeff H y) = star v := hy
  simpa using congrArg star h1

open Matrix in
/-- A row relation `24 w = conj(m) G` with the Hermitian invertible cup Gram matrix gives
`m = 24 G⁻¹ conj(w)`. -/
theorem hg7g_coeff_of_row (m w : Fin 6 → hp_K)
    (hrow' : ∀ j, 24 * w j = (star m ᵥ* hg7_cupGram) j) :
    m = (24 : hp_K) • (hg7_cupGram⁻¹ *ᵥ star w) := by
  have hrow : (24 : hp_K) • w = star m ᵥ* hg7_cupGram := funext hrow'
  obtain ⟨hh, hn, -⟩ := hg7_cup_properties
  have hG : hg7_cupGram.IsHermitian := (hg7_matrix_symm hg7_cupGram).1 hh
  have hdet : hg7_cupGram.det ≠ 0 := (hg7_matrix_nondegenerate hg7_cupGram hh).1 hn
  have h24 : star (24 : hp_K) = 24 := by
    ext <;> simp
  have hcol : hg7_cupGram *ᵥ m = (24 : hp_K) • star w := by
    have h2 := congrArg star hrow
    rw [star_vecMul, star_star, hG.eq, star_smul, h24] at h2
    exact h2.symm
  have hinv : hg7_cupGram⁻¹ * hg7_cupGram = 1 := nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet)
  calc m = (hg7_cupGram⁻¹ * hg7_cupGram) *ᵥ m := by rw [hinv, one_mulVec]
    _ = hg7_cupGram⁻¹ *ᵥ ((24 : hp_K) • star w) := by rw [← mulVec_mulVec, hcol]
    _ = _ := by rw [mulVec_smul]

theorem hg7g_cellular_apply (x y : 𝕎) :
    hg7_cellularForm x y =
      hp_matrixForm hg7_cupGram⁻¹.transpose (hg7_evaluation x) (hg7_evaluation y) := rfl

open Matrix in
theorem hg7g_dual_dot (u v : Fin 6 → hp_K) :
    ((24 : hp_K) • (hg7_cupGram⁻¹ *ᵥ star u)) ⬝ᵥ v =
      24 * hp_matrixForm hg7_cupGram⁻¹.transpose u v := by
  rw [hg7_matrix_value, smul_dotProduct, smul_eq_mul, dotProduct_mulVec, vecMul_transpose]

open Matrix in
/-- Under the Gram relation the coefficient vector of an integral pure tensor is
`24 G⁻¹ conj(ev a)`. -/
theorem hg7g_coeff_of_gram (H : 𝕎 →ₗ⋆[hp_K] 𝕎 →ₗ[hp_K] hp_K)
    (hnd : ∀ x, (∀ y, H x y = 0) → x = 0)
    (hgram : ∀ (a : hg6_cellLattice) (y : 𝕎),
      24 * H y ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a)) =
        hp_matrixForm hg7_cupGram
          (hg7g_coeff H ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a))) (hg7g_coeff H y))
    (a : hg6_cellLattice) :
    hg7g_coeff H ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a)) =
      (24 : hp_K) • (hg7_cupGram⁻¹ *ᵥ
        star (hg7_evaluation ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a)))) := by
  apply hg7g_coeff_of_row
  intro j
  obtain ⟨y, hy⟩ := hg7g_coeff_surjective H hnd (Pi.single j 1)
  have h1 := hgram a y
  rw [hg7g_coeff_expand H y, hy, single_dotProduct, one_mul, hg7_matrix_value,
    dotProduct_mulVec, dotProduct_single, mul_one] at h1
  exact h1

/-- The first argument of a sesquilinear form commutes with rational scalars. -/
theorem hg7g_rat_smul_left (H : 𝕎 →ₗ⋆[hp_K] 𝕎 →ₗ[hp_K] hp_K) (q : ℚ) (x y : 𝕎) :
    H (algebraMap ℚ hp_K q • x) y = algebraMap ℚ hp_K q * H x y := by
  have hq : starRingEnd hp_K (algebraMap ℚ hp_K q) = algebraMap ℚ hp_K q := by
    rw [starRingEnd_apply, ← algebraMap_star_comm, star_trivial]
  exact (LinearMap.map_smulₛₗ₂ H (algebraMap ℚ hp_K q) x y).trans
    ((congrArg (· • H x y) hq).trans (smul_eq_mul _ _))

/-- A sesquilinear identity `H = 24 H'` on integral pure tensors extends to the rational
cellular lattice. -/
theorem hg7g_scale_ext (H H' : 𝕎 →ₗ⋆[hp_K] 𝕎 →ₗ[hp_K] hp_K)
    (hpt : ∀ a b : hg6_cellLattice,
      H ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a))
          ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ b)) =
        24 * H' ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a))
          ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ b))) :
    ∀ x y, H x y = (24 : hp_K) * H' x y := by
  have h2 : ∀ (a : hg6_cellLattice) y,
      H ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a)) y =
        24 * H' ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a)) y :=
    fun a ↦ hg7g_additive_ext _ _ (fun x y ↦ map_add _ x y)
      (fun x y ↦ (congrArg (24 * ·) (map_add _ x y)).trans (mul_add _ _ _))
      (fun q x ↦ (map_smul _ _ x).trans (smul_eq_mul _ _))
      (fun q x ↦ (congrArg (24 * ·) ((map_smul _ _ x).trans (smul_eq_mul _ _))).trans
        (mul_left_comm _ _ _))
      (hpt a)
  intro x y
  have hf : ∀ x x' : 𝕎, H (x + x') y = H x y + H x' y := fun x x' ↦
    (LinearMap.congr_fun (H.map_add x x') y).trans (LinearMap.add_apply _ _ _)
  have hg : ∀ x x' : 𝕎, 24 * H' (x + x') y = 24 * H' x y + 24 * H' x' y := fun x x' ↦
    (congrArg (24 * ·) ((LinearMap.congr_fun (H'.map_add x x') y).trans
      (LinearMap.add_apply _ _ _))).trans (mul_add _ _ _)
  exact hg7g_additive_ext (fun x ↦ H x y) (fun x ↦ 24 * H' x y) hf hg
    (fun q x ↦ hg7g_rat_smul_left H q x y)
    (fun q x ↦ (congrArg (24 * ·) (hg7g_rat_smul_left H' q x y)).trans (mul_left_comm _ _ _))
    (fun a ↦ h2 a y) x

/-- **Scale from the Gram relation.** If a left-nondegenerate sesquilinear form `H` on the
rational cellular lattice satisfies `24 H(y, a) = c(a)ᴴ G c(y)` for its coefficient vectors `c`
and the cup Gram matrix `G = hg7_cupGram`, then `H = 24 · hg7_cellularForm`: the relation gives
`G c(a) = 24 conj(ev a)`, so `c(a) = 24 G⁻¹ conj(ev a)`, which is the dual Gram `(G⁻¹)ᵀ`.
Source: Bourbaki, *Algebra*, Ch. IX, §1 (dual sesquilinear forms); `hg7_cup_properties`. -/
theorem hg7g_scale_of_gram (H : 𝕎 →ₗ⋆[hp_K] 𝕎 →ₗ[hp_K] hp_K)
    (hnd : ∀ x, (∀ y, H x y = 0) → x = 0)
    (hgram : ∀ (a : hg6_cellLattice) (y : 𝕎),
      24 * H y ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a)) =
        hp_matrixForm hg7_cupGram
          (hg7g_coeff H ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a))) (hg7g_coeff H y)) :
    ∀ x y, H x y = (24 : hp_K) * hg7_cellularForm x y :=
  hg7g_scale_ext H hg7_cellularForm fun a _ ↦
    (hg7g_coeff_expand H _ _).trans ((congrArg (· ⬝ᵥ _) (hg7g_coeff_of_gram H hnd hgram a)).trans
      ((hg7g_dual_dot _ _).trans (congrArg (24 * ·) (hg7g_cellular_apply _ _).symm)))

/-! ## The certificate cocycles and the Gram relation -/

/-- The Shapiro cocycle of the `i`-th vector of H6's `K`-certificate; its class is
`hg7_classes i`.
Source: G32 v0.16, Lemma 6.2; `hg4_shapiroZ`, `hp_certK`. -/
def hg7g_certCocycle (i : Fin 6) : hg_eqCocycles hg4_sigmaK b4b_root :=
  hg4_shapiroZ hg4_sigmaK b4b_root ⟨hp_certK i, hg4_sigmaK_tuple ▸ hp_certK_mem i⟩

example (i : Fin 6) : hg7_classes i = Submodule.Quotient.mk (hg7g_certCocycle i) := rfl

theorem hg7g_eval_cert (i : Fin 6) (x : hg6_cellLattice) :
    hg7_evaluation ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ x)) i =
      hg6_thetaCocycle (hg7g_certCocycle i) ((1 : ℚ) ⊗ₜ x) := rfl

/-- The cup Gram entries are the normalized cup forms of the certificate cocycles. -/
theorem hg7g_cert_gram (i j : Fin 6) :
    (1 + 2 * pc_zeta) * hg4_cupForm b4b_root 1 (hg7g_certCocycle i).1 (hg7g_certCocycle j).1 =
      hg7_cupGram i j := by
  have hs := hg6_coordCup_schur (hg7g_certCocycle i).1 (hg7g_certCocycle j).1
    (hg7g_certCocycle i).2.1 (hg7g_certCocycle j).2.1 0 0
  simp only [ite_true] at hs
  change _ = (1 + 2 * pc_zeta) * (4 * hg6_coordCup b4b_root 0 0
    (hg7g_certCocycle i).1 (hg7g_certCocycle j).1)
  rw [hs, ← mul_assoc (4 : hp_K), mul_inv_cancel₀ (by norm_num : (4 : hp_K) ≠ 0), one_mul]

/-- The comparison of a combination of certificate cocycles is the dot product with the
evaluation. -/
theorem hg7g_theta_combination (m : Fin 6 → hp_K) (x : hg6_cellLattice) :
    hg6_thetaCocycle (∑ i, m i • hg7g_certCocycle i) ((1 : ℚ) ⊗ₜ x) =
      m ⬝ᵥ hg7_evaluation ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ x)) := by
  rw [map_sum, LinearMap.sum_apply, dotProduct]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hg7g_eval_cert]

/-- The normalized cup form of two combinations of certificate cocycles is the cup Gram form of
their coefficient vectors. -/
theorem hg7g_cup_combination (m n : Fin 6 → hp_K) :
    (1 + 2 * pc_zeta) * hg4_cupForm b4b_root 1 (∑ i, m i • hg7g_certCocycle i).1
        (∑ j, n j • hg7g_certCocycle j).1 = hp_matrixForm hg7_cupGram m n := by
  rw [hg7_matrix_value, Submodule.coe_sum, Submodule.coe_sum]
  simp only [Submodule.coe_smul, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply, Finset.mul_sum,
    dotProduct, Matrix.mulVec, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← hg7g_cert_gram]
  ring

theorem hg7g_star_algebraMap (q : ℚ) : star (algebraMap ℚ hp_K q) = algebraMap ℚ hp_K q := by
  rw [← algebraMap_star_comm, star_trivial]

/-- The combination of certificate cocycles with the coefficients of `H (1 ⊗ a)` evaluates to the
Weil value of `a`. -/
theorem hg7g_dual_combination (B : LinearMap.BilinForm ℤ (hg2_H1 ℤ b4b_root))
    (hskew : ∀ x y, (hg7g_cellForm B).baseChange ℚ (hg7_cellAction.1 x) y =
      -(hg7g_cellForm B).baseChange ℚ x (hg7_cellAction.1 y)) (a x : hg6_cellLattice) :
    hg6_evalVec hg4_sigmaK b4b_root (∑ i, hg7g_coeff (hg7g_cellH B hskew)
        ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a)) i • hg7g_certCocycle i) x 0 =
      hga_cellWeil B a x := by
  have h := hg7g_theta_combination (hg7g_coeff (hg7g_cellH B hskew)
    ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a))) x
  rw [hg6_thetaCocycle_tmul, one_smul, ← hg7g_coeff_expand, hg7g_cellH_tmul] at h
  exact h

/-- **The Gram relation from isotypic duality.** If the restricted integral form satisfies H4's
duality relation with Schur constant `24`, then its Weil form satisfies the Gram relation of
`hg7g_scale_of_gram` with the cup Gram matrix.
Source: `hga_isotypic_weil`, `hg6_coordCup_schur`, `hg7_cupGram`. -/
theorem hg7g_gram_of_relation (B : LinearMap.BilinForm ℤ (hg2_H1 ℤ b4b_root))
    (hskew : ∀ x y, (hg7g_cellForm B).baseChange ℚ (hg7_cellAction.1 x) y =
      -(hg7g_cellForm B).baseChange ℚ x (hg7_cellAction.1 y))
    (hrel : ∀ (c c' : hg_eqCocycles hg4_sigmaK b4b_root) (a b : hg6_cellLattice),
      (∀ x : hg6_cellLattice, hg6_evalVec hg4_sigmaK b4b_root c x 0 = hga_cellWeil B a x) →
      (∀ x : hg6_cellLattice, hg6_evalVec hg4_sigmaK b4b_root c' x 0 = hga_cellWeil B b x) →
      (1 + 2 * pc_zeta) * hg4_cupForm b4b_root 1 c.1 c'.1 = 24 * hga_cellWeil B b a)
    (a : hg6_cellLattice) (y : 𝕎) :
    24 * hg7g_cellH B hskew y ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a)) =
      hp_matrixForm hg7_cupGram
        (hg7g_coeff (hg7g_cellH B hskew) ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a)))
        (hg7g_coeff (hg7g_cellH B hskew) y) := by
  let H := hg7g_cellH B hskew
  let m := hg7g_coeff H ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a))
  have hpure : ∀ b : hg6_cellLattice,
      24 * H ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ b))
          ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a)) =
        hp_matrixForm hg7_cupGram m
          (hg7g_coeff H ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ b))) := by
    intro b
    have hr := hrel _ _ a b (hg7g_dual_combination B hskew a) (hg7g_dual_combination B hskew b)
    rw [hg7g_cup_combination] at hr
    rw [hr, hg7g_cellH_tmul]
  have hf : ∀ x x' : 𝕎, 24 * H (x + x') ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a)) =
      24 * H x ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a)) +
        24 * H x' ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a)) := fun x x' ↦
    (congrArg (24 * ·) ((LinearMap.congr_fun (H.map_add x x') _).trans
      (LinearMap.add_apply _ _ _))).trans (mul_add _ _ _)
  have hg : ∀ x x' : 𝕎, hp_matrixForm hg7_cupGram m (hg7g_coeff H (x + x')) =
      hp_matrixForm hg7_cupGram m (hg7g_coeff H x) +
        hp_matrixForm hg7_cupGram m (hg7g_coeff H x') := fun x x' ↦ by
    rw [hg7g_coeff_add, map_add]
  have hgs : ∀ (q : ℚ) (x : 𝕎), hp_matrixForm hg7_cupGram m (hg7g_coeff H (algebraMap ℚ hp_K q • x)) =
      algebraMap ℚ hp_K q * hp_matrixForm hg7_cupGram m (hg7g_coeff H x) := fun q x ↦ by
    rw [hg7g_coeff_smul, hg7g_star_algebraMap, map_smul, smul_eq_mul]
  exact hg7g_additive_ext
    (fun x ↦ 24 * H x ((WithJ.equiv hg7_cellAction).symm ((1 : ℚ) ⊗ₜ a)))
    (fun x ↦ hp_matrixForm hg7_cupGram m (hg7g_coeff H x)) hf hg
    (fun q x ↦ (congrArg (24 * ·) (hg7g_rat_smul_left H q x _)).trans (mul_left_comm _ _ _))
    hgs hpure y

/-! ## Skewness and nondegeneracy on the saturated cellular lattice -/

/-- A centre-invariant form makes `J = 1 + 2Z` skew on the rationalized restriction. -/
theorem hg7g_cell_skew (B : LinearMap.BilinForm ℤ (hg2_H1 ℤ b4b_root))
    (hC : ∀ x y, B (hg6_cellCentre x) (hg6_cellCentre y) = B x y) :
    ∀ x y, (hg7g_cellForm B).baseChange ℚ (hg7_cellAction.1 x) y =
      -(hg7g_cellForm B).baseChange ℚ x (hg7_cellAction.1 y) :=
  b64b_baseChange_skew hg6_cellLattice (hg7g_cellForm B) hg6_cellOperator
    (hga_cellOperator_skew_of_centre_invariant B hC)

/-- Nondegeneracy on cellular `H₁` restricts to the saturated lattice for a deck-invariant form:
the projector is self-adjoint and acts on the lattice by its nonzero denominator. -/
theorem hg7g_lattice_nondeg (B : LinearMap.BilinForm ℤ (hg2_H1 ℤ b4b_root))
    (hB : ∀ g x y, B (hg2_H1act ℤ b4b_root g x) (hg2_H1act ℤ b4b_root g y) = B x y)
    (hfull : ∀ u, (∀ z, B u z = 0) → u = 0) :
    ∀ a : hg6_cellLattice, (∀ w, hg7g_cellForm B a w = 0) → a = 0 := by
  intro a ha
  apply Subtype.ext
  apply hfull
  intro z
  have h1 : B a.val (hg2_projector z) = 0 := ha ⟨hg2_projector z, hg6_projector_mem_lattice z⟩
  rw [← hga_projector_selfAdjoint B hB, hga_projector_on_lattice a, map_zsmul,
    LinearMap.smul_apply, smul_eq_mul] at h1
  have hD : b4b_projectorDenominator ≠ 0 := by norm_num [b4b_projectorDenominator]
  exact (mul_eq_zero.mp h1).resolve_left hD

/-- An integral form nondegenerate on the saturated lattice has a left-nondegenerate Weil form
on its rationalization. -/
theorem hg7g_cellH_left_nondeg (B : LinearMap.BilinForm ℤ (hg2_H1 ℤ b4b_root))
    (hskew : ∀ x y, (hg7g_cellForm B).baseChange ℚ (hg7_cellAction.1 x) y =
      -(hg7g_cellForm B).baseChange ℚ x (hg7_cellAction.1 y))
    (hinj : ∀ a : hg6_cellLattice, (∀ w, hg7g_cellForm B a w = 0) → a = 0) :
    ∀ x, (∀ y, hg7g_cellH B hskew x y = 0) → x = 0 := by
  obtain ⟨b⟩ := hg6_cellLattice_basis
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  have hi := (b2bpol_flat_bijective hg6_cellLattice (hg7g_cellForm B) hinj).1
  intro x hx
  have hE : ∀ v, (hg7g_cellForm B).baseChange ℚ (WithJ.equiv hg7_cellAction x) v = 0 := by
    intro v
    have h1 := congrArg QuadraticAlgebra.im (hx ((WithJ.equiv hg7_cellAction).symm v))
    exact h1
  have h0 : WithJ.equiv hg7_cellAction x = 0 := by
    apply hi
    ext v
    rw [b2bpol_flat_apply, hE]
    rfl
  exact (WithJ.equiv hg7_cellAction).injective (h0.trans (map_zero _).symm)

/-! ## The determinant class of a multiple of the cup-dual form -/

/-- A form equal to `24 · hg7_cellularForm` is Hermitian, nondegenerate and of class `[−2]`.
Source: `hg7_scale_class` (`24⁶ = N(24³)`), `hg7_cellular_hermitian`,
`hg7_cellular_discriminant`. -/
theorem hg7g_class_of_scale (H : 𝕎 →ₗ⋆[hp_K] 𝕎 →ₗ[hp_K] hp_K)
    (hscale : ∀ x y, H x y = (24 : hp_K) * hg7_cellularForm x y) :
    ∃ hh : H.IsSymm, ∃ hn : H.Nondegenerate, detClass H hh hn = classNegTwo := by
  have heq : H = ((24 : ℚ) : hp_K) • hg7_cellularForm :=
    LinearMap.ext fun x ↦ LinearMap.ext fun y ↦
      (hscale x y).trans (congrArg (· * hg7_cellularForm x y) (Rat.cast_ofNat 24).symm)
  obtain ⟨hh₀, hn₀⟩ := hg7_cellular_hermitian
  let bK : Module.Basis (Fin 6) hp_K 𝕎 := (Pi.basisFun hp_K (Fin 6)).map
    (LinearEquiv.ofBijective hg7_evaluation hg7_evaluation_bijective).symm
  have : Module.Finite hp_K 𝕎 := Module.Finite.of_basis bK
  obtain ⟨hs, ns, hd⟩ := hg7_scale_class bK hg7_cellularForm hh₀ hn₀ 24 (by norm_num)
  subst heq
  exact ⟨hs, ns, hd.trans (hg7_cellular_discriminant hh₀ hn₀)⟩

/-! ## Transport of Weil forms along `J`-equivariant equivalences -/

section Transport

variable {V V' : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup V'] [Module ℚ V'] {a : ℚ}

/-- A rational equivalence intertwining the quadratic actions is `K`-linear between the
`WithJ` spaces.
Source: restriction of scalars along `ℚ[J] ≅ ℚ(√a)`; `WithJ`, `equiv_smul`. -/
def hg7g_withJEquiv (J : {J : V →ₗ[ℚ] V // J ∘ₗ J = a • LinearMap.id})
    (J' : {J : V' →ₗ[ℚ] V' // J ∘ₗ J = a • LinearMap.id}) (φ : V ≃ₗ[ℚ] V')
    (hφ : ∀ v, φ (J.1 v) = J'.1 (φ v)) :
    WithJ V J ≃ₗ[QuadraticAlgebra ℚ a 0] WithJ V' J' where
  toFun x := (WithJ.equiv J').symm (φ (WithJ.equiv J x))
  invFun y := (WithJ.equiv J).symm (φ.symm (WithJ.equiv J' y))
  map_add' x y := by simp only [map_add]
  map_smul' z x := by
    apply (WithJ.equiv J').injective
    simp only [LinearEquiv.apply_symm_apply, equiv_smul, map_add, map_smul, hφ,
      RingHom.id_apply]
  left_inv x := by simp only [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  right_inv y := by simp only [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]

example (J : {J : V →ₗ[ℚ] V // J ∘ₗ J = a • LinearMap.id}) :
    hg7g_withJEquiv J J (LinearEquiv.refl ℚ V) (fun _ ↦ rfl) = LinearEquiv.refl _ _ := rfl

theorem hg7g_withJEquiv_apply (J : {J : V →ₗ[ℚ] V // J ∘ₗ J = a • LinearMap.id})
    (J' : {J : V' →ₗ[ℚ] V' // J ∘ₗ J = a • LinearMap.id}) (φ : V ≃ₗ[ℚ] V')
    (hφ : ∀ v, φ (J.1 v) = J'.1 (φ v)) (x : WithJ V J) :
    WithJ.equiv J' (hg7g_withJEquiv J J' φ hφ x) = φ (WithJ.equiv J x) := rfl

/-- An isometry intertwining the quadratic actions is an isometry of the Weil forms. -/
theorem hg7g_weil_transport (E : LinearMap.BilinForm ℚ V) (E' : LinearMap.BilinForm ℚ V')
    (J : {J : V →ₗ[ℚ] V // J ∘ₗ J = a • LinearMap.id})
    (J' : {J : V' →ₗ[ℚ] V' // J ∘ₗ J = a • LinearMap.id})
    (hs : ∀ x y, E (J.1 x) y = -E x (J.1 y)) (hs' : ∀ x y, E' (J'.1 x) y = -E' x (J'.1 y))
    (φ : V ≃ₗ[ℚ] V') (hφ : ∀ v, φ (J.1 v) = J'.1 (φ v)) (hiso : ∀ u w, E' (φ u) (φ w) = E u w)
    (x y : WithJ V J) :
    weilHermitian E' J' hs' (hg7g_withJEquiv J J' φ hφ x) (hg7g_withJEquiv J J' φ hφ y) =
      weilHermitian E J hs x y := by
  ext
  · rw [re_weilHermitian, re_weilHermitian, hg7g_withJEquiv_apply, hg7g_withJEquiv_apply, ← hφ,
      hiso]
  · rw [im_weilHermitian, im_weilHermitian, hg7g_withJEquiv_apply, hg7g_withJEquiv_apply, hiso]

end Transport

/-- Rationalization preserves an integral isometry. -/
theorem hg7g_baseChange_isometry {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (Q₁ : LinearMap.BilinForm ℤ M) (Q₂ : LinearMap.BilinForm ℤ N) (φ : M →ₗ[ℤ] N)
    (h : ∀ a b, Q₂ (φ a) (φ b) = Q₁ a b) (u w : ℚ ⊗[ℤ] M) :
    Q₂.baseChange ℚ (φ.baseChange ℚ u) (φ.baseChange ℚ w) = Q₁.baseChange ℚ u w := by
  induction u using TensorProduct.inductionOn with
  | add u u' hu hu' => simp only [map_add, LinearMap.add_apply, hu, hu']
  | tmul q a =>
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => simp only [map_add, hw, hw']
    | tmul r b =>
      simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, h]

/-- **Transport along a centre-compatible equivalence.** If `E₀ : L ≃ Λ` carries the
restriction of a centre-invariant form `B` to `E` and `1 + 2Z` to `A`, then `A ⊗ ℚ` squares to
`−3` and is skew for `E`, and `E₀ ⊗ ℚ` is a `K`-linear isometry of the two Weil forms.
Source: Bourbaki, *Algebra*, Ch. II, §5 (extension of scalars); `hg6_cellOperator_sq`,
`hga_cellOperator_skew_of_centre_invariant`. -/
theorem hg7g_transport_of_equiv {Λ : Type*} [AddCommGroup Λ]
    (B : LinearMap.BilinForm ℤ (hg2_H1 ℤ b4b_root)) (E : LinearMap.BilinForm ℤ Λ)
    (E₀ : hg6_cellLattice ≃ₗ[ℤ] Λ) (A : Λ →ₗ[ℤ] Λ)
    (hAE : ∀ a, A (E₀ a) = E₀ (hg6_cellOperator a))
    (hZ : ∀ x y, B (hg6_cellCentre x) (hg6_cellCentre y) = B x y)
    (hEB : ∀ a b, E (E₀ a) (E₀ b) = hg7g_cellForm B a b) :
    ∃ hJ : A.baseChange ℚ ∘ₗ A.baseChange ℚ = (-3 : ℚ) • LinearMap.id,
    ∃ hskew : ∀ x y, E.baseChange ℚ (A.baseChange ℚ x) y =
        -E.baseChange ℚ x (A.baseChange ℚ y),
    ∃ hskewC : ∀ x y, (hg7g_cellForm B).baseChange ℚ (hg7_cellAction.1 x) y =
        -(hg7g_cellForm B).baseChange ℚ x (hg7_cellAction.1 y),
    ∃ e : WithJ (ℚ ⊗[ℤ] hg6_cellLattice) hg7_cellAction ≃ₗ[hp_K]
        WithJ (ℚ ⊗[ℤ] Λ) ⟨A.baseChange ℚ, hJ⟩,
      (∀ (q : ℚ) (x : hg6_cellLattice),
        WithJ.equiv _ (e ((WithJ.equiv hg7_cellAction).symm (q ⊗ₜ x))) = q ⊗ₜ E₀ x) ∧
      ∀ x y, b64b_latticeH Λ E ⟨A.baseChange ℚ, hJ⟩ hskew (e x) (e y) = hg7g_cellH B hskewC x y := by
  have hsq : ∀ x, A (A x) = (-3 : ℤ) • x := fun x ↦ by
    obtain ⟨a, rfl⟩ := E₀.surjective x
    rw [hAE, hAE, hg6_cellOperator_sq, E₀.map_smul]
  have hJ := b64b_baseChange_quadratic Λ A hsq
  have hop := hga_cellOperator_skew_of_centre_invariant B hZ
  have hz : ∀ x y, E (A x) y = -E x (A y) := fun x y ↦ by
    obtain ⟨a, rfl⟩ := E₀.surjective x
    obtain ⟨b, rfl⟩ := E₀.surjective y
    rw [hAE, hAE, hEB, hEB]
    exact hop a b
  have hskew := b64b_baseChange_skew Λ E A hz
  have hskewC := hg7g_cell_skew B hZ
  let φ := LinearEquiv.baseChange ℤ ℚ hg6_cellLattice Λ E₀
  have hcomp : E₀.toLinearMap ∘ₗ hg6_cellOperator = A ∘ₗ E₀.toLinearMap :=
    LinearMap.ext fun a ↦ (hAE a).symm
  have hφ : ∀ v, φ (hg7_cellAction.1 v) = A.baseChange ℚ (φ v) := by
    have hc : E₀.toLinearMap.baseChange ℚ ∘ₗ hg6_cellOperator.baseChange ℚ =
        A.baseChange ℚ ∘ₗ E₀.toLinearMap.baseChange ℚ := by
      rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hcomp]
    exact fun v ↦ LinearMap.congr_fun hc v
  refine ⟨hJ, hskew, hskewC, hg7g_withJEquiv hg7_cellAction ⟨A.baseChange ℚ, hJ⟩ φ hφ,
    fun q x ↦ rfl, ?_⟩
  exact hg7g_weil_transport _ _ _ _ hskewC hskew φ hφ
    (hg7g_baseChange_isometry (hg7g_cellForm B) E E₀.toLinearMap hEB)

/-- The conclusion of statement 3 for a saturated sublattice `Λ` of an ambient group, from a
centre-compatible equivalence `E₀` and an isometry `E(E₀ a, E₀ b) = B(a, b)`. -/
theorem hg7g_transport_conclusion {M : Type*} [AddCommGroup M] [Module ℤ M] (Λ : Submodule ℤ M)
    (Op : M →ₗ[ℤ] M) (toF : hg2_H1 ℤ b4b_root →ₗ[ℤ] M)
    (B : LinearMap.BilinForm ℤ (hg2_H1 ℤ b4b_root)) (E : LinearMap.BilinForm ℤ Λ)
    (E₀ : hg6_cellLattice ≃ₗ[ℤ] Λ) (h1 : ∀ x, (E₀ x : M) = toF x)
    (h3 : ∀ x, (E₀ (hg6_cellOperator x) : M) = Op (E₀ x))
    (hZ : ∀ x y, B (hg6_cellCentre x) (hg6_cellCentre y) = B x y)
    (hEB : ∀ a b, E (E₀ a) (E₀ b) = hg7g_cellForm B a b) :
    ∃ A : Λ →ₗ[ℤ] Λ, (∀ x, (A x).val = Op x.val) ∧
    ∃ hJ : A.baseChange ℚ ∘ₗ A.baseChange ℚ = (-3 : ℚ) • LinearMap.id,
    ∃ hskew : ∀ x y, E.baseChange ℚ (A.baseChange ℚ x) y =
        -E.baseChange ℚ x (A.baseChange ℚ y),
    ∃ hskewC : ∀ x y, (hg7g_cellForm B).baseChange ℚ (hg7_cellAction.1 x) y =
        -(hg7g_cellForm B).baseChange ℚ x (hg7_cellAction.1 y),
    ∃ E₀ : hg6_cellLattice ≃ₗ[ℤ] Λ, (∀ x, (E₀ x : M) = toF x) ∧
    ∃ e : WithJ (ℚ ⊗[ℤ] hg6_cellLattice) hg7_cellAction ≃ₗ[hp_K]
        WithJ (ℚ ⊗[ℤ] Λ) ⟨A.baseChange ℚ, hJ⟩,
      (∀ (q : ℚ) (x : hg6_cellLattice),
        WithJ.equiv _ (e ((WithJ.equiv hg7_cellAction).symm (q ⊗ₜ x))) = q ⊗ₜ E₀ x) ∧
      ∀ x y, b64b_latticeH Λ E ⟨A.baseChange ℚ, hJ⟩ hskew (e x) (e y) =
        hg7g_cellH B hskewC x y := by
  let A : Λ →ₗ[ℤ] Λ := E₀.toLinearMap ∘ₗ hg6_cellOperator ∘ₗ E₀.symm.toLinearMap
  have hAE : ∀ a, A (E₀ a) = E₀ (hg6_cellOperator a) := fun a ↦ by
    simp only [A, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have hA : ∀ x, (A x).val = Op x.val := fun x ↦ by
    obtain ⟨a, rfl⟩ := E₀.surjective x
    rw [hAE]
    exact h3 a
  obtain ⟨hJ, hskew, hskewC, e, he₁, he₂⟩ := hg7g_transport_of_equiv B E E₀ A hAE hZ hEB
  exact ⟨A, hA, hJ, hskew, hskewC, E₀, h1, e, he₁, he₂⟩

/-- Hermitian, nondegenerate and the determinant class transfer along a `K`-linear isometry.
Source: `HermitianClass.detClass_eq_of_equiv`. -/
theorem hg7g_class_transfer {W W' : Type*} [AddCommGroup W] [AddCommGroup W'] [Module hp_K W]
    [Module hp_K W'] [Module.Finite hp_K W] [Module.Finite hp_K W']
    (H : W →ₗ⋆[hp_K] W →ₗ[hp_K] hp_K) (H' : W' →ₗ⋆[hp_K] W' →ₗ[hp_K] hp_K)
    (e : W ≃ₗ[hp_K] W') (he : ∀ x y, H' (e x) (e y) = H x y)
    (hh : H.IsSymm) (hn : H.Nondegenerate) :
    ∃ hh' : H'.IsSymm, ∃ hn' : H'.Nondegenerate, detClass H' hh' hn' = detClass H hh hn := by
  have hh' : H'.IsSymm := ⟨fun x y ↦ by
    obtain ⟨u, rfl⟩ := e.surjective x
    obtain ⟨v, rfl⟩ := e.surjective y
    rw [he, he]
    exact hh.eq u v⟩
  have hn' : H'.Nondegenerate := by
    refine ⟨fun x hx ↦ ?_, fun y hy ↦ ?_⟩
    · obtain ⟨u, rfl⟩ := e.surjective x
      rw [hn.1 u fun v ↦ (he u v).symm.trans (hx (e v)), map_zero]
    · obtain ⟨v, rfl⟩ := e.surjective y
      rw [hn.2 v fun u ↦ (he u v).symm.trans (hy (e u)), map_zero]
  exact ⟨hh', hn', (HermitianClass.detClass_eq_of_equiv _ _ H H' hh hn hh' hn' e he).symm⟩

end HodgeLean.Foundations.Program
