import HodgeLean.Foundations.Program.HeckeSpreadingDefs

/-! # Proofs for the Hecke spreading specification S1–S6

Each `_aux` theorem is restated in `HeckeSpreading.lean`.

* S1: matrix identities for the Cayley map.
* S2: the Lie algebra is the kernel of an integral matrix, so its rational points are dense
  (`hk_dense_ker`, through a generalized inverse); the Cayley chart and continuity of the
  inverse give density on `det(1 + g) ≠ 0`; a general `g` is `(a - bJ)((a + bJ) g)` with
  `J = ω/√3` and `t ↦ det((1 + g) + t J (g - 1))` a nonzero polynomial (its value at `i` is
  invertible).
* S3: an explicit element of `U(3, 3)` from the origin to `σ`, built in the eigenbasis from a
  pseudo-unitary block matrix `[[P, Aᴴ S], [A P, S]]` with `Pᴴ (1 - Aᴴ A) P = 1` and
  `Sᴴ (1 - A Aᴴ) S = 1` (spectral theorem), then made real through conjugation.
* S4: the image filtration satisfies `b60c_fixed_filtration_chart`; its matrix coordinate is
  `Q P⁻¹` for the eigen-coordinates `P`, `Q` of the moved negative frame, continuous in `g`.
* S5: the marking `e = I_τ ∘ g⁻¹ ∘ I_σ⁻¹` through the dual action of `g` on `b2b_dual`, fed to
  `b60c_uniformization`.
* S6: S3, S4b, S2, S5 and `g32tr_weilAlg_pullback`.

HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Matrix TensorProduct
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem hk_cayley_mem_unitary_aux {K : Type*} [Field K] [StarRing K] {H X : Matrix n n K}
    (hX : X ∈ hk_lie H) (hdet : (1 + X).det ≠ 0) :
    hk_cayley X ∈ hk_unitary H := by
  have hX : Xᴴ * H + H * X = 0 := hX
  set A := 1 + X with hA
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hBu : IsUnit Aᴴ.det := by
    rw [Matrix.det_conjTranspose]; exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hdet)
  have h1 : (1 - X)ᴴ * H = H * A := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.sub_mul, hA, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one]
    rw [← sub_eq_zero]
    rw [show H - Xᴴ * H - (H + H * X) = -(Xᴴ * H + H * X) by abel, hX, neg_zero]
  have h2 : H * (1 - X) = Aᴴ * H := by
    rw [hA, Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.mul_sub, Matrix.add_mul,
      Matrix.one_mul, Matrix.mul_one]
    rw [← sub_eq_zero]
    rw [show H - H * X - (H + Xᴴ * H) = -(Xᴴ * H + H * X) by abel, hX, neg_zero]
  have hc : A * (1 - X) = (1 - X) * A := by
    rw [hA]; noncomm_ring
  show (hk_cayley X)ᴴ * H * hk_cayley X = H
  unfold hk_cayley
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, ← hA]
  calc Aᴴ⁻¹ * (1 - X)ᴴ * H * ((1 - X) * A⁻¹)
      = Aᴴ⁻¹ * ((1 - X)ᴴ * H) * (1 - X) * A⁻¹ := by simp only [Matrix.mul_assoc]
    _ = Aᴴ⁻¹ * H * (A * (1 - X)) * A⁻¹ := by rw [h1]; simp only [Matrix.mul_assoc]
    _ = Aᴴ⁻¹ * (H * (1 - X)) * (A * A⁻¹) := by rw [hc]; simp only [Matrix.mul_assoc]
    _ = H := by
      rw [h2, Matrix.mul_nonsing_inv _ hAu, Matrix.mul_one, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hBu, Matrix.one_mul]

theorem hk_cayley_mem_lie_aux {K : Type*} [Field K] [StarRing K] {H g : Matrix n n K}
    (hg : g ∈ hk_unitary H) (hdet : (1 + g).det ≠ 0) :
    hk_cayley g ∈ hk_lie H := by
  have hg : gᴴ * H * g = H := hg
  set A := 1 + g with hA
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hBu : IsUnit Aᴴ.det := by
    rw [Matrix.det_conjTranspose]; exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hdet)
  show (hk_cayley g)ᴴ * H + H * hk_cayley g = 0
  unfold hk_cayley
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, ← hA]
  clear_value A
  have key : Aᴴ * (Aᴴ⁻¹ * (1 - g)ᴴ * H + H * ((1 - g) * A⁻¹)) * A = 0 := by
    have e1 : Aᴴ * (Aᴴ⁻¹ * (1 - g)ᴴ * H) * A = (1 - g)ᴴ * H * A := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBu, Matrix.one_mul,
        Matrix.mul_assoc]
    have e2 : Aᴴ * (H * ((1 - g) * A⁻¹)) * A = Aᴴ * H * (1 - g) := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu, Matrix.mul_one]
    rw [Matrix.mul_add, Matrix.add_mul, e1, e2, hA, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_add, Matrix.conjTranspose_one]
    have : (1 - gᴴ) * H * (1 + g) + (1 + gᴴ) * H * (1 - g) = 2 * (H - gᴴ * H * g) := by
      noncomm_ring
    rw [this, hg, sub_self, mul_zero]
  set M := Aᴴ⁻¹ * (1 - g)ᴴ * H + H * ((1 - g) * A⁻¹)
  calc M = Aᴴ⁻¹ * Aᴴ * M * (A * A⁻¹) := by
        rw [Matrix.nonsing_inv_mul _ hBu, Matrix.mul_nonsing_inv _ hAu, Matrix.one_mul,
          Matrix.mul_one]
    _ = Aᴴ⁻¹ * (Aᴴ * M * A) * A⁻¹ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [key, Matrix.mul_zero, Matrix.zero_mul]

private lemma hk_one_add_cayley {K : Type*} [Field K] {X : Matrix n n K}
    (hdet : (1 + X).det ≠ 0) :
    1 + hk_cayley X = (2 : K) • (1 + X)⁻¹ := by
  have hAu : IsUnit (1 + X).det := isUnit_iff_ne_zero.mpr hdet
  unfold hk_cayley
  calc 1 + (1 - X) * (1 + X)⁻¹ = ((1 + X) + (1 - X)) * (1 + X)⁻¹ := by
        rw [Matrix.add_mul (1 + X), Matrix.mul_nonsing_inv _ hAu]
    _ = (2 : K) • (1 + X)⁻¹ := by
        rw [show (1 + X) + (1 - X) = (2 : K) • (1 : Matrix n n K) by
          rw [two_smul]; abel, Matrix.smul_mul, Matrix.one_mul]

theorem hk_cayley_det_aux {K : Type*} [Field K] [CharZero K] {X : Matrix n n K}
    (hdet : (1 + X).det ≠ 0) :
    (1 + hk_cayley X).det ≠ 0 := by
  rw [hk_one_add_cayley hdet, Matrix.det_smul, Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv']
  exact mul_ne_zero (pow_ne_zero _ two_ne_zero) (inv_ne_zero hdet)

theorem hk_cayley_cayley_aux {K : Type*} [Field K] [CharZero K] {X : Matrix n n K}
    (hdet : (1 + X).det ≠ 0) :
    hk_cayley (hk_cayley X) = X := by
  have hAu : IsUnit (1 + X).det := isUnit_iff_ne_zero.mpr hdet
  have hinv : (1 + hk_cayley X)⁻¹ = (2⁻¹ : K) • (1 + X) := by
    apply Matrix.inv_eq_right_inv
    rw [hk_one_add_cayley hdet, Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hAu,
      smul_smul, mul_inv_cancel₀ (two_ne_zero), one_smul]
  have hsub : 1 - hk_cayley X = (2 : K) • (X * (1 + X)⁻¹) := by
    unfold hk_cayley
    calc 1 - (1 - X) * (1 + X)⁻¹ = ((1 + X) - (1 - X)) * (1 + X)⁻¹ := by
          rw [Matrix.sub_mul (1 + X), Matrix.mul_nonsing_inv _ hAu]
      _ = (2 : K) • (X * (1 + X)⁻¹) := by
          rw [show (1 + X) - (1 - X) = (2 : K) • X by rw [two_smul]; abel, Matrix.smul_mul]
  rw [show hk_cayley (hk_cayley X) = (1 - hk_cayley X) * (1 + hk_cayley X)⁻¹ from rfl]
  rw [hsub, hinv, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ (two_ne_zero),
    one_smul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu, Matrix.mul_one]

private lemma hk_inv_commute {K : Type*} [Field K] {A Ω : Matrix n n K}
    (h : A * Ω = Ω * A) : A⁻¹ * Ω = Ω * A⁻¹ := by
  by_cases hA : IsUnit A.det
  · calc A⁻¹ * Ω = A⁻¹ * (Ω * A) * A⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_one]
      _ = A⁻¹ * (A * Ω) * A⁻¹ := by rw [h]
      _ = Ω * A⁻¹ := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hA, Matrix.zero_mul, Matrix.mul_zero]

theorem hk_cayley_commute_aux {K : Type*} [Field K] {X Ω : Matrix n n K}
    (h : X * Ω = Ω * X) :
    hk_cayley X * Ω = Ω * hk_cayley X := by
  have h1 : (1 + X) * Ω = Ω * (1 + X) := by
    rw [Matrix.add_mul, Matrix.mul_add, h, Matrix.one_mul, Matrix.mul_one]
  have h2 : (1 - X) * Ω = Ω * (1 - X) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, h, Matrix.one_mul, Matrix.mul_one]
  unfold hk_cayley
  rw [Matrix.mul_assoc, hk_inv_commute h1, ← Matrix.mul_assoc, h2, Matrix.mul_assoc]

theorem hk_cayley_map_aux {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (X : Matrix n n K) :
    (hk_cayley X).map f = hk_cayley (X.map f) := by
  have hm : ∀ M : Matrix n n K, M.map f = f.mapMatrix M := fun _ => rfl
  have hinv : ((1 + X)⁻¹).map f = (1 + X.map f)⁻¹ := by
    have e : 1 + X.map f = f.mapMatrix (1 + X) := by rw [map_add, map_one]; rfl
    rw [e]
    by_cases hA : IsUnit (1 + X).det
    · symm
      apply Matrix.inv_eq_left_inv
      rw [hm, ← map_mul, Matrix.nonsing_inv_mul _ hA, map_one]
    · have h0 : (1 + X).det = 0 := by rwa [isUnit_iff_ne_zero, not_not] at hA
      have hA' : ¬ IsUnit (f.mapMatrix (1 + X)).det := by
        rw [← RingHom.map_det, h0, map_zero]; exact not_isUnit_zero
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hA, Matrix.nonsing_inv_apply_not_isUnit _ hA']
      simp
  unfold hk_cayley
  rw [hm, map_mul, map_sub, map_one, ← hm ((1 + X)⁻¹), hinv]
  rfl

lemma hk_ratCast_eq (q : Matrix hk_ι hk_ι ℚ) : hk_ratCast q = (Rat.castHom ℝ).mapMatrix q := rfl

lemma hk_ratCast_intCast (M : Matrix hk_ι hk_ι ℤ) :
    hk_ratCast (M.map (Int.cast : ℤ → ℚ)) = M.map (Int.cast : ℤ → ℝ) := by
  ext i j; simp [hk_ratCast]

lemma hk_ratCast_mem_group {q : Matrix hk_ι hk_ι ℚ} (hq : q ∈ hk_group ℚ) :
    hk_ratCast q ∈ hk_group ℝ := by
  obtain ⟨h1, h2⟩ := hq
  have h1 : qᴴ * hk_E.map (Int.cast : ℤ → ℚ) * q = hk_E.map (Int.cast : ℤ → ℚ) := h1
  refine ⟨?_, ?_⟩
  · show (hk_ratCast q)ᴴ * _ * _ = _
    rw [← hk_ratCast_intCast, Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
    rw [show (hk_ratCast q)ᵀ = hk_ratCast qᵀ from (Matrix.transpose_map ..).symm]
    simp only [hk_ratCast_eq, ← map_mul, h1]
  · rw [← hk_ratCast_intCast, hk_ratCast_eq, hk_ratCast_eq, ← map_mul, ← map_mul, h2]

lemma hk_exists_genInv {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : Matrix κ ι ℚ) : ∃ B : Matrix ι κ ℚ, M * B * M = M := by
  set A := Matrix.toLin' M
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective A.rangeRestrict
    (LinearMap.range_rangeRestrict A)
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range A).subtype
    (Submodule.ker_subtype _)
  refine ⟨LinearMap.toMatrix' (g ∘ₗ π), ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply]
  have h1 : π (A v) = A.rangeRestrict v := by
    have := LinearMap.congr_fun hπ (A.rangeRestrict v)
    simpa using this
  rw [show Matrix.toLin' M = A from rfl, h1]
  have h2 := LinearMap.congr_fun hg (A.rangeRestrict v)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2
  have := congrArg Subtype.val h2
  simpa using this

lemma hk_dense_ker {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : Matrix κ ι ℚ) {x : ι → ℝ} (hx : M.map (Rat.cast : ℚ → ℝ) *ᵥ x = 0) :
    x ∈ closure ((fun q : ι → ℚ => fun i => (q i : ℝ)) '' {q | M *ᵥ q = 0}) := by
  obtain ⟨B, hB⟩ := hk_exists_genInv M
  set f := Rat.castHom ℝ
  let P : Matrix ι ι ℝ := (B * M).map f
  let Φ : (ι → ℝ) → (ι → ℝ) := fun y => y - P *ᵥ y
  have hΦc : Continuous Φ := continuous_id.sub (continuous_const.matrix_mulVec continuous_id)
  have hΦx : Φ x = x := by
    simp only [Φ, P, Matrix.map_mul, ← Matrix.mulVec_mulVec]
    rw [show M.map f = M.map (Rat.cast : ℚ → ℝ) from rfl, hx, Matrix.mulVec_zero, sub_zero]
  have hdense : DenseRange (fun q : ι → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hmem : x ∈ closure (Φ '' Set.range (fun q : ι → ℚ => fun i => (q i : ℝ))) := by
    rw [← hΦx]
    exact mem_closure_image hΦc.continuousAt (hdense x)
  refine closure_mono ?_ hmem
  rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
  refine ⟨q - (B * M) *ᵥ q, ?_, ?_⟩
  · show M *ᵥ (q - (B * M) *ᵥ q) = 0
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hB, sub_self]
  · ext i
    simp only [Φ, P, Pi.sub_apply, Rat.cast_sub]
    congr 1
    have := RingHom.map_mulVec f (B * M) q i
    simpa [f, Function.comp_def] using this


/-- The linear equations of `hk_lieAlg` on the entries of a matrix: the `inl` rows are the
entries of `Xᵀ E + E X`, the `inr` rows those of `X ω - ω X`.
Source: the definitions `hk_lie`, `hk_lieAlg`; Bourbaki, *Algèbre*, Ch. II, §8. -/
def hk_lieEqs (R : Type*) [CommRing R] :
    Matrix ((hk_ι × hk_ι) ⊕ (hk_ι × hk_ι)) (hk_ι × hk_ι) R :=
  Matrix.of fun r p => Sum.elim
    (fun ab : hk_ι × hk_ι =>
      (if p.2 = ab.1 then hk_E.map (Int.cast : ℤ → R) p.1 ab.2 else 0) +
      (if p.2 = ab.2 then hk_E.map (Int.cast : ℤ → R) ab.1 p.1 else 0))
    (fun ab : hk_ι × hk_ι =>
      (if p.1 = ab.1 then hk_Omega.map (Int.cast : ℤ → R) p.2 ab.2 else 0) -
      (if p.2 = ab.2 then hk_Omega.map (Int.cast : ℤ → R) ab.1 p.1 else 0)) r

example : hk_lieEqs ℚ (Sum.inr ((0, 0), (0, 0))) ((0, 0), (0, 0)) = 0 := by
  simp [hk_lieEqs]

lemma hk_sum_snd {α β M : Type*} [Fintype α] [Fintype β] [DecidableEq β] [AddCommMonoid M]
    (c : β) (G : α × β → M) :
    (∑ p : α × β, if p.2 = c then G p else 0) = ∑ a, G (a, c) := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma hk_sum_fst {α β M : Type*} [Fintype α] [Fintype β] [DecidableEq α] [AddCommMonoid M]
    (c : α) (G : α × β → M) :
    (∑ p : α × β, if p.1 = c then G p else 0) = ∑ b, G (c, b) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

lemma hk_lieEqs_mulVec_inl {R : Type*} [CommRing R] (X : Matrix hk_ι hk_ι R)
    (ab : hk_ι × hk_ι) :
    (hk_lieEqs R *ᵥ fun p => X p.1 p.2) (Sum.inl ab) =
      (Xᵀ * hk_E.map (Int.cast : ℤ → R) + hk_E.map (Int.cast : ℤ → R) * X) ab.1 ab.2 := by
  simp only [Matrix.mulVec, dotProduct, hk_lieEqs, Matrix.of_apply, Sum.elim_inl, add_mul,
    ite_mul, zero_mul, Finset.sum_add_distrib, hk_sum_snd]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, mul_comm]

lemma hk_lieEqs_mulVec_inr {R : Type*} [CommRing R] (X : Matrix hk_ι hk_ι R)
    (ab : hk_ι × hk_ι) :
    (hk_lieEqs R *ᵥ fun p => X p.1 p.2) (Sum.inr ab) =
      (X * hk_Omega.map (Int.cast : ℤ → R) - hk_Omega.map (Int.cast : ℤ → R) * X) ab.1 ab.2 := by
  simp only [Matrix.mulVec, dotProduct, hk_lieEqs, Matrix.of_apply, Sum.elim_inr, sub_mul,
    ite_mul, zero_mul, Finset.sum_sub_distrib, hk_sum_snd, hk_sum_fst]
  simp only [Matrix.sub_apply, Matrix.mul_apply, mul_comm]

lemma hk_mem_lieAlg_iff {R : Type*} [CommRing R] [StarRing R] [TrivialStar R]
    (X : Matrix hk_ι hk_ι R) :
    X ∈ hk_lieAlg R ↔ (hk_lieEqs R *ᵥ fun p => X p.1 p.2) = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    have h1 : Xᴴ * _ + _ * X = 0 := h1
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
    funext r
    rcases r with ab | ab
    · rw [hk_lieEqs_mulVec_inl, h1]; rfl
    · rw [hk_lieEqs_mulVec_inr, h2, sub_self]; rfl
  · intro h
    refine ⟨?_, ?_⟩
    · show Xᴴ * _ + _ * X = 0
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      ext a b
      have := congrFun h (Sum.inl (a, b))
      rwa [hk_lieEqs_mulVec_inl] at this
    · rw [← sub_eq_zero]
      ext a b
      have := congrFun h (Sum.inr (a, b))
      rwa [hk_lieEqs_mulVec_inr] at this

lemma hk_lieEqs_map : (hk_lieEqs ℚ).map (Rat.cast : ℚ → ℝ) = hk_lieEqs ℝ := by
  ext r p
  rcases r with ab | ab <;> simp [hk_lieEqs, apply_ite (Rat.cast : ℚ → ℝ)]

theorem hk_lieAlg_dense_aux {X : Matrix hk_ι hk_ι ℝ} (hX : X ∈ hk_lieAlg ℝ) :
    X ∈ closure (hk_ratCast '' hk_lieAlg ℚ) := by
  rw [hk_mem_lieAlg_iff, ← hk_lieEqs_map] at hX
  have h := hk_dense_ker (hk_lieEqs ℚ) hX
  let U : (hk_ι × hk_ι → ℝ) → Matrix hk_ι hk_ι ℝ := fun w => Matrix.of fun i j => w (i, j)
  have hU : Continuous U :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)
  have hX' : X = U (fun p => X p.1 p.2) := rfl
  rw [hX']
  refine closure_mono ?_ (mem_closure_image hU.continuousAt h)
  rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
  refine ⟨Matrix.of fun i j => q (i, j), ?_, rfl⟩
  rw [hk_mem_lieAlg_iff]
  exact hq

lemma hk_cayley_continuousAt {X : Matrix hk_ι hk_ι ℝ} (h : (1 + X).det ≠ 0) :
    ContinuousAt hk_cayley X := by
  have e : (hk_cayley : Matrix hk_ι hk_ι ℝ → Matrix hk_ι hk_ι ℝ) =
      fun Y => (1 - Y) * ((1 + Y).det⁻¹ • (1 + Y).adjugate) := by
    funext Y
    simp only [hk_cayley, Matrix.inv_def, Ring.inverse_eq_inv']
  rw [e]
  have hc : Continuous fun Y : Matrix hk_ι hk_ι ℝ => 1 + Y := continuous_const.add continuous_id
  have h1 : ContinuousAt (fun Y : Matrix hk_ι hk_ι ℝ => (1 + Y).det⁻¹) X :=
    hc.matrix_det.continuousAt.inv₀ h
  have h2 : ContinuousAt (fun Y : Matrix hk_ι hk_ι ℝ => (1 + Y).adjugate) X :=
    hc.matrix_adjugate.continuousAt
  exact (continuousAt_const.sub continuousAt_id).mul (h1.smul h2)

lemma hk_det_one_add_ratCast {Z : Matrix hk_ι hk_ι ℚ} (h : (1 + hk_ratCast Z).det ≠ 0) :
    (1 + Z).det ≠ 0 := by
  intro h0
  apply h
  have : 1 + hk_ratCast Z = (Rat.castHom ℝ).mapMatrix (1 + Z) := by
    rw [map_add, map_one]; rfl
  rw [this, ← RingHom.map_det, h0, map_zero]

theorem hk_chart_dense_aux {g : Matrix hk_ι hk_ι ℝ} (hg : g ∈ hk_group ℝ)
    (hdet : (1 + g).det ≠ 0) :
    g ∈ closure (hk_ratCast '' hk_group ℚ) := by
  obtain ⟨hgu, hgc⟩ := hg
  have hXlie : hk_cayley g ∈ hk_lieAlg ℝ :=
    ⟨hk_cayley_mem_lie_aux hgu hdet, hk_cayley_commute_aux hgc⟩
  have hXdet := hk_cayley_det_aux hdet
  have hXg : hk_cayley (hk_cayley g) = g := hk_cayley_cayley_aux hdet
  have hO : IsOpen {Y : Matrix hk_ι hk_ι ℝ | (1 + Y).det ≠ 0} :=
    isOpen_ne_fun (continuous_const.add continuous_id).matrix_det continuous_const
  have hX : hk_cayley g ∈ closure ({Y : Matrix hk_ι hk_ι ℝ | (1 + Y).det ≠ 0} ∩
      hk_ratCast '' hk_lieAlg ℚ) :=
    hO.inter_closure ⟨hXdet, hk_lieAlg_dense_aux hXlie⟩
  have h := ContinuousWithinAt.mem_closure_image
    (hk_cayley_continuousAt hXdet).continuousWithinAt hX
  rw [hXg] at h
  refine closure_mono ?_ h
  rintro _ ⟨_, ⟨hYdet, Z, hZ, rfl⟩, rfl⟩
  have hZdet := hk_det_one_add_ratCast hYdet
  exact ⟨hk_cayley Z, ⟨hk_cayley_mem_unitary_aux hZ.1 hZdet, hk_cayley_commute_aux hZ.2⟩,
    hk_cayley_map_aux (Rat.castHom ℝ) Z⟩

lemma hk_Omega_apply (p q : hk_ι) : hk_Omega p q =
    if p.1 = q.1 then (if p.2 = 0 then (if q.2 = 1 then -3 else 0)
      else (if q.2 = 0 then 1 else 0)) else 0 := by
  obtain ⟨i, a⟩ := p
  obtain ⟨j, b⟩ := q
  simp only [hk_Omega, LinearMap.toMatrix'_apply, b60_omega, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.single_apply, Prod.mk.injEq]
  fin_cases a <;> fin_cases b <;> by_cases h : i = j <;> simp [h, eq_comm]

lemma hk_E_apply (p q : hk_ι) : hk_E p q =
    if p.1 = q.1 then (if p.2 = 0 then (if q.2 = 1 then b60_diag p.1 else 0)
      else (if q.2 = 0 then -b60_diag p.1 else 0)) else 0 := by
  obtain ⟨i, a⟩ := p
  obtain ⟨j, b⟩ := q
  simp only [hk_E, LinearMap.toMatrix₂'_apply, b60_E, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.single_apply, Prod.mk.injEq]
  fin_cases a <;> fin_cases b <;> by_cases h : i = j <;> simp [h, eq_comm]


lemma hk_Omega_sq : hk_Omega * hk_Omega = (-3 : ℤ) • (1 : Matrix hk_ι hk_ι ℤ) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [Matrix.mul_apply, hk_Omega_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq]
  fin_cases a <;> fin_cases b <;> by_cases h : i = j <;> simp [h, Finset.sum_ite_eq']

lemma hk_Omega_E : hk_Omegaᵀ * hk_E = -(hk_E * hk_Omega) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hk_Omega_apply, hk_E_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.neg_apply]
  fin_cases a <;> fin_cases b <;> by_cases h : i = j <;> simp [h, eq_comm, mul_comm]

lemma hk_diag_ne_zero (i : Fin 6) : b60_diag i ≠ 0 := by
  fin_cases i <;> decide

lemma hk_E_det_ne_zero : (hk_E.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
  let Einv : Matrix hk_ι hk_ι ℝ := Matrix.of fun p q =>
    if p.1 = q.1 then (if p.2 = 0 then (if q.2 = 1 then -((b60_diag p.1 : ℝ))⁻¹ else 0)
      else (if q.2 = 0 then ((b60_diag p.1 : ℝ))⁻¹ else 0)) else 0
  have h : hk_E.map (Int.cast : ℤ → ℝ) * Einv = 1 := by
    ext ⟨i, a⟩ ⟨j, b⟩
    have hd : (b60_diag i : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (hk_diag_ne_zero i)
    simp only [Matrix.mul_apply, Matrix.map_apply, hk_E_apply, Einv, Matrix.of_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.one_apply, Prod.mk.injEq]
    fin_cases a <;> fin_cases b <;>
    · by_cases h : i = j
      · subst h; simp [hd]
      · simp [h]
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

open Polynomial in
lemma hk_exists_det_ne {m : Type*} [Fintype m] [DecidableEq m] (A B : Matrix m m ℝ)
    (h : (A.map (algebraMap ℝ ℂ) + Complex.I • B.map (algebraMap ℝ ℂ)).det ≠ 0) :
    ∃ t : ℝ, (A + t • B).det ≠ 0 := by
  let M : Matrix m m ℝ[X] := A.map C + (X : ℝ[X]) • B.map C
  have hev : ∀ t : ℝ, M.det.eval t = (A + t • B).det := by
    intro t
    rw [← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [M]
    ring
  have hp : M.det ≠ 0 := by
    intro h0
    apply h
    have := congrArg (eval₂RingHom (algebraMap ℝ ℂ) Complex.I) h0
    rw [map_zero, RingHom.map_det] at this
    rw [← this]
    congr 1
    ext i j
    simp [M]
    ring
  obtain ⟨t, -, ht⟩ := Set.infinite_univ.exists_notMem_finset M.det.roots.toFinset
  refine ⟨t, ?_⟩
  rw [← hev]
  intro h0
  apply ht
  rw [Multiset.mem_toFinset, mem_roots hp]
  exact h0

lemma hk_det_K_ne {m : Type*} [Fintype m] [DecidableEq m] (K g G : Matrix m m ℂ)
    (hK : K * K = 1) (hc : g * K = K * g) (hG : g * G = 1) :
    ((1 - K) + (1 + K) * g).det ≠ 0 := by
  have h1 : (1 + K) * (1 - K) = 0 := by
    rw [show (1 + K) * (1 - K) = 1 - K * K by noncomm_ring, hK, sub_self]
  have hm : g * (1 - K) = (1 - K) * g := by
    rw [mul_sub, sub_mul, hc, mul_one, one_mul]
  have hp : g * (1 + K) = (1 + K) * g := by
    rw [mul_add, add_mul, hc, mul_one, one_mul]
  have hXY : ((1 - K) + (1 + K) * g) * ((1 - K) + (1 + K) * G) = (4 : ℂ) • 1 := by
    have e : ((1 - K) + (1 + K) * g) * ((1 - K) + (1 + K) * G) =
        (1 - K) * (1 - K) + (1 - K) * (1 + K) * G + (1 + K) * (g * (1 - K)) +
          (1 + K) * (g * (1 + K) * G) := by
      noncomm_ring
    have t1 : (1 - K) * (1 + K) * G = 0 := by
      rw [show (1 - K) * (1 + K) = 1 - K * K by noncomm_ring, hK, sub_self, zero_mul]
    have t2 : (1 + K) * ((1 - K) * g) = 0 := by rw [← mul_assoc, h1, zero_mul]
    have t3 : (1 + K) * ((1 + K) * g * G) = (1 + K) * (1 + K) := by
      rw [mul_assoc (1 + K) g G, hG, mul_one]
    rw [e, hm, hp, t1, t2, t3, add_zero, add_zero,
      show (1 - K) * (1 - K) + (1 + K) * (1 + K) = 1 + 1 + (K * K + K * K) by
        simp only [mul_sub, sub_mul, mul_add, add_mul, one_mul, mul_one]; abel, hK]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
    by_cases hij : i = j
    · simp [hij]; norm_num
    · simp [hij]
  intro h0
  have := congrArg Matrix.det hXY
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact (pow_ne_zero _ (by norm_num : (4 : ℂ) ≠ 0)) this.symm

lemma hk_group_mul {R : Type*} [CommRing R] [StarRing R] [TrivialStar R]
    {g h : Matrix hk_ι hk_ι R} (hg : g ∈ hk_group R) (hh : h ∈ hk_group R) :
    g * h ∈ hk_group R := by
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨hh1, hh2⟩ := hh
  have hg1 : gᴴ * _ * g = _ := hg1
  have hh1 : hᴴ * _ * h = _ := hh1
  refine ⟨?_, ?_⟩
  · show (g * h)ᴴ * _ * (g * h) = _
    calc (g * h)ᴴ * _ * (g * h) = hᴴ * (gᴴ * hk_E.map (Int.cast : ℤ → R) * g) * h := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hg1, hh1]
  · rw [Matrix.mul_assoc, hh2, ← Matrix.mul_assoc, hg2, Matrix.mul_assoc]

/-- The real matrix of `ω / √3` on `ℝ ⊗ b60_Lattice`: a complex structure (`J² = -1`) commuting
with `ω`, so that `a + b J` with `a² + b² = 1` is a real point of `U(b60_H)`.
Source: plan `G32RemainingPremises.md`, §2.3, stage S2 (the unit scalars of `K ⊗ ℝ`);
`b60_omega_square`. -/
def hk_J : Matrix hk_ι hk_ι ℝ := (Real.sqrt 3)⁻¹ • hk_Omega.map (Int.cast : ℤ → ℝ)

example : hk_J = (Real.sqrt 3)⁻¹ • hk_Omega.map (Int.cast : ℤ → ℝ) := rfl

lemma hk_OmegaR_sq : hk_Omega.map (Int.cast : ℤ → ℝ) * hk_Omega.map (Int.cast : ℤ → ℝ) =
    (-3 : ℝ) • 1 := by
  rw [show hk_Omega.map (Int.cast : ℤ → ℝ) = (Int.castRingHom ℝ).mapMatrix hk_Omega from rfl,
    ← map_mul, hk_Omega_sq, map_zsmul, map_one, ← Int.cast_smul_eq_zsmul ℝ]
  norm_num

lemma hk_OmegaR_E : (hk_Omega.map (Int.cast : ℤ → ℝ))ᵀ * hk_E.map (Int.cast : ℤ → ℝ) =
    -(hk_E.map (Int.cast : ℤ → ℝ) * hk_Omega.map (Int.cast : ℤ → ℝ)) := by
  have := congrArg (Int.castRingHom ℝ).mapMatrix hk_Omega_E
  rw [map_mul, map_neg, map_mul] at this
  rw [← Matrix.transpose_map]
  exact this

lemma hk_J_sq : hk_J * hk_J = -1 := by
  have h3 : (Real.sqrt 3)⁻¹ * (Real.sqrt 3)⁻¹ = (3 : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  rw [hk_J, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hk_OmegaR_sq, smul_smul, h3]
  norm_num

lemma hk_J_E : hk_Jᵀ * hk_E.map (Int.cast : ℤ → ℝ) = -(hk_E.map (Int.cast : ℤ → ℝ) * hk_J) := by
  rw [hk_J, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hk_OmegaR_E, smul_neg]

lemma hk_J_comm {g : Matrix hk_ι hk_ι ℝ} (hg : g ∈ hk_group ℝ) : g * hk_J = hk_J * g := by
  rw [hk_J, Matrix.mul_smul, Matrix.smul_mul, hg.2]

lemma hk_J_mul (x y u v : ℝ) :
    (x • 1 + y • hk_J) * (u • 1 + v • hk_J) = (x * u - y * v) • 1 + (x * v + y * u) • hk_J := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, hk_J_sq]
  module

lemma hk_J_det_ne {x y : ℝ} (h : x ^ 2 + y ^ 2 ≠ 0) : (x • 1 + y • hk_J).det ≠ 0 := by
  have e := hk_J_mul x y x (-y)
  rw [show x * x - y * -y = x ^ 2 + y ^ 2 by ring, show x * -y + y * x = 0 by ring, zero_smul,
    add_zero] at e
  intro h0
  have := congrArg Matrix.det e
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ h this.symm

lemma hk_J_mem {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) : a • 1 + b • hk_J ∈ hk_group ℝ := by
  refine ⟨?_, ?_⟩
  · show (a • 1 + b • hk_J)ᴴ * _ * _ = _
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hk_J_E, Matrix.neg_mul, Matrix.mul_assoc, hk_J_sq, Matrix.mul_neg, neg_neg,
      smul_neg]
    calc _ = (a ^ 2 + b ^ 2) • hk_E.map (Int.cast : ℤ → ℝ) := by module
      _ = _ := by rw [hab, one_smul]
  · simp only [hk_J, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]

theorem hk_rational_dense_aux {g : Matrix hk_ι hk_ι ℝ} (hg : g ∈ hk_group ℝ) :
    g ∈ closure (hk_ratCast '' hk_group ℚ) := by
  -- `g` is invertible
  have hgdet : IsUnit g.det := by
    have h1 : gᴴ * _ * g = _ := hg.1
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at this
    refine isUnit_iff_ne_zero.mpr fun h0 => hk_E_det_ne_zero ?_
    rw [← this, h0, zero_mul, zero_mul]
  -- a real `t` with `det((1 + g) + t J (g - 1)) ≠ 0`
  let f := (algebraMap ℝ ℂ).mapMatrix (m := hk_ι)
  have hC : ((1 + g).map (algebraMap ℝ ℂ) +
      Complex.I • (hk_J * (g - 1)).map (algebraMap ℝ ℂ)).det ≠ 0 := by
    have hK : (Complex.I • f hk_J) * (Complex.I • f hk_J) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← map_mul, hk_J_sq, map_neg, map_one,
        Complex.I_mul_I, neg_one_smul, neg_neg]
    have hc : f g * (Complex.I • f hk_J) = (Complex.I • f hk_J) * f g := by
      rw [Matrix.mul_smul, Matrix.smul_mul, ← map_mul, ← map_mul, hk_J_comm hg]
    have hG : f g * f g⁻¹ = 1 := by
      rw [← map_mul, Matrix.mul_nonsing_inv _ hgdet, map_one]
    have := hk_det_K_ne _ _ _ hK hc hG
    convert this using 2
    show f (1 + g) + Complex.I • f (hk_J * (g - 1)) = _
    rw [map_add, map_one, map_mul, map_sub, map_one, Matrix.mul_sub, Matrix.mul_one,
      smul_sub, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
    abel
  obtain ⟨t, ht⟩ := hk_exists_det_ne _ _ hC
  have ht2 : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  set a : ℝ := (1 - t ^ 2) / (1 + t ^ 2)
  set b : ℝ := 2 * t / (1 + t ^ 2)
  have hab : a ^ 2 + b ^ 2 = 1 := by
    simp only [a, b]; field_simp; ring
  have h1a : (1 + a) ^ 2 + (-b) ^ 2 ≠ 0 := by
    have : 1 + a = 2 / (1 + t ^ 2) := by simp only [a]; field_simp; ring
    rw [this]; positivity
  have hL1 := hk_J_mem (a := a) (b := -b) (by rw [neg_sq]; exact hab)
  have hL2 := hk_group_mul (hk_J_mem hab) hg
  have hprod : (a • 1 + (-b) • hk_J) * ((a • 1 + b • hk_J) * g) = g := by
    rw [← Matrix.mul_assoc, hk_J_mul, show a * a - -b * b = a ^ 2 + b ^ 2 by ring, hab,
      show a * b + -b * a = 0 by ring, zero_smul, add_zero, one_smul, Matrix.one_mul]
  have hdet1 : (1 + (a • 1 + (-b) • hk_J)).det ≠ 0 := by
    rw [show (1 : Matrix hk_ι hk_ι ℝ) + (a • 1 + (-b) • hk_J) = (1 + a) • 1 + (-b) • hk_J by
      module]
    exact hk_J_det_ne h1a
  have hdet2 : (1 + (a • 1 + b • hk_J) * g).det ≠ 0 := by
    have hkey : ((1 : ℝ) • 1 + (-t) • hk_J) * (a • 1 + b • hk_J) = (1 : ℝ) • 1 + t • hk_J := by
      rw [hk_J_mul]
      congr 2
      · simp only [a, b]; field_simp; ring
      · simp only [a, b]; field_simp; ring
    have key : ((1 : ℝ) • 1 + (-t) • hk_J) * (1 + (a • 1 + b • hk_J) * g) =
        1 + g + t • (hk_J * (g - 1)) := by
      rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hkey]
      simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, one_smul, Matrix.mul_sub,
        Matrix.mul_one, smul_sub]
      module
    intro h0
    apply ht
    rw [← key, Matrix.det_mul, h0, mul_zero]
  rw [← hprod]
  refine map_mem_closure₂ continuous_mul (hk_chart_dense_aux hL1 hdet1)
    (hk_chart_dense_aux hL2 hdet2) ?_
  rintro _ ⟨q₁, hq₁, rfl⟩ _ ⟨q₂, hq₂, rfl⟩
  exact ⟨q₁ * q₂, hk_group_mul hq₁ hq₂, by simp only [hk_ratCast_eq, map_mul]⟩

lemma hk_toC_mul (g h : Matrix hk_ι hk_ι ℝ) : hk_toC (g * h) = hk_toC g ∘ₗ hk_toC h := by
  simp only [hk_toC]
  rw [show (g * h).map (Complex.ofReal : ℝ → ℂ) =
      g.map (Complex.ofReal : ℝ → ℂ) * h.map (Complex.ofReal : ℝ → ℂ) from
    Matrix.map_mul (f := Complex.ofRealHom), Matrix.toLin_mul b60_basis b60_basis b60_basis]

lemma hk_toC_one' : hk_toC 1 = LinearMap.id := by
  simp [hk_toC, Matrix.toLin_one]

lemma hk_toC_basis (g : Matrix hk_ι hk_ι ℝ) (q : hk_ι) :
    hk_toC g (b60_basis q) = ∑ p, ((g p q : ℝ) : ℂ) • b60_basis p := by
  simp [hk_toC, Matrix.toLin_self]

lemma hk_toC_Omega : hk_toC (hk_Omega.map (Int.cast : ℤ → ℝ)) = b60_omegaC := by
  apply (LinearMap.toMatrix b60_basis b60_basis).injective
  rw [hk_toC, LinearMap.toMatrix_toLin]
  ext p q
  rw [LinearMap.toMatrix_apply, b60_basis, Module.Basis.baseChange_apply, b60_omegaC,
    LinearMap.baseChange_tmul, Module.Basis.baseChange_repr_tmul]
  simp [hk_Omega, LinearMap.toMatrix'_apply]

lemma hk_group_isUnit_det {g : Matrix hk_ι hk_ι ℝ} (hg : g ∈ hk_group ℝ) : IsUnit g.det := by
  have h1 : gᴴ * _ * g = _ := hg.1
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
  have := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at this
  refine isUnit_iff_ne_zero.mpr fun h0 => hk_E_det_ne_zero ?_
  rw [← this, h0, zero_mul, zero_mul]

/-- `hk_toC g` as a linear equivalence for `g` in the real group, with inverse `hk_toC g⁻¹`.
Source: Mathlib `Matrix.toLin_mul`, `Matrix.mul_nonsing_inv`; `hk_group` (`gᵀ E g = E` and
`det E ≠ 0` make `g` invertible). -/
def hk_toCEquiv {g : Matrix hk_ι hk_ι ℝ} (hg : g ∈ hk_group ℝ) :
    (ℂ ⊗[ℤ] b60_Lattice) ≃ₗ[ℂ] (ℂ ⊗[ℤ] b60_Lattice) :=
  LinearEquiv.ofLinearMap (hk_toC g) (hk_toC g⁻¹)
    (by rw [← hk_toC_mul, Matrix.mul_nonsing_inv _ (hk_group_isUnit_det hg), hk_toC_one'])
    (by rw [← hk_toC_mul, Matrix.nonsing_inv_mul _ (hk_group_isUnit_det hg), hk_toC_one'])

example : hk_toCEquiv (g := 1) (by simp [hk_group, hk_unitary]) (b60_basis (0, 0)) =
    b60_basis (0, 0) := by
  simp [hk_toCEquiv, hk_toC_one']

lemma hk_toCEquiv_apply {g : Matrix hk_ι hk_ι ℝ} (hg : g ∈ hk_group ℝ) (x) :
    hk_toCEquiv hg x = hk_toC g x := rfl

lemma hk_toC_omega {g : Matrix hk_ι hk_ι ℝ} (hg : g ∈ hk_group ℝ) (x) :
    hk_toC g (b60_omegaC x) = b60_omegaC (hk_toC g x) := by
  rw [← hk_toC_Omega, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← hk_toC_mul,
    ← hk_toC_mul, hg.2]

lemma hk_E_basis (p q : hk_ι) :
    b60_E.baseChange ℂ (b60_basis p) (b60_basis q) = ((hk_E p q : ℤ) : ℂ) := by
  rw [b60_basis, Module.Basis.baseChange_apply, Module.Basis.baseChange_apply,
    LinearMap.BilinForm.baseChange_tmul]
  simp [hk_E, LinearMap.toMatrix₂'_apply]

lemma hk_toC_E {g : Matrix hk_ι hk_ι ℝ} (hg : g ∈ hk_group ℝ) (x y) :
    b60_E.baseChange ℂ (hk_toC g x) (hk_toC g y) = b60_E.baseChange ℂ x y := by
  have h1 : gᴴ * _ * g = _ := hg.1
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
  have key : (b60_E.baseChange ℂ).compl₁₂ (hk_toC g) (hk_toC g) = b60_E.baseChange ℂ := by
    refine LinearMap.ext_basis b60_basis b60_basis fun p q => ?_
    rw [LinearMap.compl₁₂_apply, hk_toC_basis, hk_toC_basis, hk_E_basis]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hk_E_basis,
      smul_eq_mul]
    have := congrArg (fun M : Matrix hk_ι hk_ι ℝ => ((M p q : ℝ) : ℂ)) h1
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul] at this
    simp only [Complex.ofReal_intCast] at this
    rw [← this]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  exact LinearMap.congr_fun₂ key x y

lemma hk_conj_smul_basis (c : ℂ) (p : hk_ι) :
    b2_conj b60_Lattice (c • b60_basis p) = (starRingEnd ℂ c) • b60_basis p := by
  rw [b60_basis, Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul,
    mul_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

lemma hk_toC_conj (g : Matrix hk_ι hk_ι ℝ) (x) :
    b2_conj b60_Lattice (hk_toC g x) = hk_toC g (b2_conj b60_Lattice x) := by
  conv_lhs => rw [← b60_basis.sum_repr x]
  conv_rhs => rw [← b60_basis.sum_repr x]
  simp only [map_sum, hk_conj_smul_basis, map_smul, hk_toC_basis, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, Complex.conj_ofReal]


lemma hk_sqrt3_ne : (Real.sqrt 3 : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'

lemma hk_F_eig_dims (z : Fin 9 → ℂ) :
    Module.finrank ℂ ↥(b60_F z ⊓ Module.End.eigenspace b60_omegaC
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3 ∧
    Module.finrank ℂ ↥(b60_F z ⊓ Module.End.eigenspace b60_omegaC
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3 := by
  set Vm := Module.End.eigenspace b60_omegaC (-Complex.I * (Real.sqrt 3 : ℂ))
  set Vp := Module.End.eigenspace b60_omegaC (Complex.I * (Real.sqrt 3 : ℂ))
  have hli := b60_frame_independent z
  have hsub (a : Fin 2) : LinearIndependent ℂ (fun i : Fin 3 => b60_frame z (a, i)) := by
    simpa only [Function.comp_def] using hli.comp (fun i : Fin 3 => (a, i))
      (by intro i j h; exact congrArg Prod.snd h)
  have hmem (a : Fin 2) (i : Fin 3) : b60_frame z (a, i) ∈ b60_F z :=
    Submodule.subset_span ⟨(a, i), rfl⟩
  have hNle : Submodule.span ℂ (Set.range fun i : Fin 3 => b60_frame z (0, i)) ≤ b60_F z ⊓ Vm := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨hmem 0 i, Module.End.mem_eigenspace_iff.mpr ?_⟩
    rw [b60_omegaC_frame]
    simp
  have hPle : Submodule.span ℂ (Set.range fun i : Fin 3 => b60_frame z (1, i)) ≤ b60_F z ⊓ Vp := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨hmem 1 i, Module.End.mem_eigenspace_iff.mpr ?_⟩
    rw [b60_omegaC_frame]
    simp
  have hN := Submodule.finrank_mono hNle
  have hP := Submodule.finrank_mono hPle
  rw [finrank_span_eq_card (hsub 0), Fintype.card_fin] at hN
  rw [finrank_span_eq_card (hsub 1), Fintype.card_fin] at hP
  have hdisj : (b60_F z ⊓ Vm) ⊓ (b60_F z ⊓ Vp) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨-, hx1⟩, ⟨-, hx2⟩⟩
    replace hx1 := Module.End.mem_eigenspace_iff.mp hx1
    replace hx2 := Module.End.mem_eigenspace_iff.mp hx2
    rw [Submodule.mem_bot]
    have h : (2 * Complex.I * (Real.sqrt 3 : ℂ)) • x = 0 := by
      rw [show (2 * Complex.I * (Real.sqrt 3 : ℂ)) • x =
        (Complex.I * (Real.sqrt 3 : ℂ)) • x - (-Complex.I * (Real.sqrt 3 : ℂ)) • x by module,
        ← hx1, ← hx2, sub_self]
    exact (smul_eq_zero.mp h).resolve_left
      (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hk_sqrt3_ne)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (b60_F z ⊓ Vm) (b60_F z ⊓ Vp)
  rw [hdisj, finrank_bot] at hsum
  have hle : Module.finrank ℂ ↥((b60_F z ⊓ Vm) ⊔ (b60_F z ⊓ Vp)) ≤ 6 := by
    have := Submodule.finrank_mono (sup_le (inf_le_left : b60_F z ⊓ Vm ≤ b60_F z)
      (inf_le_left : b60_F z ⊓ Vp ≤ b60_F z))
    rwa [b60_F, finrank_span_eq_card hli] at this
  omega

open scoped ComplexOrder in
lemma hk_exists_normalizer {m : Type*} [Fintype m] [DecidableEq m] {K : Matrix m m ℂ}
    (hK : K.PosDef) : ∃ P : Matrix m m ℂ, Pᴴ * K * P = 1 := by
  set U : Matrix m m ℂ := (hK.1.eigenvectorUnitary : Matrix m m ℂ)
  set d : m → ℝ := hK.1.eigenvalues
  have hd : ∀ i, 0 < d i := hK.eigenvalues_pos
  have hspec : K = U * Matrix.diagonal (fun i => (d i : ℂ)) * star U := by
    have := hK.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  refine ⟨U * Matrix.diagonal (fun i => ((Real.sqrt (d i))⁻¹ : ℂ)), ?_⟩
  rw [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, hspec]
  have hs : star (fun i => ((Real.sqrt (d i))⁻¹ : ℂ)) = fun i => ((Real.sqrt (d i))⁻¹ : ℂ) := by
    funext i; simp [Complex.conj_ofReal]
  rw [hs, ← Matrix.star_eq_conjTranspose]
  calc Matrix.diagonal (fun i => ((Real.sqrt (d i))⁻¹ : ℂ)) * star U *
        (U * Matrix.diagonal (fun i => (d i : ℂ)) * star U) *
        (U * Matrix.diagonal (fun i => ((Real.sqrt (d i))⁻¹ : ℂ)))
      = Matrix.diagonal (fun i => ((Real.sqrt (d i))⁻¹ : ℂ)) * (star U * U) *
        Matrix.diagonal (fun i => (d i : ℂ)) * (star U * U) *
        Matrix.diagonal (fun i => ((Real.sqrt (d i))⁻¹ : ℂ)) := by
          simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [hUU, Matrix.mul_one, Matrix.mul_one, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      have h1 : (Real.sqrt (d i) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr (hd i)).ne'
      have h2 : ((Real.sqrt (d i) : ℂ)) ^ 2 = d i := by
        exact_mod_cast Real.sq_sqrt (hd i).le
      field_simp
      rw [h2]

open scoped ComplexOrder in
lemma hk_one_sub_mul_conj_posDef {A : Matrix (Fin 3) (Fin 3) ℂ} (hA : (1 - Aᴴ * A).PosDef) :
    (1 - A * Aᴴ).PosDef := by
  have hinv := hA.inv
  have hM : (1 + A * (1 - Aᴴ * A)⁻¹ * Aᴴ).PosDef :=
    Matrix.PosDef.one.add_posSemidef (hinv.posSemidef.mul_mul_conjTranspose_same A)
  have hu : IsUnit (1 - Aᴴ * A).det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have heq : (1 - A * Aᴴ) * (1 + A * (1 - Aᴴ * A)⁻¹ * Aᴴ) = 1 := by
    have e : (1 - A * Aᴴ) * (1 + A * (1 - Aᴴ * A)⁻¹ * Aᴴ) =
        1 - A * Aᴴ + A * ((1 - Aᴴ * A) * (1 - Aᴴ * A)⁻¹) * Aᴴ := by
      noncomm_ring
    rw [e, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    abel
  have := hM.inv
  rwa [Matrix.inv_eq_left_inv heq] at this

/-- The signature matrix `diag(1, 1, 1, -1, -1, -1)` on `Fin 3 ⊕ Fin 3`.
Source: `hermSignature_diag_F1569` (signature `(3, 3)` of `b60_H`). -/
def hk_eps : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ := Matrix.fromBlocks 1 0 0 (-1)

example : hk_eps (Sum.inl 0) (Sum.inl 0) = 1 := by simp [hk_eps]

lemma hk_Gamma_unitary {A P S : Matrix (Fin 3) (Fin 3) ℂ}
    (hP : Pᴴ * (1 - Aᴴ * A) * P = 1) (hS : Sᴴ * (1 - A * Aᴴ) * S = 1) :
    (Matrix.fromBlocks P (Aᴴ * S) (A * P) S)ᴴ * hk_eps *
      Matrix.fromBlocks P (Aᴴ * S) (A * P) S = hk_eps := by
  rw [hk_eps, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  congr 1
  · rw [← hP]; noncomm_ring
  · noncomm_ring
  · noncomm_ring
  · rw [← hS]; noncomm_ring

/-- The normalized eigenbasis indexed by `Fin 2 × (Fin 3 ⊕ Fin 3)`: `(0, u)` spans the
`-i√3`-eigenspace and `(1, u)` the `i√3`-eigenspace; `inl` are the positive and `inr` the
negative directions of the Hermitian form.
Source: `b60c_eigenBasis`; Mathlib `finSumFinEquiv`. -/
def hk_B : Module.Basis (Fin 2 × (Fin 3 ⊕ Fin 3)) ℂ (ℂ ⊗[ℤ] b60_Lattice) :=
  b60c_eigenBasis.reindex (Equiv.prodCongr (Equiv.refl _) (finSumFinEquiv (m := 3) (n := 3)).symm)

lemma hk_B_apply (a : Fin 2) (u : Fin 3 ⊕ Fin 3) :
    hk_B (a, u) = b60_eigen (if a = 0 then -1 else 1) (finSumFinEquiv u) := by
  simp [hk_B]

example : hk_B (0, Sum.inl 0) = b60_eigen (-1) 0 := by
  rw [hk_B_apply]; rfl

/-- The diagonal of `hk_eps`: `1` on `inl`, `-1` on `inr`.
Source: `hk_eps`; `hermSignature_diag_F1569`. -/
def hk_epsd : Fin 3 ⊕ Fin 3 → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

example : hk_epsd (Sum.inr 0) = -1 := rfl

lemma hk_eps_eq : hk_eps = Matrix.diagonal hk_epsd := by
  rw [hk_eps]
  ext (i | i) (j | j) <;> simp [hk_epsd, Matrix.one_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

lemma hk_epsd_eq (u : Fin 3 ⊕ Fin 3) :
    (if (finSumFinEquiv u).val < 3 then (1 : ℂ) else -1) = hk_epsd u := by
  rcases u with k | k
  · rw [finSumFinEquiv_apply_left]; simp [hk_epsd]
  · rw [finSumFinEquiv_apply_right]; simp [hk_epsd]

lemma hk_sign_cases (a : Fin 2) : (if a = 0 then (-1 : ℂ) else 1) = 1 ∨
    (if a = 0 then (-1 : ℂ) else 1) = -1 := by
  fin_cases a <;> simp

lemma hk_B_E (x y : Fin 2 × (Fin 3 ⊕ Fin 3)) :
    b60_E.baseChange ℂ (hk_B x) (hk_B y) =
      if x.2 = y.2 then hk_epsd x.2 * (((if y.1 = 0 then -1 else 1) -
        (if x.1 = 0 then -1 else 1)) / (Complex.I * (Real.sqrt 3 : ℂ))) else 0 := by
  rw [hk_B_apply, hk_B_apply, b60_pairing_eigen]
  by_cases h : x.2 = y.2
  · simp only [h, ↓reduceIte]
    rw [b60c_normalized_diagonal, hk_epsd_eq]
  · have h' : finSumFinEquiv x.2 ≠ finSumFinEquiv y.2 := fun h' => h (finSumFinEquiv.injective h')
    simp only [h, h', ↓reduceIte]

lemma hk_B_conj (a : Fin 2) (u : Fin 3 ⊕ Fin 3) :
    b2_conj b60_Lattice (hk_B (a, u)) = hk_B (if a = 0 then 1 else 0, u) := by
  rw [hk_B_apply, hk_B_apply, b60_conj_eigen _ (hk_sign_cases a)]
  congr 1
  fin_cases a <;> simp

lemma hk_B_omega (a : Fin 2) (u : Fin 3 ⊕ Fin 3) :
    b60_omegaC (hk_B (a, u)) =
      ((if a = 0 then -1 else 1) * Complex.I * (Real.sqrt 3 : ℂ)) • hk_B (a, u) := by
  rw [hk_B_apply, b60_omegaC_eigen _ (hk_sign_cases a)]

/-- The block matrix `diag(Γ, Γ̄)` in the eigenbasis `hk_B`.
Source: the real structure of `ℂ ⊗ b60_Lattice` (conjugation exchanges the eigenspaces,
`b60_conj_eigen`). -/
def hk_blk (Γ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ) :
    Matrix (Fin 2 × (Fin 3 ⊕ Fin 3)) (Fin 2 × (Fin 3 ⊕ Fin 3)) ℂ :=
  Matrix.of fun x y => if x.1 = y.1 then
    (if x.1 = 0 then Γ x.2 y.2 else starRingEnd ℂ (Γ x.2 y.2)) else 0

example : hk_blk 1 = 1 := by
  ext x y
  simp only [hk_blk, Matrix.of_apply, Matrix.one_apply, Prod.ext_iff]
  split_ifs <;> simp_all

/-- The complex-linear map of `ℂ ⊗ b60_Lattice` acting by `Γ` on the `-i√3`-eigenspace and by
`Γ̄` on the `i√3`-eigenspace.
Source: `Matrix.toLin` in the basis `hk_B`. -/
def hk_G (Γ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ) :
    (ℂ ⊗[ℤ] b60_Lattice) →ₗ[ℂ] (ℂ ⊗[ℤ] b60_Lattice) :=
  Matrix.toLin hk_B hk_B (hk_blk Γ)

example : hk_G 1 = LinearMap.id := by
  rw [hk_G, show hk_blk 1 = 1 by
    ext x y
    simp only [hk_blk, Matrix.of_apply, Matrix.one_apply, Prod.ext_iff]
    split_ifs <;> simp_all, Matrix.toLin_one]

/-- The coefficient of `hk_G Γ` from `(b, v)` to `(b, u)`: `Γ u v` on the `-i√3`-eigenspace and
its conjugate on the `i√3`-eigenspace.
Source: `hk_blk`. -/
def hk_coef (Γ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ) (b : Fin 2) (u v : Fin 3 ⊕ Fin 3) : ℂ :=
  if b = 0 then Γ u v else starRingEnd ℂ (Γ u v)

example (Γ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ) (u v : Fin 3 ⊕ Fin 3) :
    hk_coef Γ 0 u v = Γ u v := rfl

lemma hk_G_B (Γ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ) (b : Fin 2) (v : Fin 3 ⊕ Fin 3) :
    hk_G Γ (hk_B (b, v)) = ∑ u, hk_coef Γ b u v • hk_B (b, u) := by
  rw [hk_G, Matrix.toLin_self, Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp [hk_blk, hk_coef]
  · intro a _ hab
    refine Finset.sum_eq_zero fun u _ => ?_
    simp [hk_blk, hab]
  · simp

lemma hk_Gamma_entries {Γ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ}
    (hΓ : Γᴴ * hk_eps * Γ = hk_eps) (v w : Fin 3 ⊕ Fin 3) :
    ∑ u, starRingEnd ℂ (Γ u v) * hk_epsd u * Γ u w = if v = w then hk_epsd v else 0 := by
  have := congrFun (congrFun hΓ v) w
  rw [hk_eps_eq] at this
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
    RCLike.star_def, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
  rw [← this]

/-- The pairing constant `(t - s) / (i √3)` between the eigenvalue signs `s` of `a` and `t` of
`b`.
Source: `b60_pairing_eigen`. -/
def hk_kappa (a b : Fin 2) : ℂ :=
  ((if b = 0 then -1 else 1) - (if a = 0 then -1 else 1)) / (Complex.I * (Real.sqrt 3 : ℂ))

example : hk_kappa 0 0 = 0 := by simp [hk_kappa]

lemma hk_B_E' (a b : Fin 2) (u w : Fin 3 ⊕ Fin 3) :
    b60_E.baseChange ℂ (hk_B (a, u)) (hk_B (b, w)) =
      if u = w then hk_epsd u * hk_kappa a b else 0 := hk_B_E (a, u) (b, w)

lemma hk_G_B_E (Γ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ) (b b' : Fin 2)
    (v w : Fin 3 ⊕ Fin 3) :
    b60_E.baseChange ℂ (hk_G Γ (hk_B (b, v))) (hk_G Γ (hk_B (b', w))) =
      (∑ u, hk_coef Γ b u v * hk_coef Γ b' u w * hk_epsd u) * hk_kappa b b' := by
  rw [hk_G_B, hk_G_B]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hk_B_E',
    smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  ring

lemma hk_G_E {Γ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ}
    (hΓ : Γᴴ * hk_eps * Γ = hk_eps) (x y : ℂ ⊗[ℤ] b60_Lattice) :
    b60_E.baseChange ℂ (hk_G Γ x) (hk_G Γ y) = b60_E.baseChange ℂ x y := by
  have key : (b60_E.baseChange ℂ).compl₁₂ (hk_G Γ) (hk_G Γ) = b60_E.baseChange ℂ := by
    refine LinearMap.ext_basis hk_B hk_B fun ⟨b, v⟩ ⟨b', w⟩ => ?_
    rw [LinearMap.compl₁₂_apply, hk_G_B_E, hk_B_E']
    have h := hk_Gamma_entries hΓ
    fin_cases b <;> fin_cases b'
    · simp [hk_kappa]
    · have h' := h w v
      have e : ∑ u, hk_coef Γ 0 u v * hk_coef Γ 1 u w * hk_epsd u =
          ∑ u, starRingEnd ℂ (Γ u w) * hk_epsd u * Γ u v := by
        refine Finset.sum_congr rfl fun u _ => ?_
        simp only [hk_coef, Fin.isValue, ↓reduceIte, one_ne_zero]
        ring
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
      rw [e, h']
      by_cases hvw : v = w
      · subst hvw; simp
      · simp [hvw, Ne.symm hvw]
    · have h' := h v w
      have e : ∑ u, hk_coef Γ 1 u v * hk_coef Γ 0 u w * hk_epsd u =
          ∑ u, starRingEnd ℂ (Γ u v) * hk_epsd u * Γ u w := by
        refine Finset.sum_congr rfl fun u _ => ?_
        simp only [hk_coef, Fin.isValue, ↓reduceIte, one_ne_zero]
        ring
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
      rw [e, h']
      by_cases hvw : v = w
      · subst hvw; simp
      · simp [hvw]
    · simp [hk_kappa]
  exact LinearMap.congr_fun₂ key x y

lemma hk_G_omega (Γ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ) (x : ℂ ⊗[ℤ] b60_Lattice) :
    hk_G Γ (b60_omegaC x) = b60_omegaC (hk_G Γ x) := by
  have key : hk_G Γ ∘ₗ b60_omegaC = b60_omegaC ∘ₗ hk_G Γ := by
    refine hk_B.ext fun ⟨b, v⟩ => ?_
    simp only [LinearMap.comp_apply, hk_B_omega, map_smul, hk_G_B, map_sum, Finset.smul_sum,
      smul_smul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_comm]
  exact LinearMap.congr_fun key x

lemma hk_G_conj_B (Γ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ) (b : Fin 2)
    (v : Fin 3 ⊕ Fin 3) :
    b2_conj b60_Lattice (hk_G Γ (hk_B (b, v))) = hk_G Γ (hk_B (if b = 0 then 1 else 0, v)) := by
  rw [hk_G_B, hk_G_B, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [b2a_conj_smul, hk_B_conj]
  congr 1
  fin_cases b <;> simp [hk_coef]

lemma hk_G_conj (Γ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ) (x : ℂ ⊗[ℤ] b60_Lattice) :
    b2_conj b60_Lattice (hk_G Γ x) = hk_G Γ (b2_conj b60_Lattice x) := by
  conv_lhs => rw [← hk_B.sum_repr x]
  conv_rhs => rw [← hk_B.sum_repr x]
  simp only [map_sum, map_smul, b2a_conj_smul]
  refine Finset.sum_congr rfl fun ⟨b, v⟩ _ => ?_
  rw [hk_G_conj_B, hk_B_conj]

lemma hk_repr_conj (x : ℂ ⊗[ℤ] b60_Lattice) (p : hk_ι) :
    b60_basis.repr (b2_conj b60_Lattice x) p = starRingEnd ℂ (b60_basis.repr x p) := by
  conv_lhs => rw [← b60_basis.sum_repr x]
  simp only [map_sum, b2a_conj_smul, b60_conj_basis, map_smul, Module.Basis.repr_self,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma hk_toC_of_real (G : (ℂ ⊗[ℤ] b60_Lattice) →ₗ[ℂ] (ℂ ⊗[ℤ] b60_Lattice))
    (hG : ∀ x, b2_conj b60_Lattice (G x) = G (b2_conj b60_Lattice x)) :
    hk_toC (Matrix.of fun p q => (b60_basis.repr (G (b60_basis q)) p).re) = G := by
  refine b60_basis.ext fun q => ?_
  rw [hk_toC_basis]
  conv_rhs => rw [← b60_basis.sum_repr (G (b60_basis q))]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  simp only [Matrix.of_apply]
  apply Complex.conj_eq_iff_re.mp
  rw [← hk_repr_conj, hG, b60_conj_basis]

lemma hk_toC_injective : Function.Injective hk_toC := by
  intro g h hgh
  have := (Matrix.toLin b60_basis b60_basis).injective hgh
  exact Matrix.map_injective Complex.ofReal_injective this

lemma hk_toC_E_basis (g : Matrix hk_ι hk_ι ℝ) (p q : hk_ι) :
    b60_E.baseChange ℂ (hk_toC g (b60_basis p)) (hk_toC g (b60_basis q)) =
      (((gᵀ * hk_E.map (Int.cast : ℤ → ℝ) * g) p q : ℝ) : ℂ) := by
  rw [hk_toC_basis, hk_toC_basis]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hk_E_basis,
    smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma hk_mem_group_of {g : Matrix hk_ι hk_ι ℝ}
    (hE : ∀ x y, b60_E.baseChange ℂ (hk_toC g x) (hk_toC g y) = b60_E.baseChange ℂ x y)
    (hω : ∀ x, hk_toC g (b60_omegaC x) = b60_omegaC (hk_toC g x)) : g ∈ hk_group ℝ := by
  refine ⟨?_, ?_⟩
  · show gᴴ * _ * g = _
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    ext p q
    apply Complex.ofReal_injective
    rw [← hk_toC_E_basis, hE, hk_E_basis]
    simp
  · apply hk_toC_injective
    rw [hk_toC_mul, hk_toC_mul, hk_toC_Omega]
    exact LinearMap.ext hω

lemma hk_fs_inl (k : Fin 3) : finSumFinEquiv (Sum.inl k : Fin 3 ⊕ Fin 3) = Fin.castAdd 3 k :=
  finSumFinEquiv_apply_left k

lemma hk_fs_inr (j : Fin 3) : finSumFinEquiv (Sum.inr j : Fin 3 ⊕ Fin 3) = j.addNat 3 := by
  rw [finSumFinEquiv_apply_right]
  exact Fin.ext (by simp)

lemma hk_frame_B_neg (z : Fin 9 → ℂ) (k : Fin 3) :
    b60_frame z (0, k) = hk_B (0, Sum.inl k) +
      ∑ j : Fin 3, g32m_toMat z j k • hk_B (0, Sum.inr j) := by
  simp [b60_frame, hk_B_apply, hk_fs_inl, hk_fs_inr]

lemma hk_frame_B_pos (z : Fin 9 → ℂ) (j : Fin 3) :
    b60_frame z (1, j) = hk_B (1, Sum.inr j) +
      ∑ k : Fin 3, g32m_toMat z j k • hk_B (1, Sum.inl k) := by
  simp [b60_frame, hk_B_apply, hk_fs_inl, hk_fs_inr]

lemma hk_G_frame_neg (A P S : Matrix (Fin 3) (Fin 3) ℂ) (z : Fin 9 → ℂ) (hz : g32m_toMat z = A)
    (i : Fin 3) :
    hk_G (Matrix.fromBlocks P (Aᴴ * S) (A * P) S) (hk_B (0, Sum.inl i)) =
      ∑ k, P k i • b60_frame z (0, k) := by
  rw [hk_G_B, Fintype.sum_sum_type]
  simp only [hk_frame_B_neg, hz, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul,
    hk_coef, ↓reduceIte, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.mul_apply,
    Finset.sum_smul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

lemma hk_G_frame_pos (A P S : Matrix (Fin 3) (Fin 3) ℂ) (z : Fin 9 → ℂ) (hz : g32m_toMat z = A)
    (i : Fin 3) :
    hk_G (Matrix.fromBlocks P (Aᴴ * S) (A * P) S) (hk_B (1, Sum.inr i)) =
      ∑ j, starRingEnd ℂ (S j i) • b60_frame z (1, j) := by
  rw [hk_G_B, Fintype.sum_sum_type]
  simp only [hk_frame_B_pos, hz, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul,
    hk_coef, one_ne_zero, ↓reduceIte, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂,
    Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_mul, RCLike.star_def,
    Complex.conj_conj, Finset.sum_smul]
  rw [add_comm]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

lemma hk_finrank_F (z : Fin 9 → ℂ) : Module.finrank ℂ ↥(b60_F z) = 6 := by
  rw [b60_F, finrank_span_eq_card (b60_frame_independent z)]
  rfl

open scoped ComplexOrder in
theorem hk_from_origin (σ : g32m_Domain) :
    ∃ g ∈ hk_group ℝ, b60_F σ = (b60_F 0).map (hk_toC g) := by
  set A := g32m_toMat σ with hAdef
  have hA : (1 - Aᴴ * A).PosDef := by
    have hz : (σ : Fin 9 → ℂ) ∈ (g32m_Domain : Set (Fin 9 → ℂ)) := σ.2
    rw [g32m_domain_coe] at hz
    exact hz
  obtain ⟨P, hP⟩ := hk_exists_normalizer hA
  obtain ⟨S, hS⟩ := hk_exists_normalizer (hk_one_sub_mul_conj_posDef hA)
  set Γ := Matrix.fromBlocks P (Aᴴ * S) (A * P) S
  have hΓ := hk_Gamma_unitary hP hS
  set g : Matrix hk_ι hk_ι ℝ :=
    Matrix.of fun p q => (b60_basis.repr (hk_G Γ (b60_basis q)) p).re
  have hgG : hk_toC g = hk_G Γ := hk_toC_of_real _ (hk_G_conj Γ)
  have hg : g ∈ hk_group ℝ := hk_mem_group_of
    (fun x y => by rw [hgG]; exact hk_G_E hΓ x y)
    (fun x => by rw [hgG]; exact hk_G_omega Γ x)
  refine ⟨g, hg, ?_⟩
  have hle : (b60_F 0).map (hk_toC g) ≤ b60_F σ := by
    rw [hgG, b60_F, Submodule.map_span_le]
    rintro _ ⟨⟨a, i⟩, rfl⟩
    fin_cases a
    · have e : b60_frame 0 (0, i) = hk_B (0, Sum.inl i) := by
        rw [hk_frame_B_neg]; simp [g32m_toMat]
      simp only [Fin.zero_eta, Fin.isValue]
      rw [e, hk_G_frame_neg A P S σ rfl]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨(0, k), rfl⟩)
    · have e : b60_frame 0 (1, i) = hk_B (1, Sum.inr i) := by
        rw [hk_frame_B_pos]; simp [g32m_toMat]
      simp only [Fin.mk_one, Fin.isValue]
      rw [e, hk_G_frame_pos A P S σ rfl]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨(1, j), rfl⟩)
  obtain ⟨T, hT⟩ : ∃ T : (ℂ ⊗[ℤ] b60_Lattice) ≃ₗ[ℂ] (ℂ ⊗[ℤ] b60_Lattice),
      (T : _ →ₗ[ℂ] _) = hk_toC g := ⟨hk_toCEquiv hg, rfl⟩
  symm
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [← hT, LinearEquiv.finrank_map_eq, hk_finrank_F, hk_finrank_F]

lemma hk_group_inv {g : Matrix hk_ι hk_ι ℝ} (hg : g ∈ hk_group ℝ) : g⁻¹ ∈ hk_group ℝ := by
  have hu := hk_group_isUnit_det hg
  have h1 : ∀ x, hk_toC g (hk_toC g⁻¹ x) = x := fun x => by
    rw [← LinearMap.comp_apply, ← hk_toC_mul, Matrix.mul_nonsing_inv _ hu, hk_toC_one',
      LinearMap.id_apply]
  refine hk_mem_group_of (fun x y => ?_) (fun x => ?_)
  · rw [← hk_toC_E hg, h1, h1]
  · apply (hk_toCEquiv hg).injective
    rw [hk_toCEquiv_apply, hk_toCEquiv_apply, h1, hk_toC_omega hg, h1]

theorem hk_transitive_aux (τ σ : g32m_Domain) :
    ∃ g ∈ hk_group ℝ, hk_moves g τ σ := by
  obtain ⟨gτ, hgτ, hτ⟩ := hk_from_origin τ
  obtain ⟨gσ, hgσ, hσ⟩ := hk_from_origin σ
  refine ⟨gσ * gτ⁻¹, hk_group_mul hgσ (hk_group_inv hgτ), ?_⟩
  show b60_F σ = (b60_F τ).map (hk_toC (gσ * gτ⁻¹))
  rw [hτ, ← Submodule.map_comp, ← hk_toC_mul, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (hk_group_isUnit_det hgτ), Matrix.mul_one]
  exact hσ

theorem hk_action_exists_aux {g : Matrix hk_ι hk_ι ℝ} (hg : g ∈ hk_group ℝ)
    (τ : g32m_Domain) :
    ∃ σ, hk_moves g τ σ := by
  obtain ⟨T, hT⟩ : ∃ T : (ℂ ⊗[ℤ] b60_Lattice) ≃ₗ[ℂ] (ℂ ⊗[ℤ] b60_Lattice),
      (T : _ →ₗ[ℂ] _) = hk_toC g := ⟨hk_toCEquiv hg, rfl⟩
  have hTx : ∀ x, T x = hk_toC g x := fun x => LinearMap.congr_fun hT x
  have heig : ∀ μ : ℂ, (Module.End.eigenspace b60_omegaC μ).map (T : _ →ₗ[ℂ] _) =
      Module.End.eigenspace b60_omegaC μ := by
    intro μ
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      replace hx := Module.End.mem_eigenspace_iff.mp hx
      apply Module.End.mem_eigenspace_iff.mpr
      rw [LinearEquiv.coe_coe, hTx, ← hk_toC_omega hg, hx, map_smul]
    · intro y hy
      refine ⟨T.symm y, ?_, T.apply_symm_apply y⟩
      replace hy := Module.End.mem_eigenspace_iff.mp hy
      apply Module.End.mem_eigenspace_iff.mpr
      apply T.injective
      rw [map_smul, T.apply_symm_apply, hTx, hk_toC_omega hg, ← hTx, T.apply_symm_apply, hy]
  have hdim (μ : ℂ) : Module.finrank ℂ ↥((b60_F τ).map (hk_toC g) ⊓
      Module.End.eigenspace b60_omegaC μ) = Module.finrank ℂ ↥(b60_F τ ⊓
      Module.End.eigenspace b60_omegaC μ) := by
    rw [← hT]
    have e1 : (b60_F τ).map (T : _ →ₗ[ℂ] _) ⊓ Module.End.eigenspace b60_omegaC μ =
        (b60_F τ ⊓ Module.End.eigenspace b60_omegaC μ).map (T : _ →ₗ[ℂ] _) := by
      rw [Submodule.map_inf _ T.injective, heig]
    rw [e1]
    exact LinearEquiv.finrank_map_eq T _
  have hR := (b60_riemann_iff τ).2 τ.property
  have hR' : b2_IsRiemannForm b60_Lattice ((b60_F τ).map (hk_toC g)) b60_E := by
    refine ⟨hR.alt, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [hk_toC_E hg]
      exact hR.isotropic x hx y hy
    · rintro _ ⟨x, hx, rfl⟩ hne
      have hx0 : x ≠ 0 := by rintro rfl; exact hne (map_zero _)
      rw [hk_toC_conj, hk_toC_E hg]
      exact hR.positive x hx hx0
  obtain ⟨σ, hσ⟩ := b60c_fixed_filtration_chart ((b60_F τ).map (hk_toC g))
    (by rw [← hT, LinearEquiv.finrank_map_eq, b60_F, finrank_span_eq_card
      (b60_frame_independent τ)]; rfl)
    (by rw [hdim]; exact (hk_F_eig_dims τ).1)
    (by rw [hdim]; exact (hk_F_eig_dims τ).2) hR'
  exact ⟨σ, hσ.symm⟩

lemma hk_frame_neg_eq (z : Fin 9 → ℂ) (i : Fin 3) :
    b60_frame z (0, i) = b60c_eigenBasis (0, Fin.castAdd 3 i) +
      ∑ j : Fin 3, g32m_toMat z j i • b60c_eigenBasis (0, Fin.natAdd 3 j) := by
  simp [b60_frame]

lemma hk_frame_pos_eq (z : Fin 9 → ℂ) (i : Fin 3) :
    b60_frame z (1, i) = b60c_eigenBasis (1, Fin.natAdd 3 i) +
      ∑ j : Fin 3, g32m_toMat z i j • b60c_eigenBasis (1, Fin.castAdd 3 j) := by
  simp [b60_frame]

lemma hk_cast_ne_nat (i j : Fin 3) : Fin.castAdd 3 i ≠ Fin.natAdd 3 j := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

lemma hk_repr_frame_neg_cast (z : Fin 9 → ℂ) (i k : Fin 3) :
    b60c_eigenBasis.repr (b60_frame z (0, i)) (0, Fin.castAdd 3 k) = if i = k then 1 else 0 := by
  rw [hk_frame_neg_eq]
  simp only [map_add, map_sum, map_smul, Module.Basis.repr_self, Finsupp.add_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply,
    Prod.mk.injEq, true_and, (hk_cast_ne_nat _ _).symm, ite_false, smul_zero,
    Finset.sum_const_zero, add_zero, (Fin.castAdd_injective 3 3).eq_iff]

lemma hk_repr_frame_neg_nat (z : Fin 9 → ℂ) (i j : Fin 3) :
    b60c_eigenBasis.repr (b60_frame z (0, i)) (0, Fin.natAdd 3 j) = g32m_toMat z j i := by
  rw [hk_frame_neg_eq]
  simp only [map_add, map_sum, map_smul, Module.Basis.repr_self, Finsupp.add_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply,
    Prod.mk.injEq, true_and, hk_cast_ne_nat, ite_false, zero_add,
    (Fin.natAdd_injective 3 3).eq_iff, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma hk_repr_frame_pos (z : Fin 9 → ℂ) (i : Fin 3) (m : Fin 6) :
    b60c_eigenBasis.repr (b60_frame z (1, i)) (0, m) = 0 := by
  rw [hk_frame_pos_eq]
  simp only [map_add, map_sum, map_smul, Module.Basis.repr_self, Finsupp.add_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply,
    Prod.mk.injEq]
  simp

lemma hk_repr_comb (w : Fin 9 → ℂ) (c : Fin 2 × Fin 3 → ℂ) (m : Fin 6) :
    b60c_eigenBasis.repr (∑ p, c p • b60_frame w p) (0, m) =
      ∑ i, c (0, i) * b60c_eigenBasis.repr (b60_frame w (0, i)) (0, m) := by
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [hk_repr_frame_pos, mul_zero, Finset.sum_const_zero, add_zero]

lemma hk_repr_comb_cast (w : Fin 9 → ℂ) (c : Fin 2 × Fin 3 → ℂ) (k : Fin 3) :
    b60c_eigenBasis.repr (∑ p, c p • b60_frame w p) (0, Fin.castAdd 3 k) = c (0, k) := by
  rw [hk_repr_comb]
  simp only [hk_repr_frame_neg_cast, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

lemma hk_repr_comb_nat (w : Fin 9 → ℂ) (c : Fin 2 × Fin 3 → ℂ) (j : Fin 3) :
    b60c_eigenBasis.repr (∑ p, c p • b60_frame w p) (0, Fin.natAdd 3 j) =
      ∑ i, g32m_toMat w j i * c (0, i) := by
  rw [hk_repr_comb]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hk_repr_frame_neg_nat, mul_comm]

lemma hk_repr_comb_zero (w : Fin 9 → ℂ) (c : Fin 2 × Fin 3 → ℂ) (hc : ∀ i, c (0, i) = 0)
    (m : Fin 6) : b60c_eigenBasis.repr (∑ p, c p • b60_frame w p) (0, m) = 0 := by
  rw [hk_repr_comb]
  simp only [hc, zero_mul, Finset.sum_const_zero]

/-- Leading eigen-coordinates of the moved negative frame: `P k i` is the `k`-th coordinate of
`g · f_i` along `b60_eigen (-1) k`, with `f_i = b60_frame τ (0, i)`.
Source: van Geemen, LNM 1594, §5.10 (graph coordinates of the negative plane); plan
`G32RemainingPremises.md`, §2.3, stage S4. -/
def hk_P (τ : Fin 9 → ℂ) (g : Matrix hk_ι hk_ι ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun k i => b60c_eigenBasis.repr (hk_toC g (b60_frame τ (0, i))) (0, Fin.castAdd 3 k)

/-- Trailing eigen-coordinates of the moved negative frame.
Source: as for `hk_P`. -/
def hk_Q (τ : Fin 9 → ℂ) (g : Matrix hk_ι hk_ι ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun j i => b60c_eigenBasis.repr (hk_toC g (b60_frame τ (0, i))) (0, Fin.natAdd 3 j)

example (τ : Fin 9 → ℂ) : hk_P τ 1 = 1 := by
  ext k i
  simp only [hk_P, Matrix.of_apply, hk_toC_one', LinearMap.id_apply, hk_repr_frame_neg_cast,
    Matrix.one_apply, eq_comm]

lemma hk_Q_eq {g : Matrix hk_ι hk_ι ℝ} {τ σ : g32m_Domain} (h : hk_moves g τ σ) :
    hk_Q τ g = g32m_toMat σ * hk_P τ g := by
  ext j i
  have hmem : hk_toC g (b60_frame τ (0, i)) ∈ b60_F σ := by
    rw [h]; exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨(0, i), rfl⟩)
  rw [b60_F, Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  simp only [hk_Q, hk_P, Matrix.of_apply, Matrix.mul_apply, ← hc, hk_repr_comb_nat,
    hk_repr_comb_cast]

lemma hk_toC_neg_eigen {g : Matrix hk_ι hk_ι ℝ} (hg : g ∈ hk_group ℝ) (z : Fin 9 → ℂ)
    (v : Fin 3 → ℂ) :
    b60_omegaC (hk_toC g (∑ i, v i • b60_frame z (0, i))) =
      ((if (0 : Fin 2) = 0 then -1 else 1) * Complex.I * (Real.sqrt 3 : ℂ)) •
        hk_toC g (∑ i, v i • b60_frame z (0, i)) := by
  rw [← hk_toC_omega hg, ← map_smul]
  simp only [↓reduceIte]
  congr 1
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, b60_omegaC_frame]
  simp only [↓reduceIte]
  rw [smul_smul, smul_smul]
  congr 1
  ring

lemma hk_P_det {g : Matrix hk_ι hk_ι ℝ} (hg : g ∈ hk_group ℝ) (τ : g32m_Domain) :
    (hk_P τ g).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hPv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  obtain ⟨σ, hσ⟩ := hk_action_exists_aux hg τ
  set y := ∑ i, v i • b60_frame τ (0, i)
  have hmem : hk_toC g y ∈ b60_F σ := by
    rw [hσ]
    refine Submodule.mem_map_of_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
    exact Submodule.subset_span ⟨(0, i), rfl⟩
  rw [b60_F, Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hlead : ∀ k, c (0, k) = 0 := by
    intro k
    rw [← hk_repr_comb_cast σ c k, hc]
    have := congrFun hPv k
    simp only [Matrix.mulVec, dotProduct, hk_P, Matrix.of_apply, Pi.zero_apply] at this
    rw [← this]
    simp only [y, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hzero : hk_toC g y = 0 := by
    rw [b60c_eigen_reconstruction 0 _ (hk_toC_neg_eigen hg τ v)]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [← hc, hk_repr_comb_zero σ c hlead m, zero_smul]
  have hy : y = 0 := by
    have := congrArg (hk_toCEquiv hg).symm hzero
    rwa [map_zero, ← hk_toCEquiv_apply hg, LinearEquiv.symm_apply_apply] at this
  apply hv
  have hli := b60_frame_independent τ
  have hsub : LinearIndependent ℂ (fun i : Fin 3 => b60_frame τ (0, i)) := by
    simpa only [Function.comp_def] using hli.comp (fun i : Fin 3 => (0, i))
      (by intro i j h; exact congrArg Prod.snd h)
  funext i
  exact (Fintype.linearIndependent_iff.mp hsub) v hy i

lemma hk_repr_toC (g : Matrix hk_ι hk_ι ℝ) (v : ℂ ⊗[ℤ] b60_Lattice) (m : Fin 2 × Fin 6) :
    b60c_eigenBasis.repr (hk_toC g v) m = ∑ p, ∑ q, ((g p q : ℝ) : ℂ) *
      (b60_basis.repr v q * b60c_eigenBasis.repr (b60_basis p) m) := by
  conv_lhs => rw [← b60_basis.sum_repr v]
  simp only [map_sum, map_smul, hk_toC_basis, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

lemma hk_continuous_repr_toC (v : ℂ ⊗[ℤ] b60_Lattice) (m : Fin 2 × Fin 6) :
    Continuous fun g : Matrix hk_ι hk_ι ℝ => b60c_eigenBasis.repr (hk_toC g v) m := by
  simp only [hk_repr_toC]
  refine continuous_finsetSum _ fun p _ => continuous_finsetSum _ fun q _ => ?_
  exact (Complex.continuous_ofReal.comp ((continuous_apply q).comp (continuous_apply p))).mul
    continuous_const

lemma hk_matrixCoordinates_toMat (z : Fin 9 → ℂ) : b60c_matrixCoordinates (g32m_toMat z) = z := by
  funext k
  simp [b60c_matrixCoordinates, g32m_toMat]

theorem hk_moves_open_aux (τ : g32m_Domain) {U : Set g32m_Domain} (hU : IsOpen U) :
    IsOpen {g : hk_group ℝ | ∃ σ ∈ U, hk_moves g.1 τ σ} := by
  obtain ⟨V, hV, hUV⟩ := isOpen_induced_iff.1 hU
  let Φ : hk_group ℝ → Fin 9 → ℂ := fun g =>
    b60c_matrixCoordinates (hk_Q τ g.1 * (hk_P τ g.1)⁻¹)
  have hPc : Continuous fun g : Matrix hk_ι hk_ι ℝ => hk_P τ g :=
    continuous_pi fun k => continuous_pi fun i => hk_continuous_repr_toC _ _
  have hQc : Continuous fun g : Matrix hk_ι hk_ι ℝ => hk_Q τ g :=
    continuous_pi fun k => continuous_pi fun i => hk_continuous_repr_toC _ _
  have hΦc : Continuous Φ := by
    have hP' : Continuous fun g : hk_group ℝ => hk_P τ g.1 := hPc.comp continuous_subtype_val
    have hQ' : Continuous fun g : hk_group ℝ => hk_Q τ g.1 := hQc.comp continuous_subtype_val
    have hinv : Continuous fun g : hk_group ℝ => (hk_P τ g.1)⁻¹ := by
      have e : (fun g : hk_group ℝ => (hk_P τ g.1)⁻¹) =
          fun g => (hk_P τ g.1).det⁻¹ • (hk_P τ g.1).adjugate := by
        funext g
        rw [Matrix.inv_def, Ring.inverse_eq_inv']
      rw [e]
      exact (hP'.matrix_det.inv₀ fun g => hk_P_det g.2 τ).smul hP'.matrix_adjugate
    have hm : Continuous fun g : hk_group ℝ => hk_Q τ g.1 * (hk_P τ g.1)⁻¹ :=
      hQ'.matrix_mul hinv
    exact continuous_pi fun k => (continuous_apply _).comp ((continuous_apply _).comp hm)
  have hΦ : ∀ (g : hk_group ℝ) (σ : g32m_Domain), hk_moves g.1 τ σ → Φ g = σ := by
    intro g σ h
    have hP := hk_P_det g.2 τ
    simp only [Φ]
    rw [hk_Q_eq h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP),
      Matrix.mul_one, hk_matrixCoordinates_toMat]
  have hset : {g : hk_group ℝ | ∃ σ ∈ U, hk_moves g.1 τ σ} = Φ ⁻¹' V := by
    ext g
    show (∃ σ ∈ U, hk_moves g.1 τ σ) ↔ Φ g ∈ V
    constructor
    · rintro ⟨σ, hσU, h⟩
      rw [hΦ g σ h]
      rw [← hUV] at hσU
      exact hσU
    · intro hg
      obtain ⟨σ, h⟩ := hk_action_exists_aux g.2 τ
      refine ⟨σ, ?_, h⟩
      rw [← hUV]
      show (σ : Fin 9 → ℂ) ∈ V
      rw [← hΦ g σ h]
      exact hg
  rw [hset]
  exact hV.preimage hΦc

/-- Coefficients of a rational functional on `b60_Lattice` in the standard basis.
Source: Mathlib `Pi.single`, `Finset.univ_sum_single`; `b2b_dual`. -/
def hk_coeff : b2b_dual b60_Lattice ≃ₗ[ℚ] (hk_ι → ℚ) where
  toFun φ := fun p => φ (Pi.single p 1)
  invFun v :=
    { toFun := fun y => ∑ p, v p * (y p : ℚ)
      map_add' := by
        intro x y
        simp only [Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro n y
        simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, eq_intCast, Int.cast_id,
          zsmul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        ring }
  left_inv φ := by
    apply LinearMap.ext
    intro y
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    conv_rhs => rw [pi_eq_sum_univ y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_zsmul, zsmul_eq_mul, mul_comm]
    congr 2
    funext q
    simp [Pi.single_apply, eq_comm]
  right_inv v := by
    funext p
    simp [Pi.single_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

example : hk_coeff 0 = 0 := map_zero _

lemma hk_coeff_apply (φ : b2b_dual b60_Lattice) (p : hk_ι) :
    hk_coeff φ p = φ (Pi.single p 1) := rfl

/-- The rational matrix `g` acting on functionals by precomposition, in coefficients
`v ↦ v ᵥ* g`.
Source: the contravariant marking `e = I_τ ∘ g⁻¹ ∘ I_σ⁻¹` of review `hlean-rev-spread`;
Mathlib `Matrix.vecMul_vecMul`. -/
def hk_dualEquiv {g : Matrix hk_ι hk_ι ℚ} (hg : IsUnit g.det) :
    b2b_dual b60_Lattice ≃ₗ[ℚ] b2b_dual b60_Lattice :=
  hk_coeff.trans ((
    { toFun := fun v => v ᵥ* g
      invFun := fun v => v ᵥ* g⁻¹
      left_inv := fun v => by
        simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hg, Matrix.vecMul_one]
      right_inv := fun v => by
        simp only [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hg, Matrix.vecMul_one]
      map_add' := fun v w => Matrix.add_vecMul g v w
      map_smul' := fun c v => Matrix.smul_vecMul c v g } : (hk_ι → ℚ) ≃ₗ[ℚ] (hk_ι → ℚ)).trans
    hk_coeff.symm)

example : hk_dualEquiv (g := 1) (by simp) 0 = 0 := map_zero _

lemma hk_coeff_dualEquiv {g : Matrix hk_ι hk_ι ℚ} (hg : IsUnit g.det)
    (φ : b2b_dual b60_Lattice) : hk_coeff (hk_dualEquiv hg φ) = hk_coeff φ ᵥ* g := by
  simp [hk_dualEquiv]

lemma hk_coeff_flat (u : b60_Lattice) (p : hk_ι) :
    hk_coeff (b2b_flat b60_Lattice b60_E ((1 : ℚ) ⊗ₜ u)) p = (b60_E u (Pi.single p 1) : ℚ) := by
  simp [hk_coeff_apply, b2b_flat]

lemma hk_coeff_flat_single (q p : hk_ι) :
    hk_coeff (b2b_flat b60_Lattice b60_E ((1 : ℚ) ⊗ₜ Pi.single q 1)) p = (hk_E q p : ℚ) := by
  rw [hk_coeff_flat]
  simp [hk_E, LinearMap.toMatrix₂'_apply]

lemma hk_coeff_dualAction (φ : b2b_dual b60_Lattice) :
    hk_coeff (b60_dualAction.1 φ) = hk_coeff φ ᵥ* hk_Omega.map (Int.cast : ℤ → ℚ) := by
  funext q
  rw [hk_coeff_apply]
  change φ (b60_omega (Pi.single q 1)) = _
  conv_lhs => rw [pi_eq_sum_univ (b60_omega (Pi.single q 1))]
  rw [map_sum]
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, hk_coeff_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_zsmul, zsmul_eq_mul, mul_comm]
  congr 1
  · congr 1
    funext r
    simp [Pi.single_apply, eq_comm]

lemma hk_musical_basis (q : hk_ι) :
    b2bpol_musical b60_Lattice b60_E (b60_basis q) =
      (1 : ℂ) ⊗ₜ b2b_flat b60_Lattice b60_E ((1 : ℚ) ⊗ₜ Pi.single q 1) := by
  rw [b60_basis, Module.Basis.baseChange_apply, Pi.basisFun_apply, b2bpol_musical_tmul]

lemma hk_dual_flat {g : Matrix hk_ι hk_ι ℚ} (hg : g ∈ hk_group ℚ) (hdet : IsUnit g.det)
    (q : hk_ι) :
    hk_dualEquiv hdet (∑ p, g p q • b2b_flat b60_Lattice b60_E ((1 : ℚ) ⊗ₜ Pi.single p 1)) =
      b2b_flat b60_Lattice b60_E ((1 : ℚ) ⊗ₜ Pi.single q 1) := by
  have h1 : gᴴ * _ * g = _ := hg.1
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
  apply hk_coeff.injective
  rw [hk_coeff_dualEquiv]
  funext s
  rw [hk_coeff_flat_single]
  have := congrArg (fun M : Matrix hk_ι hk_ι ℚ => M q s) h1
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply] at this
  rw [← this]
  simp only [Matrix.vecMul, dotProduct, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    hk_coeff_flat_single, smul_eq_mul, Finset.sum_mul]

lemma hk_musical_toC {g : Matrix hk_ι hk_ι ℚ} (hg : g ∈ hk_group ℚ) (hdet : IsUnit g.det)
    (v : ℂ ⊗[ℤ] b60_Lattice) :
    (hk_dualEquiv hdet).toLinearMap.baseChange ℂ
      (b2bpol_musical b60_Lattice b60_E (hk_toC (hk_ratCast g) v)) =
      b2bpol_musical b60_Lattice b60_E v := by
  have key : (hk_dualEquiv hdet).toLinearMap.baseChange ℂ ∘ₗ
      b2bpol_musical b60_Lattice b60_E ∘ₗ hk_toC (hk_ratCast g) =
      b2bpol_musical b60_Lattice b60_E := by
    refine b60_basis.ext fun q => ?_
    have hc : ∀ p, (((hk_ratCast g p q : ℝ)) : ℂ) • ((1 : ℂ) ⊗ₜ[ℚ]
        b2b_flat b60_Lattice b60_E ((1 : ℚ) ⊗ₜ Pi.single p 1)) =
        (1 : ℂ) ⊗ₜ[ℚ] (g p q • b2b_flat b60_Lattice b60_E ((1 : ℚ) ⊗ₜ Pi.single p 1)) := by
      intro p
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul,
        Rat.smul_one_eq_cast]
      simp [hk_ratCast]
    have hm : b2bpol_musical b60_Lattice b60_E (hk_toC (hk_ratCast g) (b60_basis q)) =
        (1 : ℂ) ⊗ₜ[ℚ] (∑ p, g p q • b2b_flat b60_Lattice b60_E ((1 : ℚ) ⊗ₜ Pi.single p 1)) := by
      rw [hk_toC_basis, map_sum, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_smul, hk_musical_basis, hc]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hm, LinearMap.baseChange_tmul,
      LinearEquiv.coe_coe, hk_dual_flat hg hdet, hk_musical_basis]
  exact LinearMap.congr_fun key v

lemma hk_isUnit_det_rat {g : Matrix hk_ι hk_ι ℚ} (hg : g ∈ hk_group ℚ) : IsUnit g.det := by
  have h := hk_group_isUnit_det (hk_ratCast_mem_group hg)
  rw [hk_ratCast_eq, ← RingHom.map_det] at h
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, map_zero] at h
  exact not_isUnit_zero h

lemma hk_dualEquiv_action {g : Matrix hk_ι hk_ι ℚ} (hg : g ∈ hk_group ℚ) (hdet : IsUnit g.det)
    (u : b2b_dual b60_Lattice) :
    hk_dualEquiv hdet (b60_dualAction.1 u) = b60_dualAction.1 (hk_dualEquiv hdet u) := by
  apply hk_coeff.injective
  rw [hk_coeff_dualEquiv, hk_coeff_dualAction, hk_coeff_dualAction, hk_coeff_dualEquiv,
    Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hg.2]

lemma hk_baseChange_marking {g : Matrix hk_ι hk_ι ℚ} (hdet : IsUnit g.det) (τ σ : g32m_Domain)
    (m : ℂ ⊗[ℚ] b2b_dual b60_Lattice) :
    ((b60_cohomologyEquiv σ).symm.trans ((hk_dualEquiv hdet).trans
      (b60_cohomologyEquiv τ))).toLinearMap.baseChange ℂ
      ((LinearEquiv.baseChange ℚ ℂ _ _ (b60_cohomologyEquiv σ)) m) =
      (LinearEquiv.baseChange ℚ ℂ _ _ (b60_cohomologyEquiv τ))
        ((hk_dualEquiv hdet).toLinearMap.baseChange ℂ m) := by
  induction m using TensorProduct.inductionOn with
  | tmul c φ => simp [LinearEquiv.baseChange_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

lemma hk_dualForm_dualEquiv {g : Matrix hk_ι hk_ι ℚ} (hg : g ∈ hk_group ℚ) (hdet : IsUnit g.det)
    (τ : g32m_Domain) (u v : b2b_dual b60_Lattice) :
    b2b_dualForm b60_Lattice b60_E (hk_dualEquiv hdet u) (hk_dualEquiv hdet v) =
      b2b_dualForm b60_Lattice b60_E u v := by
  have hflat := b60_flat_bijective τ
  have hmus := b2bpol_musical_bijective b60_Lattice b60_E hflat
  set T := hk_toCEquiv (hk_ratCast_mem_group hg)
  set D := (hk_dualEquiv hdet).toLinearMap.baseChange ℂ
  have hc : ∀ x y : b2b_dual b60_Lattice,
      ((b2b_dualForm b60_Lattice b60_E x y : ℚ) : ℂ) =
        (b2b_dualForm b60_Lattice b60_E).baseChange ℂ ((1 : ℂ) ⊗ₜ x) ((1 : ℂ) ⊗ₜ y) := by
    intro x y
    rw [LinearMap.BilinForm.baseChange_tmul, mul_one, Rat.smul_one_eq_cast]
  obtain ⟨w, hw⟩ := hmus.2 ((1 : ℂ) ⊗ₜ u)
  obtain ⟨z, hz⟩ := hmus.2 ((1 : ℂ) ⊗ₜ v)
  have hDu : D ((1 : ℂ) ⊗ₜ u) = (1 : ℂ) ⊗ₜ hk_dualEquiv hdet u := by
    simp [D, LinearMap.baseChange_tmul]
  have hDv : D ((1 : ℂ) ⊗ₜ v) = (1 : ℂ) ⊗ₜ hk_dualEquiv hdet v := by
    simp [D, LinearMap.baseChange_tmul]
  have hTw : ∀ x, D (b2bpol_musical b60_Lattice b60_E x) =
      b2bpol_musical b60_Lattice b60_E (T.symm x) := by
    intro x
    conv_lhs => rw [← T.apply_symm_apply x]
    exact hk_musical_toC hg hdet (T.symm x)
  apply (Rat.cast_injective (α := ℂ))
  rw [hc, hc, ← hDu, ← hDv, ← hw, ← hz, hTw, hTw,
    b2bpol_dualForm_musical _ _ hflat, b2bpol_dualForm_musical _ _ hflat]
  conv_rhs => rw [← T.apply_symm_apply w, ← T.apply_symm_apply z]
  exact (hk_toC_E (hk_ratCast_mem_group hg) _ _).symm

set_option maxRecDepth 20000 in
open HodgeLean.RealDefs HodgeLean.Adapters in

theorem hk_hecke_isog_aux {g : Matrix hk_ι hk_ι ℚ} (hg : g ∈ hk_group ℚ)
    {τ σ : g32m_Domain} (h : hk_moves (hk_ratCast g) τ σ) :
    g32t_KIsog (b60b_univ τ) (b60b_univ σ) := by
  have hdet := hk_isUnit_det_rat hg
  set D := hk_dualEquiv hdet
  let e : HQ (b60b_univ σ).X 1 ≃ₗ[ℚ] HQ (b60b_univ τ).X 1 :=
    (b60_cohomologyEquiv σ).symm.trans (D.trans (b60_cohomologyEquiv τ))
  have hJ : ∀ x, e ((b60b_univ σ).W.J x) = (b60b_univ τ).W.J (e x) := by
    intro x
    obtain ⟨u, rfl⟩ := (b60_cohomologyEquiv σ).surjective x
    change b60_cohomologyEquiv τ (D ((b60_cohomologyEquiv σ).symm
        ((b60_cohomAction σ).1 (b60_cohomologyEquiv σ u)))) =
      (b60_cohomAction τ).1 (b60_cohomologyEquiv τ (D ((b60_cohomologyEquiv σ).symm
        (b60_cohomologyEquiv σ u))))
    rw [← b60_cohomologyEquiv_action, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, ← b60_cohomologyEquiv_action, hk_dualEquiv_action hg hdet]
  have hpol : exteriorPower.map 2 e.toLinearMap
      (polarizationVec (torusCohomology_cupProductOf (b60b_univ σ).X) (b60b_univ σ).pol) =
      polarizationVec (torusCohomology_cupProductOf (b60b_univ τ).X) (b60b_univ τ).pol := by
    let := (torusCohomology_cupProductOf (b60b_univ τ).X).finite
    let := (torusCohomology_cupProductOf (b60b_univ σ).X).finite
    apply b60c_bivector_map_of_dualForm _ (b60b_member σ).nondegenerate
      (b60b_member τ).nondegenerate
    intro x y
    obtain ⟨u, rfl⟩ := (b60_cohomologyEquiv σ).surjective x
    obtain ⟨v, rfl⟩ := (b60_cohomologyEquiv σ).surjective y
    change polarizationForm (torusCohomology_cupProductOf (b60b_model τ))
        (b60b_member τ).nondegenerate
        (b60_cohomologyEquiv τ (D ((b60_cohomologyEquiv σ).symm (b60_cohomologyEquiv σ u))))
        (b60_cohomologyEquiv τ (D ((b60_cohomologyEquiv σ).symm (b60_cohomologyEquiv σ v)))) = _
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    exact (b60_cohomologyEquiv_form τ _ _).trans
      ((hk_dualForm_dualEquiv hg hdet τ u v).trans (b60_cohomologyEquiv_form σ u v).symm)
  have hF : (b60c_F (b60b_univ σ)).map (e.toLinearMap.baseChange ℂ) = b60c_F (b60b_univ τ) := by
    have hσ : b60c_F (b60b_univ σ) =
        (b60_F σ).map (b60b_homologyCohomologyEquiv σ).toLinearMap :=
      (b60b_homologyCohomology_F σ).symm
    have hτ : b60c_F (b60b_univ τ) =
        (b60_F τ).map (b60b_homologyCohomologyEquiv τ).toLinearMap :=
      (b60b_homologyCohomology_F τ).symm
    have key : ∀ v, e.toLinearMap.baseChange ℂ
        (b60b_homologyCohomologyEquiv σ (hk_toC (hk_ratCast g) v)) =
        b60b_homologyCohomologyEquiv τ v := by
      intro v
      rw [b60c_homologyCohomology_fixed, b60c_homologyCohomology_fixed]
      exact (hk_baseChange_marking hdet τ σ _).trans (by rw [hk_musical_toC hg hdet])
    rw [hσ, hτ, h]
    erw [← Submodule.map_comp, ← Submodule.map_comp]
    congr 1
    exact LinearMap.ext key
  obtain ⟨N, hN, f, hf, hi, -, hfJ, hfpol⟩ := b60c_uniformization (b60b_univ τ) σ e hJ hF hpol
  have hNq : (0 : ℚ) < (N : ℚ) ^ 2 := by
    have : (0 : ℚ) < N := Nat.cast_pos.mpr hN
    positivity
  refine ⟨f, ?_⟩
  refine ⟨hf, ?_⟩
  refine ⟨hi, ?_⟩
  refine ⟨?_, ?_⟩
  · intro x
    exact hfJ x
  · exact ⟨(N : ℚ) ^ 2, hNq, hfpol⟩

theorem hk_weilAlg_of_open_aux {U : Set g32m_Domain} (hU : IsOpen U) (hne : U.Nonempty)
    (hAlg : ∀ m ∈ U, g32t_WeilAlg (b60b_univ m)) (τ : g32m_Domain) :
    g32t_WeilAlg (b60b_univ τ) := by
  obtain ⟨m, hm⟩ := hne
  obtain ⟨g₀, hg₀, h₀⟩ := hk_transitive_aux τ m
  obtain ⟨V, hV, hVS⟩ := isOpen_induced_iff.1 (hk_moves_open_aux τ hU)
  have hg₀V : g₀ ∈ V := by
    have : (⟨g₀, hg₀⟩ : hk_group ℝ) ∈ Subtype.val ⁻¹' V := by
      rw [hVS]; exact ⟨m, hm, h₀⟩
    exact this
  obtain ⟨_, hyV, q, hq, rfl⟩ := mem_closure_iff.1 (hk_rational_dense_aux hg₀) V hV hg₀V
  have hqS : (⟨hk_ratCast q, hk_ratCast_mem_group hq⟩ : hk_group ℝ) ∈ Subtype.val ⁻¹' V := hyV
  rw [hVS] at hqS
  obtain ⟨σ, hσU, hσ⟩ := hqS
  have hP : ∀ x : g32m_Domain, g32t_PolarizedWeil (b60b_univ x) := fun x =>
    ((g32t_isMember_iff _).1 (b60b_member x)).1
  exact g32tr_weilAlg_pullback _ _ (hP τ) (hP σ) (hk_hecke_isog_aux hq hσ) (hAlg σ hσU)


end HodgeLean.Foundations.Program
