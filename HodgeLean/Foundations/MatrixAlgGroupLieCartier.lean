import HodgeLean.Foundations.MatrixAlgGroupLieBasic

/-! # Reducedness of intersections of matrix groups in characteristic zero

The tangent space at `1` of `G ∩ H` is the intersection of the tangent spaces, for matrix
algebraic groups over an algebraically closed field of characteristic zero. The route avoids
group schemes:

* the left-invariant derivation `D_X f = Σ (xX)_{ij} ∂f/∂x_{ij}` of a tangent vector `X ∈ 𝔤`
  preserves the vanishing ideal `I(G)` (its value at `g ∈ G` is the differential at `1` of the
  left translate of `f` by `g`);
* hence `D_X` preserves `J = I(G) + I(H)` when `X ∈ 𝔤 ∩ 𝔥`;
* Seidenberg's lemma: in characteristic zero, `aᵐ ∈ J` gives `(D a)^{2m} ∈ J`;
* the Nullstellensatz: for `f ∈ I(G ∩ H)`, the product `f · det` lies in the radical of `J`;
* evaluating `D_X (f · det)` at `1` gives the differential of `f` at `1` in the direction `X`.

The centralizer of a set `S` of invertible matrices is presented by the linear equations
`xs - sx`, and its Lie algebra is the commutant of `S` (a line argument over an infinite field).
-/

noncomputable section
set_option maxHeartbeats 400000

namespace HodgeLean.Foundations

open MvPolynomial Matrix HodgeLean.Foundations.Program

variable {k : Type*} [Field k] {n : ℕ}

/-! ## Seidenberg's lemma -/

/-- One step of Seidenberg's lemma for a derivation `D` preserving an ideal `J`, over a
`ℚ`-algebra: `a^{r+1} (D a)^s ∈ J` gives `a^r (D a)^{s+2} ∈ J`.
Source: Kaplansky, *An Introduction to Differential Algebra*, Lemma 1.8; Seidenberg,
*Differential ideals in rings of finitely generated type*, Amer. J. Math. 89 (1967). -/
theorem g1_seidenberg_step [CharZero k] {A : Type*} [CommRing A] [Algebra k A]
    (D : Derivation k A A) (J : Ideal A) (hJ : ∀ x ∈ J, D x ∈ J) (a : A) (r s : ℕ)
    (h : a ^ (r + 1) * D a ^ s ∈ J) : a ^ r * D a ^ (s + 2) ∈ J := by
  have h1 := J.mul_mem_left (D a) (hJ _ h)
  have h2 : D a * D (a ^ (r + 1) * D a ^ s) =
      ((r : A) + 1) * (a ^ r * D a ^ (s + 2)) + (s : A) * D (D a) * (a ^ (r + 1) * D a ^ s) := by
    rw [Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow]
    rcases s with _ | s
    · simp only [smul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    · simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
      push_cast
      ring
  rw [h2] at h1
  have h3 : ((r : A) + 1) * (a ^ r * D a ^ (s + 2)) ∈ J :=
    (J.add_mem_iff_left (J.mul_mem_left _ h)).mp h1
  have hr : ((r : k) + 1) ≠ 0 := Nat.cast_add_one_ne_zero r
  have h4 := J.mul_mem_left (algebraMap k A ((r : k) + 1)⁻¹) h3
  rwa [← mul_assoc, show ((r : A) + 1) = algebraMap k A ((r : k) + 1) by simp, ← map_mul,
    inv_mul_cancel₀ hr, map_one, one_mul] at h4

/-- **Seidenberg's lemma.** Over a `ℚ`-algebra, a derivation preserving an ideal `J` maps an
element `a` with `aᵐ ∈ J` to an element with `(D a)^{2m} ∈ J`.
Source: Kaplansky, *An Introduction to Differential Algebra*, Lemma 1.8; Seidenberg,
*Differential ideals in rings of finitely generated type*, Amer. J. Math. 89 (1967). -/
theorem g1_seidenberg [CharZero k] {A : Type*} [CommRing A] [Algebra k A]
    (D : Derivation k A A) (J : Ideal A) (hJ : ∀ x ∈ J, D x ∈ J) (a : A) (m : ℕ)
    (h : a ^ m ∈ J) : D a ^ (2 * m) ∈ J := by
  have key : ∀ j r s : ℕ, a ^ (r + j) * D a ^ s ∈ J → a ^ r * D a ^ (s + 2 * j) ∈ J := by
    intro j
    induction j with
    | zero => intro r s h; simpa using h
    | succ j ih =>
      intro r s h
      have := ih r (s + 2) (g1_seidenberg_step D J hJ a (r + j) s (by
        rwa [show r + j + 1 = r + (j + 1) by omega]))
      rwa [show s + 2 + 2 * j = s + 2 * (j + 1) by ring] at this
  simpa using key m 0 0 (by simpa using h)

/-! ## Differentials at `1` and point derivations -/

/-- The differential at `1` in a fixed direction `Y`, as a linear form on polynomials.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.16.1 and §3.3. -/
def g1_diffAt (Y : Matrix (Fin n) (Fin n) k) : MvPolynomial (Fin n × Fin n) k →ₗ[k] k where
  toFun f := g1_differential f Y
  map_add' f g := by
    simp only [g1_differential_apply_dir, map_add, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [g1_differential_apply_dir, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ij _ ↦ ?_
    rw [Derivation.map_smul, MvPolynomial.smul_eval]
    ring

/-- `g1_diffAt Y` is the differential at `1` in the direction `Y`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.16.1. -/
theorem g1_diffAt_apply (Y : Matrix (Fin n) (Fin n) k) (f : MvPolynomial (Fin n × Fin n) k) :
    g1_diffAt Y f = g1_differential f Y := rfl

example (Y : Matrix (Fin n) (Fin n) k) : g1_diffAt Y (C 1) = 0 := by
  simp [g1_diffAt_apply, g1_differential]

/-- The differential at `1` of a coordinate function.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.16.1. -/
theorem g1_differential_X (ij : Fin n × Fin n) (Y : Matrix (Fin n) (Fin n) k) :
    g1_differential (X ij) Y = Y ij.1 ij.2 := by
  classical
  simp [g1_differential_apply_dir, pderiv_X, Pi.single_apply]

/-- The differential at `1` of a constant is zero.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.16.1. -/
theorem g1_differential_C (a : k) (Y : Matrix (Fin n) (Fin n) k) :
    g1_differential (C a : MvPolynomial (Fin n × Fin n) k) Y = 0 := by
  simp [g1_differential_apply_dir]

/-- The differential at `1` is linear over constants.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.16.1. -/
theorem g1_differential_C_mul (a : k) (p : MvPolynomial (Fin n × Fin n) k)
    (Y : Matrix (Fin n) (Fin n) k) :
    g1_differential (C a * p) Y = a * g1_differential p Y := by
  rw [g1_differential_mul, g1_differential_C, eval_C]
  ring

/-- A linear form `L` on polynomials satisfying the Leibniz rule at a point `x` (a point
derivation) is `f ↦ Σ L(x_i) ∂f/∂x_i (x)`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.16.1 (tangent vectors as point
derivations). -/
theorem g1_pointDeriv_eq {σ : Type*} [Fintype σ] (x : σ → k)
    (L : MvPolynomial σ k →ₗ[k] k)
    (hL : ∀ p q, L (p * q) = eval x p * L q + eval x q * L p) (f : MvPolynomial σ k) :
    L f = ∑ i, L (X i) * eval x (pderiv i f) := by
  classical
  have h1 : L 1 = 0 := by
    have := hL 1 1
    simp only [mul_one, map_one, one_mul] at this
    simpa using this
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [show (C a : MvPolynomial σ k) = a • (1 : MvPolynomial σ k) by
      rw [MvPolynomial.smul_eq_C_mul, mul_one], map_smul, h1]
    simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p i hp =>
    have hd : ∀ j, eval x (pderiv j (p * X i)) =
        eval x p * (if j = i then 1 else 0) + x i * eval x (pderiv j p) := by
      intro j
      rw [Derivation.leibniz, pderiv_X]
      by_cases h : j = i
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [hL, hp]
    simp only [hd, mul_add, Finset.sum_add_distrib, eval_X]
    congr 1
    · simp [mul_comm]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      ring

/-! ## The left-invariant derivation of a tangent vector -/

/-- The left-invariant derivation `f ↦ Σ_{ij} (xX)_{ij} ∂f/∂x_{ij}` of `k[x_{ij}]` attached to a
matrix `X`, written `Y` below.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §3.4 (left-invariant derivations) and §3.9. -/
def g1_leftDeriv (Y : Matrix (Fin n) (Fin n) k) :
    Derivation k (MvPolynomial (Fin n × Fin n) k) (MvPolynomial (Fin n × Fin n) k) :=
  mkDerivation k fun ij ↦ ∑ l, X (ij.1, l) * C (Y l ij.2)

example (Y : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    g1_leftDeriv Y (X (i, j)) = ∑ l, X (i, l) * C (Y l j) :=
  mkDerivation_X _ _ _

/-- The value at `g` of the left-invariant derivation attached to `Y`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §3.4. -/
theorem g1_eval_leftDeriv (g : Matrix.GeneralLinearGroup (Fin n) k)
    (Y : Matrix (Fin n) (Fin n) k) (f : MvPolynomial (Fin n × Fin n) k) :
    eval (g1_coords g) (g1_leftDeriv Y f) =
      ∑ ij, ((g : Matrix (Fin n) (Fin n) k) * Y) ij.1 ij.2 * eval (g1_coords g) (pderiv ij f) := by
  let L : MvPolynomial (Fin n × Fin n) k →ₗ[k] k :=
    (aeval (g1_coords g)).toLinearMap ∘ₗ (g1_leftDeriv Y).toLinearMap
  have hL : ∀ p, L p = eval (g1_coords g) (g1_leftDeriv Y p) := fun p ↦ by
    simp [L]
  rw [← hL, g1_pointDeriv_eq (g1_coords g) L (fun p q ↦ by
    simp only [hL, Derivation.leibniz, smul_eq_mul, map_add, map_mul])]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  rw [hL]
  simp [g1_leftDeriv, mkDerivation_X, Matrix.mul_apply, g1_coords]

/-- The differential at `1` of the left translate by `g` of `f`, in the direction `Y`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §3.4. -/
theorem g1_differential_leftTranslate (g : Matrix.GeneralLinearGroup (Fin n) k)
    (Y : Matrix (Fin n) (Fin n) k) (f : MvPolynomial (Fin n × Fin n) k) :
    g1_differential (g1_leftTranslateBind g f) Y =
      ∑ ij, ((g : Matrix (Fin n) (Fin n) k) * Y) ij.1 ij.2 * eval (g1_coords g) (pderiv ij f) := by
  classical
  let L : MvPolynomial (Fin n × Fin n) k →ₗ[k] k :=
    g1_diffAt Y ∘ₗ (bind₁ (fun ij ↦ ∑ l, C ((g : Matrix (Fin n) (Fin n) k) ij.1 l) *
      X (l, ij.2))).toLinearMap
  have hL : ∀ p, L p = g1_differential (g1_leftTranslateBind g p) Y := fun p ↦ rfl
  have h1 : ∀ p, eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k))
      (g1_leftTranslateBind g p) = eval (g1_coords g) p := fun p ↦ by
    rw [g1_eval_leftTranslateBind, mul_one]
  rw [← hL, g1_pointDeriv_eq (g1_coords g) L (fun p q ↦ by
    simp only [hL]
    rw [show g1_leftTranslateBind g (p * q) =
        g1_leftTranslateBind g p * g1_leftTranslateBind g q from map_mul _ _ _, g1_differential_mul, h1, h1])]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  rw [hL]
  congr 1
  simp only [g1_leftTranslateBind, bind₁_X_right]
  rw [← g1_diffAt_apply, map_sum]
  simp [g1_diffAt_apply, g1_differential_C_mul, g1_differential_X, Matrix.mul_apply]

/-! ## Vanishing ideals and tangent spaces -/

/-- Membership in the vanishing ideal of a set of invertible matrices.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.1.1. -/
theorem g1_mem_vanishingIdealSet_iff {S : Set (Matrix.GeneralLinearGroup (Fin n) k)}
    {f : MvPolynomial (Fin n × Fin n) k} :
    f ∈ g1_vanishingIdealSet S ↔ ∀ g ∈ S, eval (g1_coords g) f = 0 := by
  constructor
  · intro hf g hg
    exact (mem_vanishingIdeal_iff.mp hf) _ ⟨g, hg, rfl⟩
  · rintro hf
    refine mem_vanishingIdeal_iff.mpr ?_
    rintro _ ⟨g, hg, rfl⟩
    exact hf g hg

/-- A larger set has a smaller vanishing ideal.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.1.1. -/
theorem g1_vanishingIdealSet_anti {S T : Set (Matrix.GeneralLinearGroup (Fin n) k)}
    (h : S ⊆ T) : g1_vanishingIdealSet T ≤ g1_vanishingIdealSet S := fun _ hf ↦
  g1_mem_vanishingIdealSet_iff.mpr fun g hg ↦ g1_mem_vanishingIdealSet_iff.mp hf g (h hg)

/-- Membership in the tangent space at `1` of a set of invertible matrices.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.16.2. -/
theorem g1_mem_lieOfSet_iff {S : Set (Matrix.GeneralLinearGroup (Fin n) k)}
    {Y : Matrix (Fin n) (Fin n) k} :
    Y ∈ g1_lieOfSet S ↔ ∀ f ∈ g1_vanishingIdealSet S, g1_differential f Y = 0 := by
  simp [g1_lieOfSet]

/-- The presenting equations lie in the vanishing ideal.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.1.1 and §1.1. -/
theorem g1_equations_le_vanishingIdeal (G : MatrixAlgGroup k n) :
    G.equations ≤ g1_vanishingIdeal G := fun f hf ↦
  g1_mem_vanishingIdealSet_iff.mpr fun g hg ↦ (G.equations_iff g).mp hg f hf

/-- The determinant of the coordinate matrix evaluated at `1`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.6. -/
theorem g1_eval_one_det :
    eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k)) (g1_varMatrix k n).det = 1 := by
  rw [RingHom.map_det, g1_mapMatrix_eval_varMatrix]
  simp

/-- The value at `1` of the left-invariant derivation of `Y` is the differential in direction `Y`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §3.4. -/
theorem g1_eval_one_leftDeriv (Y : Matrix (Fin n) (Fin n) k)
    (f : MvPolynomial (Fin n × Fin n) k) :
    eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k)) (g1_leftDeriv Y f) =
      g1_differential f Y := by
  rw [g1_eval_leftDeriv, g1_differential_apply_dir]
  simp

/-- The left-invariant derivation of a tangent vector `Y ∈ 𝔤` preserves the vanishing ideal of
`G`: its value at `g ∈ G` is the differential at `1` of the left translate by `g`, which again
vanishes on `G`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §3.4 and §3.5. -/
theorem g1_leftDeriv_mem_vanishingIdeal (G : MatrixAlgGroup k n) {Y : Matrix (Fin n) (Fin n) k}
    (hY : Y ∈ g1_lieAlgebra G) {f : MvPolynomial (Fin n × Fin n) k}
    (hf : f ∈ g1_vanishingIdeal G) : g1_leftDeriv Y f ∈ g1_vanishingIdeal G := by
  refine g1_mem_vanishingIdealSet_iff.mpr fun g hg ↦ ?_
  rw [g1_eval_leftDeriv, ← g1_differential_leftTranslate]
  refine g1_mem_lieOfSet_iff.mp hY _ (g1_mem_vanishingIdealSet_iff.mpr fun h hh ↦ ?_)
  rw [g1_eval_leftTranslateBind]
  exact g1_mem_vanishingIdealSet_iff.mp hf _ (G.carrier.mul_mem hg hh)

/-! ## The intersection -/

/-- **Lie algebra of an intersection, the hard inclusion.** Over an algebraically closed field of
characteristic zero, `𝔤 ∩ 𝔥 ⊆ 𝔩𝔦𝔢(G ∩ H)`. For `f ∈ I(G ∩ H)`, the Nullstellensatz puts
`f · det` in the radical of `J = I(G) + I(H)`; the left-invariant derivation `D` of `Y ∈ 𝔤 ∩ 𝔥`
preserves `J`, so Seidenberg's lemma gives `(D (f · det))^{2m} ∈ J ⊆ I(G ∩ H)`; at `1` this is
the differential of `f` in the direction `Y`. This is the reducedness input of Cartier's theorem
for these groups.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §6.12; Humphreys, *Linear Algebraic Groups*,
§12.5 and §13.1; Seidenberg, *Differential ideals in rings of finitely generated type*, Amer. J.
Math. 89 (1967). -/
theorem g1_lieAlgebra_inf_le [IsAlgClosed k] [CharZero k] (G H I : MatrixAlgGroup k n)
    (hI : I.carrier = G.carrier ⊓ H.carrier) :
    g1_lieAlgebra G ⊓ g1_lieAlgebra H ≤ g1_lieAlgebra I := by
  rintro Y ⟨hYG, hYH⟩
  refine g1_mem_lieOfSet_iff.mpr fun f hf ↦ ?_
  have hmemI : ∀ g, g ∈ I.carrier ↔ g ∈ G.carrier ∧ g ∈ H.carrier := fun g ↦ by
    rw [hI, Subgroup.mem_inf]
  have hJI : g1_vanishingIdeal G ⊔ g1_vanishingIdeal H ≤ g1_vanishingIdeal I :=
    sup_le (g1_vanishingIdealSet_anti fun g hg ↦ ((hmemI g).mp hg).1)
      (g1_vanishingIdealSet_anti fun g hg ↦ ((hmemI g).mp hg).2)
  have hDJ : ∀ p ∈ g1_vanishingIdeal G ⊔ g1_vanishingIdeal H,
      g1_leftDeriv Y p ∈ g1_vanishingIdeal G ⊔ g1_vanishingIdeal H := by
    intro p hp
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hp
    rw [map_add]
    exact add_mem (Ideal.mem_sup_left (g1_leftDeriv_mem_vanishingIdeal G hYG hy))
      (Ideal.mem_sup_right (g1_leftDeriv_mem_vanishingIdeal H hYH hz))
  have ha : f * (g1_varMatrix k n).det ∈ (g1_vanishingIdeal G ⊔ g1_vanishingIdeal H).radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := k), mem_vanishingIdeal_iff]
    intro x hx
    rw [mem_zeroLocus_iff] at hx
    change eval x (f * (g1_varMatrix k n).det) = 0
    have hdetx : eval x (g1_varMatrix k n).det = (Matrix.of fun i j ↦ x (i, j)).det := by
      rw [RingHom.map_det]
      congr 1
      ext i j
      simp [g1_varMatrix]
    by_cases hdet : (Matrix.of fun i j ↦ x (i, j)).det = 0
    · rw [map_mul, hdetx, hdet, mul_zero]
    · let g : Matrix.GeneralLinearGroup (Fin n) k :=
        Matrix.nonsingInvUnit _ (isUnit_iff_ne_zero.mpr hdet)
      have hgx : g1_coords g = x := by
        funext ij
        rfl
      have hmem : ∀ K : MatrixAlgGroup k n, g1_vanishingIdeal K ≤
          g1_vanishingIdeal G ⊔ g1_vanishingIdeal H → g ∈ K.carrier := fun K hK ↦
        (K.equations_iff g).mpr fun p hp ↦ by
          have := hx p (hK (g1_equations_le_vanishingIdeal K hp))
          change eval (g1_coords g) p = 0
          rw [hgx]
          exact this
      have hgI : g ∈ I.carrier := (hmemI g).mpr ⟨hmem G le_sup_left, hmem H le_sup_right⟩
      have := g1_mem_vanishingIdealSet_iff.mp hf g hgI
      rw [hgx] at this
      rw [map_mul, this, zero_mul]
  obtain ⟨m, hm⟩ := ha
  have h2 := hJI (g1_seidenberg (g1_leftDeriv Y) _ hDJ _ m hm)
  have h3 := g1_mem_vanishingIdealSet_iff.mp h2 1 I.carrier.one_mem
  rw [map_pow] at h3
  have h4 := (pow_eq_zero_iff'.mp h3).1
  have hf1 := g1_mem_vanishingIdealSet_iff.mp hf 1 I.carrier.one_mem
  rwa [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hf1,
    g1_eval_one_det, zero_mul, zero_add, one_mul, g1_eval_one_leftDeriv] at h4

/-! ## Centralizers -/

/-- The linear polynomial `(x s - s x)_{ij}` in the matrix entries.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.7. -/
def g1_commEquation (s : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    MvPolynomial (Fin n × Fin n) k :=
  ∑ l, (C (s l j) * X (i, l) - C (s i l) * X (l, j))

example (i j : Fin n) : g1_commEquation (1 : Matrix (Fin n) (Fin n) k) i j = 0 := by
  simp [g1_commEquation, Matrix.one_apply]

/-- The value of `(x s - s x)_{ij}` at a point.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.7. -/
theorem g1_eval_commEquation (x : Fin n × Fin n → k) (s : Matrix (Fin n) (Fin n) k)
    (i j : Fin n) :
    eval x (g1_commEquation s i j) =
      (Matrix.of (fun a b ↦ x (a, b)) * s - s * Matrix.of (fun a b ↦ x (a, b))) i j := by
  simp [g1_commEquation, Matrix.mul_apply, Finset.sum_sub_distrib, mul_comm]

/-- The differential at `1` of `(x s - s x)_{ij}` in the direction `Y` is `(Y s - s Y)_{ij}`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §3.11. -/
theorem g1_differential_commEquation (s Y : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    g1_differential (g1_commEquation s i j) Y = (Y * s - s * Y) i j := by
  rw [← g1_diffAt_apply, g1_commEquation, map_sum]
  simp only [map_sub, g1_diffAt_apply, g1_differential_C_mul, g1_differential_X]
  simp [Matrix.mul_apply, Finset.sum_sub_distrib, mul_comm]

/-- The centralizer `Z(S)` in `GL_n` of a set `S` of invertible matrices, presented by the linear
equations `(x s - s x)_{ij}` for `s ∈ S`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.7; Humphreys, *Linear Algebraic Groups*,
§8.2. -/
def g1_centralizerGroup (S : Set (Matrix.GeneralLinearGroup (Fin n) k)) : MatrixAlgGroup k n :=
  g1_ofEquations
    {f | ∃ s ∈ S, ∃ i j : Fin n, f = g1_commEquation (s : Matrix (Fin n) (Fin n) k) i j}
    (Subgroup.centralizer S)
    (by
      intro g
      have hx : Matrix.of (fun a b ↦ g1_coords g (a, b)) = (g : Matrix (Fin n) (Fin n) k) := by
        ext a b
        rfl
      rw [Subgroup.mem_centralizer_iff]
      constructor
      · rintro h f ⟨s, hs, i, j, rfl⟩
        rw [g1_eval_commEquation, hx, ← Matrix.GeneralLinearGroup.coe_mul,
          ← Matrix.GeneralLinearGroup.coe_mul, h s hs, sub_self]
        rfl
      · intro h s hs
        ext i j
        have := h _ ⟨s, hs, i, j, rfl⟩
        rw [g1_eval_commEquation, hx, Matrix.sub_apply, sub_eq_zero] at this
        simpa using this.symm)

/-- The point set of `g1_centralizerGroup S` is the centralizer of `S`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.7. -/
theorem g1_centralizerGroup_carrier (S : Set (Matrix.GeneralLinearGroup (Fin n) k)) :
    (g1_centralizerGroup S).carrier = Subgroup.centralizer S := rfl

example (S : Set (Matrix.GeneralLinearGroup (Fin n) k)) :
    (1 : Matrix.GeneralLinearGroup (Fin n) k) ∈ (g1_centralizerGroup S).carrier :=
  (g1_centralizerGroup S).carrier.one_mem

/-- **The Lie algebra of a centralizer in `GL_n`** is the commutant: `Z_{GL_n}(S)` is the unit
group of the commutant algebra `A`, a linear subspace through `1`, and a polynomial vanishing on
`A ∩ GL_n` has zero differential along `A` (restrict `f · det` to the line `1 + tY`).
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §3.11 and §9.1; Humphreys, *Linear Algebraic
Groups*, §13.4. -/
theorem g1_lieAlgebra_centralizerGroup [Infinite k]
    (S : Set (Matrix.GeneralLinearGroup (Fin n) k)) :
    g1_lieAlgebra (g1_centralizerGroup S) = g1_lieCentralizer S := by
  ext Y
  rw [g1_lieCentralizer, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
  constructor
  · rintro hY _ ⟨s, hs, rfl⟩
    ext i j
    have h := g1_mem_lieOfSet_iff.mp hY (g1_commEquation (s : Matrix (Fin n) (Fin n) k) i j)
      (g1_equations_le_vanishingIdeal _ (Ideal.subset_span ⟨s, hs, i, j, rfl⟩))
    rw [g1_differential_commEquation, Matrix.sub_apply, sub_eq_zero] at h
    exact h.symm
  · intro hY
    refine g1_mem_lieOfSet_iff.mpr fun f hf ↦ ?_
    -- the line `t ↦ 1 + t Y`
    let φ : MvPolynomial (Fin n × Fin n) k →ₐ[k] Polynomial k :=
      aeval fun ij ↦ Polynomial.C ((1 : Matrix (Fin n) (Fin n) k) ij.1 ij.2) +
        Polynomial.C (Y ij.1 ij.2) * Polynomial.X
    have heval : ∀ p t, (φ p).eval t = eval (fun ij ↦ (1 + t • Y) ij.1 ij.2) p := by
      intro p t
      rw [← Polynomial.coe_aeval_eq_eval, ← AlgHom.comp_apply, comp_aeval]
      change eval _ p = _
      congr 2
      funext ij
      simp only [Polynomial.coe_aeval_eq_eval, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have h0 : (fun ij : Fin n × Fin n ↦ ((1 : Matrix (Fin n) (Fin n) k) + (0 : k) • Y) ij.1 ij.2) =
        g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k) := by
      funext ij
      simp [g1_coords]
    let L : MvPolynomial (Fin n × Fin n) k →ₗ[k] k :=
      Polynomial.leval (0 : k) ∘ₗ Polynomial.derivative ∘ₗ φ.toLinearMap
    have hL : ∀ p, L p = (Polynomial.derivative (φ p)).eval 0 := fun p ↦ rfl
    have hLeib : ∀ p q, L (p * q) =
        eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k)) p * L q +
          eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k)) q * L p := by
      intro p q
      simp only [hL, map_mul, Polynomial.derivative_mul, Polynomial.eval_add,
        Polynomial.eval_mul, heval, h0]
      ring
    have hLf : L f = g1_differential f Y := by
      rw [g1_pointDeriv_eq _ L hLeib, g1_differential_apply_dir]
      refine Finset.sum_congr rfl fun ij _ ↦ ?_
      congr 1
      simp [hL, φ]
    -- `f · det` vanishes on the line
    have hzero : φ (f * (g1_varMatrix k n).det) = 0 := by
      refine Polynomial.funext fun t ↦ ?_
      rw [heval, Polynomial.eval_zero, map_mul]
      have hdetx : eval (fun ij ↦ (1 + t • Y) ij.1 ij.2) (g1_varMatrix k n).det =
          (1 + t • Y).det := by
        rw [RingHom.map_det]
        congr 1
        ext i j
        simp [g1_varMatrix]
      by_cases hdet : (1 + t • Y).det = 0
      · rw [hdetx, hdet, mul_zero]
      · let g : Matrix.GeneralLinearGroup (Fin n) k :=
          Matrix.nonsingInvUnit _ (isUnit_iff_ne_zero.mpr hdet)
        have hgx : g1_coords g = fun ij ↦ (1 + t • Y) ij.1 ij.2 := by
          funext ij
          rfl
        have hg : g ∈ (g1_centralizerGroup S).carrier := by
          rw [g1_centralizerGroup_carrier, Subgroup.mem_centralizer_iff]
          intro s hs
          ext1
          change (s : Matrix (Fin n) (Fin n) k) * (1 + t • Y) =
            (1 + t • Y) * (s : Matrix (Fin n) (Fin n) k)
          rw [mul_add, add_mul, mul_one, one_mul, Matrix.mul_smul, Matrix.smul_mul,
            hY _ ⟨s, hs, rfl⟩]
        have := g1_mem_vanishingIdealSet_iff.mp hf g hg
        rw [hgx] at this
        rw [this, zero_mul]
    have h1 : L (f * (g1_varMatrix k n).det) = 0 := by
      rw [hL, hzero]
      simp
    rw [hLeib, g1_mem_vanishingIdealSet_iff.mp hf 1 (g1_centralizerGroup S).carrier.one_mem,
      g1_eval_one_det, zero_mul, zero_add, one_mul, hLf] at h1
    exact h1

end HodgeLean.Foundations
