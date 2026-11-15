import HodgeLean.Foundations.MatrixAlgGroupLieCartier
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.ClosedPointDimension
import HodgeConjecture.Mathlib.Algebra.PolynomialCatenary

/-! # Smoothness of matrix algebraic groups in characteristic zero

`g1_finrank_lie_eq_krullDim`: for a matrix algebraic group `G` over a field of characteristic
zero, the Lie algebra `𝔤` (the Zariski tangent space at `1`, cut out by the differentials of the
vanishing ideal `I(G)`) has dimension equal to the Krull dimension of `k[x_ij] ⧸ I(G)`. The
route is commutative algebra only; it uses neither generic smoothness nor group schemes.

* `dim k[x] ⧸ I(G) ≤ dim 𝔤` (any field). Every minimal prime `P` of the radical ideal `I(G)`
  vanishes at a point `g ∈ G` (the other minimal primes supply `s ∉ P` with `P s ⊆ I(G)`).
  Translating by `g⁻¹` moves `P` to a prime through `1` with an isomorphic quotient. At `1`, the
  maximal ideal is generated modulo its square and `I(G)` by `dim 𝔤` affine-linear polynomials
  (first-order Taylor expansion and `T_1 = (m/m²)^*`); Nakayama makes `m` minimal over them,
  Krull's height theorem bounds its height by `dim 𝔤`, and a maximal ideal of a finite-type
  domain has height equal to the dimension.
* `dim 𝔤 ≤ dim k[x] ⧸ I(G)` (characteristic zero). The left-invariant derivations `D_X`
  (`g1_leftDeriv`, `X` in a basis of `𝔤`) preserve `I(G)`, hence each of its minimal primes; take
  one, `P`, through `1`. For affine-linear `y_j` dual to the basis, `det(D_i y_j)` is `1` at `1`,
  so not in `P`, and a polynomial relation among the `y_j` modulo `P` of least degree would have
  all partial derivatives in the relation ideal, so it is constant (characteristic zero) and zero.
  Noether normalization turns `dim 𝔤` algebraically independent elements into a lower bound for
  the Krull dimension of `k[x] ⧸ P`.

Sources: Borel, *Linear Algebraic Groups*, 2nd ed., §3.6, AG.10.1 and AG.16.2; Humphreys,
*Linear Algebraic Groups*, §5.5; Cartier's theorem (Demazure–Gabriel, II.6.1.1); Matsumura,
*Commutative Ring Theory*, Theorems 5.6 and 13.5.
-/

noncomputable section
set_option maxHeartbeats 400000

namespace HodgeLean.Foundations

open MvPolynomial Matrix HodgeLean.Foundations.Program

universe u

variable {k : Type*} [Field k]

/-! ## Commutative algebra -/

/-- The chain rule for a derivation applied to a polynomial expression.
Source: Kaplansky, *An Introduction to Differential Algebra*, §1 (derivations of polynomial
rings). -/
theorem g1s_derivation_aeval {R : Type*} [CommRing R] [Algebra k R] {ι : Type*} [Fintype ι]
    (D : Derivation k R R) (y : ι → R) (F : MvPolynomial ι k) :
    D (aeval y F) = ∑ j, aeval y (pderiv j F) * D (y j) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    have h1 : ∀ j, aeval y (pderiv j (p * X i)) =
        aeval y p * (if j = i then 1 else 0) + y i * aeval y (pderiv j p) := by
      intro j
      rw [Derivation.leibniz, pderiv_X]
      by_cases h : j = i
      · subst h; simp [mul_comm]
      · simp [h, mul_comm]
    rw [map_mul, aeval_X, Derivation.leibniz, hp]
    simp only [h1, add_mul, Finset.sum_add_distrib, smul_eq_mul, mul_ite, mul_one, mul_zero,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.mul_sum]
    simp only [mul_assoc]

/-- A partial derivative lowers the total degree by one.
Source: the formula for the coefficients of a partial derivative. -/
theorem g1s_totalDegree_pderiv_le {ι : Type*} (j : ι) (F : MvPolynomial ι k) :
    (pderiv j F).totalDegree ≤ F.totalDegree - 1 := by
  classical
  refine Finset.sup_le fun m hm ↦ ?_
  rw [mem_support_iff, coeff_pderiv] at hm
  have hmF : m + Finsupp.single j 1 ∈ F.support :=
    mem_support_iff.mpr (left_ne_zero_of_mul hm)
  have h := le_totalDegree hmF
  rw [Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl), Finsupp.sum_single_index rfl] at h
  omega

/-- In characteristic zero, a polynomial whose partial derivatives all vanish is constant.
Source: the formula for the coefficients of a partial derivative. -/
theorem g1s_eq_C_of_pderiv_eq_zero [CharZero k] {ι : Type*} (F : MvPolynomial ι k)
    (h : ∀ j, pderiv j F = 0) : F = C (F.coeff 0) := by
  classical
  ext m
  rw [coeff_C]
  split_ifs with hm
  · rw [hm]
  · obtain ⟨j, hj⟩ : ∃ j, m j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hm (Finsupp.ext fun j ↦ by simpa using (hcon j).symm)
    have hle : Finsupp.single j 1 ≤ m := by
      rw [Finsupp.single_le_iff]
      omega
    have hc := coeff_pderiv (i := j) F (m - Finsupp.single j 1)
    rw [h j, AddMonoidAlgebra.coeff_zero, tsub_add_cancel_of_le hle] at hc
    have hne : (((m - Finsupp.single j (1 : ℕ)) j : ℕ) : k) + 1 ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero ((m - Finsupp.single j (1 : ℕ)) j)
    exact ((mul_eq_zero.mp hc.symm).resolve_right hne)

/-- **Algebraic independence from derivations.** In characteristic zero, if derivations
`D_1, …, D_d` preserve a prime `P` and the matrix `(D_i y_j)` has determinant outside `P`, then
`y_1, …, y_d` are algebraically independent modulo `P`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.15 (separating transcendence bases and
derivations); Cartier's argument (Demazure–Gabriel, II.6.1.1). -/
theorem g1s_eq_zero_of_aeval_mem [CharZero k] {R : Type*} [CommRing R] [Algebra k R] {d : ℕ}
    (P : Ideal R) [hP : P.IsPrime] (D : Fin d → Derivation k R R)
    (hD : ∀ i, ∀ x ∈ P, D i x ∈ P) (y : Fin d → R)
    (hdet : (Matrix.of fun i j ↦ D i (y j)).det ∉ P) (F : MvPolynomial (Fin d) k)
    (hF : aeval y F ∈ P) : F = 0 := by
  have key : ∀ F : MvPolynomial (Fin d) k, aeval y F ∈ P →
      ∀ j, aeval y (pderiv j F) ∈ P := by
    intro F hF
    let mk := Ideal.Quotient.mk P
    have hv : (mk.mapMatrix (Matrix.of fun i j ↦ D i (y j))) *ᵥ
        (fun j ↦ mk (aeval y (pderiv j F))) = 0 := by
      funext i
      simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.of_apply, Pi.zero_apply, ← map_mul, ← map_sum]
      rw [Ideal.Quotient.eq_zero_iff_mem]
      have h := hD i _ hF
      rw [g1s_derivation_aeval] at h
      simpa only [mul_comm] using h
    have hdet' : (mk.mapMatrix (Matrix.of fun i j ↦ D i (y j))).det ≠ 0 := by
      rw [← RingHom.map_det]
      exact fun h ↦ hdet (Ideal.Quotient.eq_zero_iff_mem.mp h)
    intro j
    have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet' hv) j
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  have hconst : ∀ c : k, aeval y (C c : MvPolynomial (Fin d) k) ∈ P → c = 0 := by
    intro c hc
    by_contra hc0
    rw [aeval_C] at hc
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hc ((Units.mk0 c hc0).isUnit.map _))
  suffices H : ∀ N, ∀ F : MvPolynomial (Fin d) k,
      F.totalDegree ≤ N → aeval y F ∈ P → F = 0 from
    H _ F le_rfl hF
  intro N
  induction N with
  | zero =>
    intro F hdeg hF
    have hF0 := totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hdeg)
    rw [hF0] at hF ⊢
    rw [hconst _ hF, C_0]
  | succ N ih =>
    intro F hdeg hF
    have hder : ∀ j, pderiv j F = 0 := fun j ↦
      ih _ ((g1s_totalDegree_pderiv_le j F).trans (by omega)) (key F hF j)
    have hF0 := g1s_eq_C_of_pderiv_eq_zero F hder
    rw [hF0] at hF ⊢
    rw [hconst _ hF, C_0]

/-- A finitely generated domain over a field containing `d` algebraically independent elements
has Krull dimension at least `d` (Noether normalization and the transcendence degree).
Source: Matsumura, *Commutative Ring Theory*, Theorem 5.6; Borel, *Linear Algebraic Groups*,
2nd ed., AG.10.1. -/
theorem g1s_le_ringKrullDim_of_algebraicIndependent {K B : Type u} [Field K] [CommRing B]
    [IsDomain B] [Algebra K B] [Algebra.FiniteType K B] {d : ℕ} {y : Fin d → B}
    (hy : AlgebraicIndependent K y) : (d : WithBot ℕ∞) ≤ ringKrullDim B := by
  obtain ⟨s, g, hg, hfinite⟩ := exists_finite_inj_algHom_of_fg K B
  let : Algebra (MvPolynomial (Fin s) K) B := g.toAlgebra
  have : IsScalarTower K (MvPolynomial (Fin s) K) B :=
    IsScalarTower.of_algebraMap_eq (fun c ↦ (g.commutes c).symm)
  have : FaithfulSMul (MvPolynomial (Fin s) K) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  have : Algebra.IsIntegral (MvPolynomial (Fin s) K) B := ⟨hfinite.to_isIntegral⟩
  have hdim : ringKrullDim B = s := by
    rw [PolynomialCatenary.ringKrullDim_eq_of_isIntegral_of_injective hg,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      ENat.card_eq_coe_fintype_card, Fintype.card_fin]
    simp
  have htr : Algebra.trdeg K B = s := by
    have h := trdeg_add_eq K (MvPolynomial (Fin s) K) (A := B)
    rw [trdeg_eq_zero (R := MvPolynomial (Fin s) K) (A := B), add_zero,
      MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin, Cardinal.lift_natCast] at h
    exact h.symm
  have h := hy.lift_cardinalMk_le_trdeg
  rw [Cardinal.mk_fin, Cardinal.lift_natCast, Cardinal.lift_uzero, htr] at h
  have hds : d ≤ s := by exact_mod_cast h
  rw [hdim]
  exact_mod_cast hds

/-- A minimal prime `P` of a radical ideal `J` in a Noetherian ring is a colon ideal: some
`s ∉ P` has `P · s ⊆ J` (take `s` in the other minimal primes).
Source: Matsumura, *Commutative Ring Theory*, §6 (primary decomposition of a radical ideal). -/
theorem g1s_exists_mul_mem_of_mem_minimalPrimes {R : Type*} [CommRing R] [IsNoetherianRing R]
    {J P : Ideal R} (hJ : J.IsRadical) (hP : P ∈ J.minimalPrimes) :
    ∃ s ∉ P, ∀ f ∈ P, f * s ∈ J := by
  classical
  have hPp : P.IsPrime := hP.1.1
  set S := (J.finite_minimalPrimes_of_isNoetherianRing).toFinset.erase P
  have hnot : ¬ S.inf id ≤ P := by
    intro h
    obtain ⟨Q, hQ, hQP⟩ := hPp.inf_le'.mp h
    rw [Finset.mem_erase, Set.Finite.mem_toFinset] at hQ
    exact hQ.1 (le_antisymm hQP (hP.2 hQ.2.1 hQP))
  obtain ⟨s, hsS, hsP⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  refine ⟨s, hsP, fun f hf ↦ ?_⟩
  rw [← hJ.radical, ← Ideal.sInf_minimalPrimes]
  refine Submodule.mem_sInf.mpr fun Q hQ ↦ ?_
  by_cases hQP : Q = P
  · subst hQP
    exact Ideal.mul_mem_right _ _ hf
  · have hmem : Q ∈ S := by
      rw [Finset.mem_erase, Set.Finite.mem_toFinset]
      exact ⟨hQP, hQ⟩
    have hle : S.inf id ≤ Q := Finset.inf_le (f := id) hmem
    exact Ideal.mul_mem_left _ _ (hle hsS)

/-- A derivation preserving a radical ideal of a Noetherian ring preserves each of its minimal
primes.
Source: Kaplansky, *An Introduction to Differential Algebra*, Lemma 1.15; Seidenberg,
*Differential ideals in rings of finitely generated type*, Amer. J. Math. 89 (1967). -/
theorem g1s_derivation_mem_of_mem_minimalPrimes {R : Type*} [CommRing R] [Algebra k R]
    [IsNoetherianRing R] {J P : Ideal R} (hJ : J.IsRadical) (hP : P ∈ J.minimalPrimes)
    (D : Derivation k R R) (hD : ∀ x ∈ J, D x ∈ J) : ∀ x ∈ P, D x ∈ P := by
  obtain ⟨s, hsP, hs⟩ := g1s_exists_mul_mem_of_mem_minimalPrimes hJ hP
  have hPp : P.IsPrime := hP.1.1
  intro x hx
  have h1 := hD _ (hs x hx)
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1
  have h3 : s * (x * D s) ∈ J := by
    have := J.mul_mem_right (D s) (hs x hx)
    convert this using 1
    ring
  have h2 : s * (s * D x) ∈ J := by
    have := J.mul_mem_left s h1
    rw [mul_add] at this
    exact (J.add_mem_iff_right h3).mp this
  rcases hPp.mem_or_mem (hP.1.2 h2) with h | h
  · exact absurd h hsP
  rcases hPp.mem_or_mem h with h | h
  · exact absurd h hsP
  · exact h

/-- **Krull's height theorem at a point.** If a maximal ideal `m ⊇ P` is generated modulo `m²`
and `P` by `d` elements, then the domain `R ⧸ P` (of finite type over a field) has Krull
dimension at most `d`: by Nakayama `m ⧸ P` is minimal over those `d` elements, so it has height
at most `d`, and every maximal ideal of a finite-type domain has height equal to its dimension.
Source: Matsumura, *Commutative Ring Theory*, Theorem 13.5 and Theorem 5.6; Borel, *Linear
Algebraic Groups*, 2nd ed., AG.16.2. -/
theorem g1s_ringKrullDim_quotient_le_of_gen {R : Type*} [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] [IsNoetherianRing R] (P m : Ideal R) [P.IsPrime] [hm : m.IsMaximal]
    (hPm : P ≤ m) {d : ℕ} (ℓ : Fin d → R) (hℓ : ∀ i, ℓ i ∈ m)
    (hgen : m ≤ Ideal.span (Set.range ℓ) ⊔ m ^ 2 ⊔ P) : ringKrullDim (R ⧸ P) ≤ d := by
  classical
  set K' := Ideal.span (Set.range ℓ) ⊔ P with hK'
  obtain ⟨r, hr1, hr⟩ : ∃ r : R, r - 1 ∈ m ∧ ∀ x ∈ m, r * x ∈ K' := by
    let N : Submodule R (R ⧸ K') := Submodule.map K'.mkQ m
    have hN : N.FG := (IsNoetherian.noetherian m).map _
    have hle : N ≤ m • N := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ K' ⊔ m ^ 2 := by
        have := hgen hx
        rwa [sup_right_comm] at this
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx'
      rw [map_add, Submodule.mkQ_apply K' a, (Submodule.Quotient.mk_eq_zero K').mpr ha, zero_add]
      have hb' : b ∈ m • m := by rwa [pow_two] at hb
      have : K'.mkQ b ∈ Submodule.map K'.mkQ (m • m) := ⟨b, hb', rfl⟩
      rwa [Submodule.map_smul''] at this
    obtain ⟨r, hr1, hr⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m N hN hle
    refine ⟨r, hr1, fun x hx ↦ ?_⟩
    have := hr _ ⟨x, hx, rfl⟩
    rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    exact this
  have hrm : r ∉ m := fun h ↦ hm.ne_top ((Ideal.eq_top_iff_one _).mpr (by
    simpa using m.sub_mem h hr1))
  have : Algebra.FiniteType k (R ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k P)
      (Ideal.Quotient.mkₐ_surjective k P)
  set M := m.map (Ideal.Quotient.mk P) with hM
  have hcomap : M.comap (Ideal.Quotient.mk P) = m := Ideal.comap_map_mk hPm
  have hMmax : M.IsMaximal := by
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      hm).resolve_left fun h ↦ hm.ne_top ?_
    rw [← hcomap, hM, h, Ideal.comap_top]
  set S : Finset (R ⧸ P) := Finset.univ.image fun i ↦ Ideal.Quotient.mk P (ℓ i)
  have hmin : M ∈ (Ideal.span (S : Set (R ⧸ P))).minimalPrimes := by
    refine ⟨⟨hMmax.isPrime, ?_⟩, fun Q hQ hQM ↦ ?_⟩
    · rw [Ideal.span_le]
      intro z hz
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      exact Ideal.mem_map_of_mem _ (hℓ i)
    · have := hQ.1
      set Q' := Q.comap (Ideal.Quotient.mk P)
      have hQ'm : Q' ≤ m := hcomap ▸ Ideal.comap_mono hQM
      have hK'Q : K' ≤ Q' := by
        refine sup_le ?_ ?_
        · rw [Ideal.span_le]
          rintro _ ⟨i, rfl⟩
          exact hQ.2 (Ideal.subset_span (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
        · intro x hx
          change Ideal.Quotient.mk P x ∈ Q
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
          exact Q.zero_mem
      have hmQ' : m ≤ Q' := fun x hx ↦
        ((Ideal.IsPrime.comap (Ideal.Quotient.mk P) (K := Q)).mem_or_mem
          (hK'Q (hr x hx))).resolve_left fun h ↦ hrm (hQ'm h)
      rw [hM, Ideal.map_le_iff_le_comap]
      exact hmQ'
  have hht := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
  have hcard : S.card ≤ d := Finset.card_image_le.trans (by simp)
  rw [← Algebra.FiniteType.height_eq_ringKrullDim_of_isMaximal (k := k) M]
  have : M.height ≤ d := hht.trans (by exact_mod_cast hcard)
  exact_mod_cast this

/-- The Krull dimension of `R ⧸ J` is at most a bound satisfied by every `R ⧸ P` with `P` a
minimal prime of `J`: every chain of primes over `J` starts above a minimal prime.
Source: Matsumura, *Commutative Ring Theory*, §5 (the dimension of a ring is attained over its
minimal primes). -/
theorem g1s_ringKrullDim_quotient_le_of_minimalPrimes {R : Type*} [CommRing R] (J : Ideal R)
    (d : WithBot ℕ∞) (h : ∀ P ∈ J.minimalPrimes, ringKrullDim (R ⧸ P) ≤ d) :
    ringKrullDim (R ⧸ J) ≤ d := by
  rw [ringKrullDim_quotient, Order.krullDim]
  refine iSup_le fun l ↦ ?_
  have hhead : J ≤ l.head.1.asIdeal := by
    have := l.head.2
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] at this
    exact this
  obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le hhead
  have := hP.1.1
  let l' : LTSeries (PrimeSpectrum.zeroLocus (R := R) P) :=
    ⟨l.length, fun i ↦ ⟨(l i).1, by
      rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
      exact hPle.trans (l.monotone (Fin.zero_le i))⟩, fun i ↦ l.step i⟩
  have := Order.LTSeries.length_le_krullDim l'
  rw [← ringKrullDim_quotient] at this
  exact this.trans (h P hP)

/-! ## Matrix coordinates at the identity -/

variable {n : ℕ}

/-- The maximal ideal of the identity matrix in `k[x_ij]`: polynomials vanishing at `1`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.1.1 and AG.16.1. -/
def g1s_maxIdealOne (k : Type*) [Field k] (n : ℕ) : Ideal (MvPolynomial (Fin n × Fin n) k) :=
  RingHom.ker (eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k)))

example : (X ((0 : Fin 1), (0 : Fin 1)) - 1 : MvPolynomial (Fin 1 × Fin 1) k) ∈
    g1s_maxIdealOne k 1 := by
  simp [g1s_maxIdealOne, g1_coords]

/-- Membership in the maximal ideal of `1`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.1.1. -/
theorem g1s_mem_maxIdealOne {f : MvPolynomial (Fin n × Fin n) k} :
    f ∈ g1s_maxIdealOne k n ↔
      eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k)) f = 0 :=
  RingHom.mem_ker

/-- The ideal of `1` is maximal.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.1.1. -/
theorem g1s_maxIdealOne_isMaximal : (g1s_maxIdealOne k n).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun a ↦ ⟨C a, eval_C a⟩

/-- The vanishing ideal of a group lies in the ideal of `1`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.1.1. -/
theorem g1s_vanishingIdeal_le_maxIdealOne (G : MatrixAlgGroup k n) :
    g1_vanishingIdeal G ≤ g1s_maxIdealOne k n := fun _ hf ↦
  g1s_mem_maxIdealOne.mpr (g1_mem_vanishingIdealSet_iff.mp hf 1 G.carrier.one_mem)

/-- The vanishing ideal of a group is radical.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.1.1. -/
theorem g1s_vanishingIdeal_isRadical (G : MatrixAlgGroup k n) :
    (g1_vanishingIdeal G).IsRadical := by
  rintro f ⟨m, hm⟩
  refine g1_mem_vanishingIdealSet_iff.mpr fun g hg ↦ ?_
  have := g1_mem_vanishingIdealSet_iff.mp hm g hg
  rw [map_pow] at this
  exact IsNilpotent.eq_zero ⟨m, this⟩

/-- A linear form on matrices is determined by its values on the matrix units.
Source: linear algebra (the basis of matrix units). -/
theorem g1s_apply_eq_sum_single (φ : Matrix (Fin n) (Fin n) k →ₗ[k] k)
    (Y : Matrix (Fin n) (Fin n) k) :
    φ Y = ∑ ab : Fin n × Fin n, φ (Matrix.single ab.1 ab.2 1) * Y ab.1 ab.2 := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
  simp only [map_sum]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [show Matrix.single i j (Y i j) = Y i j • Matrix.single i j (1 : k) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul, mul_comm]

/-- The differential at `1` evaluated at a matrix unit is a partial derivative at `1`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.16.1. -/
theorem g1s_differential_single (f : MvPolynomial (Fin n × Fin n) k) (a b : Fin n) :
    g1_differential f (Matrix.single a b 1) =
      eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k)) (pderiv (a, b) f) := by
  classical
  rw [g1_differential_apply, Finset.sum_eq_single (a, b)]
  · simp
  · rintro ⟨i, j⟩ _ hij
    rw [Matrix.single_apply_of_ne, mul_zero]
    rintro ⟨rfl, rfl⟩
    exact hij rfl
  · simp

/-- The affine-linear polynomial `Σ φ(E_ab) (x_ab - δ_ab)` attached to a linear form `φ`; it
vanishes at `1` and its differential at `1` is `φ`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.16.1. -/
def g1s_linPoly (φ : Matrix (Fin n) (Fin n) k →ₗ[k] k) : MvPolynomial (Fin n × Fin n) k :=
  ∑ ab : Fin n × Fin n, C (φ (Matrix.single ab.1 ab.2 1)) *
    (X ab - C (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k) ab))

example (φ : Matrix (Fin n) (Fin n) k →ₗ[k] k) : g1s_linPoly φ = ∑ ab : Fin n × Fin n,
    C (φ (Matrix.single ab.1 ab.2 1)) *
      (X ab - C (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k) ab)) := rfl

/-- `g1s_linPoly φ` vanishes at `1`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.16.1. -/
theorem g1s_linPoly_mem_maxIdealOne (φ : Matrix (Fin n) (Fin n) k →ₗ[k] k) :
    g1s_linPoly φ ∈ g1s_maxIdealOne k n := by
  simp [g1s_mem_maxIdealOne, g1s_linPoly]

/-- The differential at `1` of `g1s_linPoly φ` is `φ`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.16.1. -/
theorem g1s_differential_linPoly (φ : Matrix (Fin n) (Fin n) k →ₗ[k] k)
    (Y : Matrix (Fin n) (Fin n) k) : g1_differential (g1s_linPoly φ) Y = φ Y := by
  rw [g1s_apply_eq_sum_single φ Y, ← g1_diffAt_apply, g1s_linPoly, map_sum]
  refine Finset.sum_congr rfl fun ab _ ↦ ?_
  rw [g1_diffAt_apply, g1_differential_C_mul, ← g1_diffAt_apply, map_sub, g1_diffAt_apply,
    g1_diffAt_apply, g1_differential_X, g1_differential_C, sub_zero]

/-- **First-order Taylor expansion at `1`.** A polynomial minus its value and its linear part at
`1` lies in the square of the maximal ideal of `1`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.16.1 (`m/m²` and differentials). -/
theorem g1s_sub_linear_mem_sq (f : MvPolynomial (Fin n × Fin n) k) :
    f - C (eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k)) f) -
      ∑ ab : Fin n × Fin n,
        C (eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k)) (pderiv ab f)) *
          (X ab - C (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k) ab)) ∈
      g1s_maxIdealOne k n ^ 2 := by
  classical
  set e1 := g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k)
  set e : Fin n × Fin n → MvPolynomial (Fin n × Fin n) k := fun ab ↦ X ab - C (e1 ab)
    with he_def
  have he : ∀ ab, e ab ∈ g1s_maxIdealOne k n := fun ab ↦ by
    simp [g1s_mem_maxIdealOne, he_def, e1]
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    convert add_mem hp hq using 1
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    ring
  | mul_X p c hp =>
    set Lp := ∑ ab, C (eval e1 (pderiv ab p)) * e ab with hLp_def
    have hLp : Lp ∈ g1s_maxIdealOne k n := Ideal.sum_mem _ fun ab _ ↦
      Ideal.mul_mem_left _ _ (he ab)
    have hd : ∀ ab, eval e1 (pderiv ab (p * X c)) =
        eval e1 p * (if ab = c then 1 else 0) + e1 c * eval e1 (pderiv ab p) := by
      intro ab
      rw [Derivation.leibniz, pderiv_X]
      by_cases h : ab = c
      · subst h; simp [mul_comm]
      · simp [h, Ne.symm h, mul_comm]
    have hsum : ∑ ab, C (eval e1 (pderiv ab (p * X c))) * e ab =
        C (e1 c) * Lp + C (eval e1 p) * e c := by
      simp only [hd, map_add, map_mul, add_mul, Finset.sum_add_distrib, hLp_def, Finset.mul_sum,
        mul_ite, mul_one, mul_zero, apply_ite C, C_0, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_assoc]
      ring
    have key : p * X c - C (eval e1 (p * X c)) - ∑ ab, C (eval e1 (pderiv ab (p * X c))) * e ab
        = Lp * e c + (p - C (eval e1 p) - Lp) * X c := by
      rw [hsum, map_mul, eval_X, C_mul]
      simp only [he_def]
      ring
    rw [key]
    refine add_mem ?_ (Ideal.mul_mem_right _ _ hp)
    rw [pow_two]
    exact Ideal.mul_mem_mul hLp (he c)

/-- A polynomial vanishing at `1` with zero differential at `1` lies in the square of the maximal
ideal of `1`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.16.1. -/
theorem g1s_mem_sq_of_differential_eq_zero {f : MvPolynomial (Fin n × Fin n) k}
    (h0 : f ∈ g1s_maxIdealOne k n) (hd : g1_differential f = 0) :
    f ∈ g1s_maxIdealOne k n ^ 2 := by
  have h := g1s_sub_linear_mem_sq f
  have hpd : ∀ ab : Fin n × Fin n,
      eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k)) (pderiv ab f) = 0 := by
    rintro ⟨a, b⟩
    rw [← g1s_differential_single, hd, LinearMap.zero_apply]
  simpa [hpd, g1s_mem_maxIdealOne.mp h0] using h

/-- The differential at `1`, as a `k`-linear map from polynomials to linear forms on matrices.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.16.1. -/
def g1s_diffLin (k : Type*) [Field k] (n : ℕ) :
    MvPolynomial (Fin n × Fin n) k →ₗ[k] Module.Dual k (Matrix (Fin n) (Fin n) k) where
  toFun f := g1_differential f
  map_add' f g := by
    ext Y
    exact map_add (g1_diffAt Y) f g
  map_smul' c f := by
    ext Y
    exact map_smul (g1_diffAt Y) c f

example (f : MvPolynomial (Fin n × Fin n) k) : g1s_diffLin k n f = g1_differential f := rfl

/-- The Lie algebra is the common kernel of the differentials of the vanishing ideal.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.16.2. -/
theorem g1s_lieAlgebra_eq_dualCoannihilator (G : MatrixAlgGroup k n) :
    g1_lieAlgebra G =
      (((g1_vanishingIdeal G).restrictScalars k).map (g1s_diffLin k n)).dualCoannihilator := by
  ext Y
  rw [Submodule.mem_dualCoannihilator]
  change Y ∈ g1_lieOfSet _ ↔ _
  rw [g1_mem_lieOfSet_iff]
  constructor
  · rintro h _ ⟨f, hf, rfl⟩
    exact h f hf
  · intro h f hf
    exact h _ ⟨f, hf, rfl⟩

/-- **Cotangent generators at `1`.** The maximal ideal of `1` is generated, modulo its square and
the vanishing ideal of `G`, by `dim 𝔤` affine-linear polynomials vanishing at `1`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.16.1 and AG.16.2 (`T_e = (m/m²)^*`). -/
theorem g1s_exists_gen (G : MatrixAlgGroup k n) :
    ∃ ℓ : Fin (Module.finrank k (g1_lieAlgebra G)) → MvPolynomial (Fin n × Fin n) k,
      (∀ i, ℓ i ∈ g1s_maxIdealOne k n) ∧
      g1s_maxIdealOne k n ≤
        Ideal.span (Set.range ℓ) ⊔ g1s_maxIdealOne k n ^ 2 ⊔ g1_vanishingIdeal G := by
  classical
  set W := ((g1_vanishingIdeal G).restrictScalars k).map (g1s_diffLin k n) with hW
  obtain ⟨U, hWU⟩ := Submodule.exists_isCompl W
  have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq W
  have h2 := Submodule.finrank_add_eq_of_isCompl hWU
  have h3 := Subspace.dual_finrank_eq (K := k) (V := Matrix (Fin n) (Fin n) k)
  have hU : Module.finrank k U = Module.finrank k (g1_lieAlgebra G) := by
    rw [g1s_lieAlgebra_eq_dualCoannihilator, ← hW]
    omega
  let bU := Module.finBasisOfFinrankEq k U hU
  refine ⟨fun i ↦ g1s_linPoly (bU i : Module.Dual k (Matrix (Fin n) (Fin n) k)),
    fun i ↦ g1s_linPoly_mem_maxIdealOne _, fun f hf ↦ ?_⟩
  have hδ : g1s_diffLin k n f ∈ W ⊔ U := by
    rw [hWU.sup_eq_top]
    trivial
  obtain ⟨w, hw, u, hu, hwu⟩ := Submodule.mem_sup.mp hδ
  obtain ⟨h, hh, rfl⟩ := hw
  have hh' : h ∈ g1_vanishingIdeal G := hh
  set c := bU.repr ⟨u, hu⟩
  have husum : u = ∑ i, c i • (bU i : Module.Dual k (Matrix (Fin n) (Fin n) k)) := by
    conv_lhs => rw [show u = ((⟨u, hu⟩ : U) : Module.Dual k (Matrix (Fin n) (Fin n) k))
      from rfl,
      ← bU.sum_repr ⟨u, hu⟩]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rfl
  set L := ∑ i, c i • g1s_linPoly (bU i : Module.Dual k (Matrix (Fin n) (Fin n) k))
  have hL : L ∈ Ideal.span (Set.range fun i ↦
      g1s_linPoly (bU i : Module.Dual k (Matrix (Fin n) (Fin n) k))) :=
    Submodule.sum_mem _ fun i _ ↦ Submodule.smul_of_tower_mem _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have hδL : g1s_diffLin k n L = u := by
    rw [husum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul]
    congr 1
    ext Y
    exact g1s_differential_linPoly _ Y
  have hq : f - h - L ∈ g1s_maxIdealOne k n ^ 2 := by
    refine g1s_mem_sq_of_differential_eq_zero ?_ ?_
    · refine Ideal.sub_mem _ (Ideal.sub_mem _ hf (g1s_vanishingIdeal_le_maxIdealOne G hh')) ?_
      exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_of_tower_mem _ _
        (g1s_linPoly_mem_maxIdealOne _)
    · have : g1s_diffLin k n (f - h - L) = 0 := by
        rw [map_sub, map_sub, ← hwu, hδL]
        abel
      exact this
  have hf' : f = L + (f - h - L) + h := by ring
  rw [hf']
  exact add_mem (add_mem (Ideal.mem_sup_left (Ideal.mem_sup_left hL))
    (Ideal.mem_sup_left (Ideal.mem_sup_right hq))) (Ideal.mem_sup_right hh')

/-! ## Translations and the points of minimal primes -/

/-- Every minimal prime of the vanishing ideal of `G` vanishes at some point of `G`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.1.2 and AG.2.1 (irreducible components
of the closure of `G` meet `G`). -/
theorem g1s_exists_point_of_mem_minimalPrimes (G : MatrixAlgGroup k n)
    {P : Ideal (MvPolynomial (Fin n × Fin n) k)} (hP : P ∈ (g1_vanishingIdeal G).minimalPrimes) :
    ∃ g ∈ G.carrier, ∀ f ∈ P, eval (g1_coords g) f = 0 := by
  obtain ⟨s, hsP, hs⟩ :=
    g1s_exists_mul_mem_of_mem_minimalPrimes (g1s_vanishingIdeal_isRadical G) hP
  by_contra hcon
  push Not at hcon
  refine hsP (hP.1.2 (g1_mem_vanishingIdealSet_iff.mpr fun g hg ↦ ?_))
  obtain ⟨f, hfP, hfg⟩ := hcon g hg
  have := g1_mem_vanishingIdealSet_iff.mp (hs f hfP) g hg
  rw [map_mul] at this
  exact (mul_eq_zero.mp this).resolve_left hfg

/-- Left translation `f ↦ f(a x)` as an algebra endomorphism of `k[x_ij]`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.9 (translations `λ_a`). -/
def g1s_translate (a : Matrix.GeneralLinearGroup (Fin n) k) :
    MvPolynomial (Fin n × Fin n) k →ₐ[k] MvPolynomial (Fin n × Fin n) k :=
  bind₁ fun ij ↦ ∑ l, C ((a : Matrix (Fin n) (Fin n) k) ij.1 l) * X (l, ij.2)

example (a : Matrix.GeneralLinearGroup (Fin n) k) (f : MvPolynomial (Fin n × Fin n) k) :
    g1s_translate a f = g1_leftTranslate a f := rfl

/-- Evaluating a translate.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.9. -/
theorem g1s_eval_translate (a h : Matrix.GeneralLinearGroup (Fin n) k)
    (f : MvPolynomial (Fin n × Fin n) k) :
    eval (g1_coords h) (g1s_translate a f) = eval (g1_coords (a * h)) f :=
  g1_eval_leftTranslate a h f

/-- Composition of translations: `λ_a ∘ λ_b = λ_{b a}`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.9. -/
theorem g1s_translate_translate (a b : Matrix.GeneralLinearGroup (Fin n) k)
    (f : MvPolynomial (Fin n × Fin n) k) :
    g1s_translate a (g1s_translate b f) = g1s_translate (b * a) f := by
  rw [← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun ij ↦ ?_
  simp only [AlgHom.comp_apply, g1s_translate, bind₁_X_right, map_sum, map_mul, bind₁_C_right,
    Units.val_mul, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun m _ ↦ ?_
  rw [mul_assoc]

/-- Translation by `1` is the identity.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.9. -/
theorem g1s_translate_one (f : MvPolynomial (Fin n × Fin n) k) : g1s_translate 1 f = f := by
  classical
  have : g1s_translate (1 : Matrix.GeneralLinearGroup (Fin n) k) = AlgHom.id k _ := by
    refine MvPolynomial.algHom_ext fun ij ↦ ?_
    rw [g1s_translate, bind₁_X_right, AlgHom.id_apply, Finset.sum_eq_single ij.1]
    · simp
    · intro l _ hl
      simp [Ne.symm hl]
    · simp
  rw [this, AlgHom.id_apply]

/-- Translation by an element of `G` preserves the vanishing ideal of `G`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.9. -/
theorem g1s_translate_mem_vanishingIdeal (G : MatrixAlgGroup k n)
    {a : Matrix.GeneralLinearGroup (Fin n) k} (ha : a ∈ G.carrier)
    {f : MvPolynomial (Fin n × Fin n) k} (hf : f ∈ g1_vanishingIdeal G) :
    g1s_translate a f ∈ g1_vanishingIdeal G := by
  refine g1_mem_vanishingIdealSet_iff.mpr fun h hh ↦ ?_
  rw [g1s_eval_translate]
  exact g1_mem_vanishingIdealSet_iff.mp hf _ (G.carrier.mul_mem ha hh)

/-! ## The two inequalities -/

/-- **`dim G ≤ dim 𝔤`** (any field): every component of the closure of `G` is translated to one
through `1`, where Krull's height theorem bounds its dimension by the number of cotangent
generators.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.10.1 and AG.16.2; Matsumura,
*Commutative Ring Theory*, Theorem 13.5. -/
theorem g1s_ringKrullDim_le_finrank (G : MatrixAlgGroup k n) :
    ringKrullDim (MvPolynomial (Fin n × Fin n) k ⧸ g1_vanishingIdeal G) ≤
      Module.finrank k (g1_lieAlgebra G) := by
  have := g1s_maxIdealOne_isMaximal (k := k) (n := n)
  obtain ⟨ℓ, hℓ, hgen⟩ := g1s_exists_gen G
  refine g1s_ringKrullDim_quotient_le_of_minimalPrimes _ _ fun P hP ↦ ?_
  have := hP.1.1
  obtain ⟨g, hg, hPg⟩ := g1s_exists_point_of_mem_minimalPrimes G hP
  let ψ : MvPolynomial (Fin n × Fin n) k →+* MvPolynomial (Fin n × Fin n) k ⧸ P :=
    (Ideal.Quotient.mk P).comp (g1s_translate g⁻¹).toRingHom
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨g1s_translate g f, ?_⟩
    simp only [ψ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      g1s_translate_translate, mul_inv_cancel, g1s_translate_one]
  have hmem : ∀ f, f ∈ RingHom.ker ψ ↔ g1s_translate g⁻¹ f ∈ P := fun f ↦ by
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem
  have : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have hJP : g1_vanishingIdeal G ≤ RingHom.ker ψ := fun f hf ↦
    (hmem f).mpr (hP.1.2 (g1s_translate_mem_vanishingIdeal G (G.carrier.inv_mem hg) hf))
  have hP1 : RingHom.ker ψ ≤ g1s_maxIdealOne k n := fun f hf ↦ by
    have := hPg _ ((hmem f).mp hf)
    rw [g1s_eval_translate, inv_mul_cancel] at this
    exact g1s_mem_maxIdealOne.mpr this
  rw [ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hψ).symm]
  exact g1s_ringKrullDim_quotient_le_of_gen (k := k) _ _ hP1 ℓ hℓ
    (hgen.trans (sup_le_sup_left hJP _))

/-- **`dim 𝔤 ≤ dim G`** in characteristic zero: the left-invariant derivations of a basis of `𝔤`
preserve a minimal prime through `1`, and make `dim 𝔤` affine-linear coordinates algebraically
independent on that component.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §3.6 and AG.16.2; Cartier's theorem
(Demazure–Gabriel, *Groupes algébriques*, II.6.1.1). -/
theorem g1s_finrank_le_ringKrullDim [CharZero k] (G : MatrixAlgGroup k n) :
    (Module.finrank k (g1_lieAlgebra G) : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin n × Fin n) k ⧸ g1_vanishingIdeal G) := by
  classical
  have := g1s_maxIdealOne_isMaximal (k := k) (n := n)
  set e1 := g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k)
  obtain ⟨P, hP, hP1⟩ := Ideal.exists_minimalPrimes_le (g1s_vanishingIdeal_le_maxIdealOne G)
  have := hP.1.1
  set d := Module.finrank k (g1_lieAlgebra G)
  let bL := Module.finBasisOfFinrankEq k (g1_lieAlgebra G) (rfl : d = d)
  have hext : ∀ j, ∃ φ : Matrix (Fin n) (Fin n) k →ₗ[k] k,
      φ.comp (g1_lieAlgebra G).subtype = bL.coord j := fun j ↦ LinearMap.exists_extend _
  choose φ hφ using hext
  let D : Fin d →
      Derivation k (MvPolynomial (Fin n × Fin n) k) (MvPolynomial (Fin n × Fin n) k) :=
    fun i ↦ g1_leftDeriv (bL i : Matrix (Fin n) (Fin n) k)
  let y : Fin d → MvPolynomial (Fin n × Fin n) k := fun j ↦ g1s_linPoly (φ j)
  have hDP : ∀ i, ∀ x ∈ P, D i x ∈ P := fun i ↦
    g1s_derivation_mem_of_mem_minimalPrimes (g1s_vanishingIdeal_isRadical G) hP _
      (fun x hx ↦ g1_leftDeriv_mem_vanishingIdeal G (bL i).2 hx)
  have hval : ∀ i j, eval e1 (D i (y j)) = if i = j then 1 else 0 := by
    intro i j
    have h := LinearMap.congr_fun (hφ j) (bL i)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply] at h
    simp only [D, y, e1, g1_eval_one_leftDeriv, g1s_differential_linPoly, h]
  have hdet : (Matrix.of fun i j ↦ D i (y j)).det ∉ P := by
    intro h
    have h1 := g1s_mem_maxIdealOne.mp (hP1 h)
    rw [RingHom.map_det] at h1
    have hM : (eval e1).mapMatrix (Matrix.of fun i j ↦ D i (y j)) = 1 := by
      ext i j
      simp [hval, Matrix.one_apply, e1]
    rw [hM, Matrix.det_one] at h1
    exact one_ne_zero h1
  have hind : AlgebraicIndependent k (fun j ↦ Ideal.Quotient.mkₐ k P (y j)) := by
    refine (injective_iff_map_eq_zero _).mpr fun F hF ↦
      g1s_eq_zero_of_aeval_mem P D hDP y hdet F ?_
    rw [← MvPolynomial.comp_aeval_apply, Ideal.Quotient.mkₐ_eq_mk] at hF
    exact Ideal.Quotient.eq_zero_iff_mem.mp hF
  have : Algebra.FiniteType k (MvPolynomial (Fin n × Fin n) k ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k P)
      (Ideal.Quotient.mkₐ_surjective k P)
  exact (g1s_le_ringKrullDim_of_algebraicIndependent hind).trans
    (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hP.1.2)
      (Ideal.Quotient.factor_surjective hP.1.2))

/-! ## Smoothness -/

/-- **Matrix algebraic groups are smooth in characteristic zero.** The Lie algebra (the Zariski
tangent space at `1`) has dimension equal to the Krull dimension of the coordinate ring
`k[x_ij] ⧸ I(G)`. The `[IsAlgClosed k]` binder is kept from the frozen form of the statement;
the two inequalities `g1s_finrank_le_ringKrullDim` and `g1s_ringKrullDim_le_finrank` do not use it.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §3.6 and AG.16.2; Humphreys, *Linear
Algebraic Groups*, §5.5; Cartier's theorem (Demazure–Gabriel, *Groupes algébriques*,
II.6.1.1). -/
theorem g1_finrank_lie_eq_krullDim [IsAlgClosed k] [CharZero k] (G : MatrixAlgGroup k n) :
    (Module.finrank k (g1_lieAlgebra G) : WithBot ℕ∞) =
      ringKrullDim (MvPolynomial (Fin n × Fin n) k ⧸ g1_vanishingIdeal G) :=
  le_antisymm (g1s_finrank_le_ringKrullDim G) (g1s_ringKrullDim_le_finrank G)

end HodgeLean.Foundations
