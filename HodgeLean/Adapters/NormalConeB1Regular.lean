import HodgeLean.Adapters.NormalConeB1Special
import HodgeLean.Adapters.NormalConeB1Relations
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Regular-sequence coordinates for the normal cone -/

noncomputable section
namespace HodgeLean.Adapters

theorem a3b1_coneMonomial_add
    (R : Type*) [CommRing R] (I : Ideal R) (n : ℕ)
    (a b : ↑(I ^ n)) :
    a3b1_coneMonomial R I n (a + b) =
      a3b1_coneMonomial R I n a + a3b1_coneMonomial R I n b := by
  unfold a3b1_coneMonomial
  rw [← map_add]
  congr 1
  apply Subtype.ext
  exact map_add (Polynomial.monomial n) a.1 b.1

theorem a3b1_coneMonomial_mul
    (R : Type*) [CommRing R] (I : Ideal R) (m n : ℕ)
    (a : ↑(I ^ m)) (b : ↑(I ^ n)) :
    a3b1_coneMonomial R I m a * a3b1_coneMonomial R I n b =
      a3b1_coneMonomial R I (m + n)
        ⟨a.1 * b.1, by
          rw [pow_add]
          exact Ideal.mul_mem_mul a.2 b.2⟩ := by
  apply Ideal.Quotient.eq.mpr
  convert Ideal.zero_mem _ using 1
  apply SetCoe.ext
  simp [a3b1_coneMonomial, Polynomial.monomial_mul_monomial]

theorem a3b1_coneMonomial_one_pow
    (R : Type*) [CommRing R] (I : Ideal R) (a : ↑I) (n : ℕ) :
    a3b1_coneMonomial R I 1 ⟨a.1, by simpa⟩ ^ n =
      a3b1_coneMonomial R I n
        ⟨a.1 ^ n, Ideal.pow_mem_pow a.2 n⟩ := by
  induction n with
  | zero =>
      apply Ideal.Quotient.eq.mpr
      convert Ideal.zero_mem _ using 1
      apply SetCoe.ext
      simp [a3b1_coneMonomial]
  | succ n ih =>
      rw [pow_succ, ih]
      simpa [pow_succ] using
        (a3b1_coneMonomial_mul R I n 1
          ⟨a.1 ^ n, Ideal.pow_mem_pow a.2 n⟩ ⟨a.1, by simpa⟩)

def a3b1_regularSequence_normalConeMap
    (R : Type*) [CommRing R] (rs : List R) :
    MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs) →ₐ[R ⧸ Ideal.ofList rs]
      a3cc3_normalConeRing (Ideal.ofList rs) :=
  MvPolynomial.aeval fun j ↦
    a3b1_coneMonomial R (Ideal.ofList rs) 1
      ⟨rs.get j, by
        rw [pow_one]
        exact Ideal.subset_span (List.get_mem rs j)⟩

@[simp] theorem a3b1_regularSequence_normalConeMap_X
    (R : Type*) [CommRing R] (rs : List R) (j : Fin rs.length) :
    a3b1_regularSequence_normalConeMap R rs (MvPolynomial.X j) =
      a3b1_coneMonomial R (Ideal.ofList rs) 1
        ⟨rs.get j, by
          rw [pow_one]
          exact Ideal.subset_span (List.get_mem rs j)⟩ := by
  simp [a3b1_regularSequence_normalConeMap]

theorem a3b1_coneMonomial_zero_degree
    (R : Type*) [CommRing R] (I : Ideal R) (a : ↑(I ^ 0)) :
    a3b1_coneMonomial R I 0 a = algebraMap R (a3cc3_normalConeRing I) a.1 := by
  rfl

theorem a3b1_coneMonomial_mem_range
    (R : Type*) [CommRing R] (rs : List R) (n : ℕ)
    (a : ↑((Ideal.ofList rs) ^ n)) :
    a3b1_coneMonomial R (Ideal.ofList rs) n a ∈
      (a3b1_regularSequence_normalConeMap R rs).range := by
  let f := a3b1_regularSequence_normalConeMap R rs
  have hzero (m : ℕ) : a3b1_coneMonomial R (Ideal.ofList rs) m 0 = 0 := by
    have h : (⟨Polynomial.monomial m 0, by simp⟩ :
        reesAlgebra (Ideal.ofList rs)) = 0 := by ext; simp
    change Ideal.Quotient.mk _ (⟨Polynomial.monomial m 0, _⟩ :
      reesAlgebra (Ideal.ofList rs)) = 0
    rw [h, map_zero]
  have hscalar (b : ↑((Ideal.ofList rs) ^ 0)) :
      a3b1_coneMonomial R (Ideal.ofList rs) 0 b ∈ f.range := by
    rw [a3b1_coneMonomial_zero_degree]
    rw [IsScalarTower.algebraMap_apply R (R ⧸ Ideal.ofList rs)
      (a3cc3_normalConeRing (Ideal.ofList rs))]
    exact f.range.algebraMap_mem _
  have hone (b : ↑((Ideal.ofList rs) ^ 1)) :
      a3b1_coneMonomial R (Ideal.ofList rs) 1 b ∈ f.range := by
    suffices h : ∀ (x : R) (hx : x ∈ Ideal.ofList rs),
        a3b1_coneMonomial R (Ideal.ofList rs) 1 ⟨x, by simpa using hx⟩ ∈ f.range by
      exact h b.1 (by simpa using b.2)
    intro b hb
    change b ∈ Submodule.span R {x | x ∈ rs} at hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
        obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hb
        exact ⟨MvPolynomial.X j, a3b1_regularSequence_normalConeMap_X R rs j⟩
    | zero =>
        change a3b1_coneMonomial R (Ideal.ofList rs) 1 0 ∈ f.range
        rw [hzero]
        exact f.range.zero_mem
    | add x y hx hy ihx ihy =>
        rw [show (⟨x + y, _⟩ : ↑((Ideal.ofList rs) ^ 1)) =
          ⟨x, by simpa using hx⟩ + ⟨y, by simpa using hy⟩ from rfl,
          a3b1_coneMonomial_add]
        exact f.range.add_mem ihx ihy
    | smul r x hx ih =>
        have h := f.range.mul_mem (hscalar ⟨r, by simp⟩) ih
        rw [a3b1_coneMonomial_mul] at h
        exact h
  induction n with
  | zero => exact hscalar a
  | succ n ih =>
      obtain ⟨a, ha⟩ := a
      rw [pow_succ] at ha
      induction ha using Submodule.mul_induction_on' with
      | mem_mul_mem x hx y hy =>
          have h := f.range.mul_mem (ih ⟨x, hx⟩) (hone ⟨y, by simpa using hy⟩)
          rw [a3b1_coneMonomial_mul] at h
          exact h
      | add x hx y hy ihx ihy =>
          rw [show (⟨x + y, _⟩ : ↑((Ideal.ofList rs) ^ (n + 1))) =
            ⟨x, by simpa [pow_succ] using hx⟩ +
              ⟨y, by simpa [pow_succ] using hy⟩ from rfl,
            a3b1_coneMonomial_add]
          exact f.range.add_mem (ihx _) (ihy _)

theorem a3b1_regularSequence_normalConeMap_surjective
    (R : Type*) [CommRing R] (rs : List R) :
    Function.Surjective (a3b1_regularSequence_normalConeMap R rs) := by
  intro y
  refine Quotient.inductionOn y ?_
  intro p
  change Ideal.Quotient.mk _ p ∈ (a3b1_regularSequence_normalConeMap R rs).range
  rw [reesAlgebra.as_sum_support p, map_sum]
  apply Subalgebra.sum_mem
  intro n hn
  exact a3b1_coneMonomial_mem_range R rs n
    ⟨p.1.coeff n, (mem_reesAlgebra_iff _ _).mp p.2 n⟩

def a3b1_reesCoordinateMap
    (R : Type*) [CommRing R] (rs : List R) :
    MvPolynomial (Fin rs.length) R →ₐ[R] reesAlgebra (Ideal.ofList rs) :=
  MvPolynomial.aeval fun j ↦
    ⟨Polynomial.monomial 1 (rs.get j), reesAlgebra.monomial_mem.mpr (by
      rw [pow_one]
      exact Ideal.subset_span (List.get_mem rs j))⟩

theorem a3b1_reesCoordinateMap_monomial
    (R : Type*) [CommRing R] (rs : List R)
    (d : Fin rs.length →₀ ℕ) (r : R) :
    (a3b1_reesCoordinateMap R rs (MvPolynomial.monomial d r) : Polynomial R) =
      Polynomial.monomial d.degree ((MvPolynomial.monomial d r).eval rs.get) := by
  classical
  unfold a3b1_reesCoordinateMap
  simp only [MvPolynomial.aeval_monomial, Subalgebra.coe_mul,
    Subalgebra.coe_pow, Subalgebra.coe_algebraMap, Polynomial.algebraMap_apply,
    MvPolynomial.eval_monomial]
  simp only [Finsupp.prod, SubmonoidClass.coe_finset_prod, Subalgebra.coe_pow,
    Algebra.algebraMap_self, RingHom.id_apply,
    ← Polynomial.C_mul_X_pow_eq_monomial, pow_one, mul_pow,
    one_mul, Finset.prod_mul_distrib, ← map_pow, ← map_prod, ← map_mul,
    Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply, mul_assoc]
  rw [← mul_assoc, ← map_mul]

theorem a3b1_reesCoordinateMap_coeff
    (R : Type*) [CommRing R] (rs : List R)
    (p : MvPolynomial (Fin rs.length) R) (n : ℕ) :
    (a3b1_reesCoordinateMap R rs p : Polynomial R).coeff n =
      (MvPolynomial.homogeneousComponent n p).eval rs.get := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d r =>
      rw [a3b1_reesCoordinateMap_monomial, Polynomial.coeff_monomial,
        MvPolynomial.homogeneousComponent_of_mem
          (MvPolynomial.isHomogeneous_monomial r (show d.degree = d.degree from rfl))]
      by_cases h : d.degree = n
      · simp [h]
      · simp [h, Ne.symm h]
  | add p q hp hq =>
      simp only [map_add, Subalgebra.coe_add, Polynomial.coeff_add, hp, hq]

theorem a3b1_reesCoordinateMap_quotient
    (R : Type*) [CommRing R] (rs : List R)
    (p : MvPolynomial (Fin rs.length) R) :
    Ideal.Quotient.mk _ (a3b1_reesCoordinateMap R rs p) =
      a3b1_regularSequence_normalConeMap R rs
        (MvPolynomial.map (Ideal.Quotient.mk (Ideal.ofList rs)) p) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      simp only [a3b1_reesCoordinateMap, MvPolynomial.aeval_C,
        MvPolynomial.map_C, a3b1_regularSequence_normalConeMap]
      rfl
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
      simp only [map_mul, hp, MvPolynomial.map_X,
        a3b1_regularSequence_normalConeMap_X]
      congr 1
      simp only [a3b1_reesCoordinateMap, MvPolynomial.aeval_X, a3b1_coneMonomial]

theorem a3b1_zero_eval_fin_zero
    (R : Type*) [CommRing R] (p : MvPolynomial (Fin 0) R)
    (h : p.eval (fun i : Fin 0 ↦ i.elim0) = 0) : p = 0 := by
  apply ((MvPolynomial.aeval_injective_iff_of_isEmpty (R := R)).mpr
    (fun _ _ hxy ↦ hxy))
  simpa [MvPolynomial.aeval_def] using h

theorem a3b1_ofList_eq_span_range_get
    (R : Type*) [CommRing R] (rs : List R) :
    Ideal.ofList rs = Ideal.span (Set.range rs.get) := by
  rw [Ideal.ofList, Set.range_list_get]

theorem a3b1_mem_ofList_pow_iff_exists_homogeneous
    (R : Type*) [CommRing R] (rs : List R) (n : ℕ) (y : R) :
    y ∈ (Ideal.ofList rs) ^ n ↔
      ∃ p : MvPolynomial (Fin rs.length) R,
        p.IsHomogeneous n ∧ p.eval rs.get = y := by
  rw [a3b1_ofList_eq_span_range_get]
  exact Ideal.mem_span_pow_iff_exists_isHomogeneous rs.get y

theorem a3b1_eval_monomial_mem_ofList_pow
    (R : Type*) [CommRing R] (rs : List R)
    (d : Fin rs.length →₀ ℕ) (r : R) :
    (MvPolynomial.monomial d r).eval rs.get ∈
      (Ideal.ofList rs) ^ d.degree := by
  apply (a3b1_mem_ofList_pow_iff_exists_homogeneous R rs d.degree _).mpr
  exact ⟨MvPolynomial.monomial d r,
    MvPolynomial.isHomogeneous_monomial r rfl, rfl⟩

theorem a3b1_mem_succ_pow_has_ideal_coefficient_expression
    (R : Type*) [CommRing R] (rs : List R) (n : ℕ) (y : R)
    (hy : y ∈ (Ideal.ofList rs) ^ (n + 1)) :
    ∃ p : MvPolynomial (Fin rs.length) R,
      p.IsHomogeneous n ∧ p.eval rs.get = y ∧
        ∀ d, p.coeff d ∈ Ideal.ofList rs := by
  rw [pow_succ'] at hy
  induction hy using Submodule.mul_induction_on' with
  | mem_mul_mem a ha b hb =>
      obtain ⟨p, hp, rfl⟩ :=
        (a3b1_mem_ofList_pow_iff_exists_homogeneous R rs n b).mp hb
      refine ⟨MvPolynomial.C a * p, hp.C_mul a, ?_, ?_⟩
      · simp
      · intro d
        rw [MvPolynomial.coeff_C_mul]
        exact (Ideal.ofList rs).mul_mem_right _ ha
  | add x hx y hy hx' hy' =>
      obtain ⟨p, hp, hp_eval, hp_coeff⟩ := hx'
      obtain ⟨q, hq, hq_eval, hq_coeff⟩ := hy'
      refine ⟨p + q, hp.add hq, ?_, ?_⟩
      · simp [hp_eval, hq_eval]
      · intro d
        rw [MvPolynomial.coeff_add]
        exact (Ideal.ofList rs).add_mem (hp_coeff d) (hq_coeff d)

/-- A homogeneous relation on a regular sequence has coefficients in its generated ideal.
Source: Stacks Project, Lemma 10.69.2 (tag 061M). -/
theorem a3b1_regularSequence_zero_eval_coeff_mem
    (R : Type*) [CommRing R] (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs)
    (n : ℕ) (p : MvPolynomial (Fin rs.length) R)
    (hp : p.IsHomogeneous n) (heval : p.eval rs.get = 0) :
    ∀ d, p.coeff d ∈ Ideal.ofList rs := by
  have hreg' : RingTheory.Sequence.IsWeaklyRegular R
      (List.ofFn (fun i : Fin rs.length ↦ rs.get i.rev)).reverse := by
    rw [a3b1_reverse_ofFn_get_rev]
    exact hreg.toIsWeaklyRegular
  have h := a3b1_reverse_regular_homogeneous_coeff_mem rs.length
    (fun i : Fin rs.length ↦ rs.get i.rev) hreg' n
    (MvPolynomial.rename Fin.rev p) hp.rename_isHomogeneous (by
      have he : (MvPolynomial.rename Fin.rev p).eval
          (fun i : Fin rs.length ↦ rs.get i.rev) = 0 := by
        simpa only [MvPolynomial.eval_rename, Function.comp_def, Fin.rev_rev] using heval
      rw [he]
      exact Ideal.zero_mem _)
  intro d
  have hd := h (d.mapDomain Fin.rev)
  rw [MvPolynomial.coeff_rename_mapDomain Fin.rev Fin.rev_injective] at hd
  rw [a3b1_span_range_eq_ofList_reverse, a3b1_reverse_ofFn_get_rev] at hd
  exact hd

/-- Homogeneous relations among a regular sequence gain one further factor from its ideal.
Source: Stacks Project, Lemma 10.69.2 (tag 061M). -/
theorem a3b1_regularSequence_homogeneous_coeff_mem
    (R : Type*) [CommRing R] (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs)
    (n : ℕ) (p : MvPolynomial (Fin rs.length) R)
    (hp : p.IsHomogeneous n)
    (heval : p.eval rs.get ∈ (Ideal.ofList rs) ^ (n + 1)) :
    ∀ d, p.coeff d ∈ Ideal.ofList rs := by
  obtain ⟨q, hq, hq_eval, hq_coeff⟩ :=
    a3b1_mem_succ_pow_has_ideal_coefficient_expression R rs n _ heval
  have hrel : (p - q).eval rs.get = 0 := by
    rw [map_sub, hq_eval, sub_eq_zero]
  have hcoeff := a3b1_regularSequence_zero_eval_coeff_mem R rs hreg n
    (p - q) (hp.sub hq) hrel
  intro d
  have hsum := (Ideal.ofList rs).add_mem (hcoeff d) (hq_coeff d)
  simpa only [MvPolynomial.coeff_sub, sub_add_cancel] using hsum

theorem a3b1_regularSequence_normalConeMap_bijective
    (R : Type*) [CommRing R] (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) :
    Function.Bijective (a3b1_regularSequence_normalConeMap R rs) := by
  refine ⟨?_, a3b1_regularSequence_normalConeMap_surjective R rs⟩
  rw [injective_iff_map_eq_zero]
  intro p hp
  obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective
    (Ideal.Quotient.mk (Ideal.ofList rs)) Ideal.Quotient.mk_surjective p
  rw [← a3b1_reesCoordinateMap_quotient, Ideal.Quotient.eq_zero_iff_mem,
    mem_map_algebraMap_reesAlgebra_iff] at hp
  ext d
  rw [MvPolynomial.coeff_map]
  change Ideal.Quotient.mk (Ideal.ofList rs) (q.coeff d) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have h := a3b1_regularSequence_homogeneous_coeff_mem R rs hreg d.degree
    (MvPolynomial.homogeneousComponent d.degree q)
    (MvPolynomial.homogeneousComponent_isHomogeneous _ _) (by
      rw [← a3b1_reesCoordinateMap_coeff]
      exact hp d.degree) d
  simpa [MvPolynomial.coeff_homogeneousComponent] using h

end HodgeLean.Adapters
