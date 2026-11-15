import HodgeLean.Foundations.CMCentreInvariantsDefs
import HodgeLean.Foundations.MultiBlockInvariants

/-! # Proofs for the centre-invariants spec (stage A4)

The agent's working file. Fill every proof hole. **Do not change the statement of any `_aux`
theorem**: `CMCentreInvariants.lean` (frozen) restates each one and must still typecheck.
Helper lemmas may be added freely, in this file or in new files; prefix them `a4_`.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] HodgeLean.Foundations.SchurWeyl.dualAddCommGroup
open scoped TensorProduct
namespace HodgeLean.Foundations
open InvariantsExterior SchurWeyl Module

section AnyField

variable {K : Type*} [Field K]

theorem a4_add_pow_succ_of_sq_eq_zero {A : Type*} [Ring A] {a b : A} (hc : Commute a b)
    (hb : b * b = 0) (n : ℕ) : (a + b) ^ (n + 1) = a ^ (n + 1) + (n + 1) • (a ^ n * b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, add_mul, mul_add, mul_add, smul_mul_assoc, smul_mul_assoc,
      mul_assoc (a ^ n) b b, hb, mul_zero, smul_zero, add_zero, mul_assoc (a ^ n) b a, ← hc.eq,
      ← mul_assoc, ← pow_succ, ← pow_succ, succ_nsmul _ (n + 1)]
    abel

theorem a4_sum_pow_of_sq_eq_zero {A : Type*} [Ring A] :
    ∀ (n : ℕ) (p : Fin n → A), (∀ i j, Commute (p i) (p j)) → (∀ i, p i * p i = 0) →
      (∑ i, p i) ^ n = n.factorial • (List.ofFn p).prod ∧ (∑ i, p i) ^ (n + 1) = 0
  | 0, p, _, _ => by simp
  | n + 1, p, hc, hsq => by
    obtain ⟨ih1, ih2⟩ := a4_sum_pow_of_sq_eq_zero n (fun i => p i.castSucc)
      (fun i j => hc _ _) (fun i => hsq _)
    have hcomm : Commute (∑ i : Fin n, p i.castSucc) (p (Fin.last n)) :=
      Commute.sum_left _ _ _ fun i _ => hc _ _
    rw [Fin.sum_univ_castSucc, List.ofFn_succ', List.prod_concat]
    refine ⟨?_, ?_⟩
    · rw [a4_add_pow_succ_of_sq_eq_zero hcomm (hsq _), ih2, ih1, zero_add, smul_mul_assoc,
        smul_smul, Nat.factorial_succ]
    · rw [a4_add_pow_succ_of_sq_eq_zero hcomm (hsq _), pow_succ, ih2, zero_mul, zero_add]
      simp

theorem a4_prod_mul_anticomm {A : Type*} [Ring A] :
    ∀ (n : ℕ) (y : Fin n → A) (z : A), (∀ i, y i * z = -(z * y i)) →
      (List.ofFn y).prod * z = (-1) ^ n * (z * (List.ofFn y).prod)
  | 0, y, z, _ => by simp
  | n + 1, y, z, h => by
    rw [List.ofFn_succ', List.prod_concat, mul_assoc, h, mul_neg, ← mul_assoc,
      a4_prod_mul_anticomm n _ z fun i => h _]
    simp only [pow_succ, mul_assoc, neg_mul, mul_neg, mul_one]

theorem a4_half_succ (n : ℕ) : (n + 1) * n / 2 = n * (n - 1) / 2 + n := by
  have : (n + 1) * n = n * (n - 1) + n * 2 := by
    cases n with
    | zero => rfl
    | succ n => simp only [Nat.add_sub_cancel]; ring
  rw [this, Nat.add_mul_div_right _ _ (by norm_num)]

theorem a4_prod_pairs {A : Type*} [Ring A] :
    ∀ (n : ℕ) (x y : Fin n → A), (∀ i j, y i * x j = -(x j * y i)) →
      (List.ofFn fun i => x i * y i).prod =
        (-1) ^ (n * (n - 1) / 2) * ((List.ofFn x).prod * (List.ofFn y).prod)
  | 0, x, y, _ => by simp
  | n + 1, x, y, h => by
    rw [List.ofFn_succ', List.prod_concat,
      a4_prod_pairs n (fun i => x i.castSucc) (fun i => y i.castSucc) fun i j => h _ _,
      List.ofFn_succ' x, List.ofFn_succ' y, List.prod_concat, List.prod_concat]
    have key := a4_prod_mul_anticomm n (fun i => y i.castSucc) (x (Fin.last n)) fun i => h _ _
    simp only [Nat.add_sub_cancel, a4_half_succ, pow_add]
    calc (-1) ^ (n * (n - 1) / 2) * ((List.ofFn fun i => x i.castSucc).prod *
            (List.ofFn fun i => y i.castSucc).prod) * (x (Fin.last n) * y (Fin.last n))
        = (-1) ^ (n * (n - 1) / 2) * ((List.ofFn fun i => x i.castSucc).prod *
            ((List.ofFn fun i => y i.castSucc).prod * x (Fin.last n)) * y (Fin.last n)) := by
          simp only [mul_assoc]
      _ = _ := by
          rw [key]
          simp only [mul_assoc, ((Commute.neg_one_left _).pow_left n).eq]

variable {W U U' : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup U] [Module K U] [AddCommGroup U'] [Module K U']

theorem a4_ι_anticomm {M : Type*} [AddCommGroup M] [Module K M] (u v : M) :
    ExteriorAlgebra.ι K u * ExteriorAlgebra.ι K v = -(ExteriorAlgebra.ι K v * ExteriorAlgebra.ι K u) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap u v)

theorem a4_coe_wedgePair {M : Type*} [AddCommGroup M] [Module K M] (u v : M) :
    ((exteriorPower.ιMulti K 2 ![u, v] : ⋀[K]^2 M) : ExteriorAlgebra K M) =
      ExteriorAlgebra.ι K u * ExteriorAlgebra.ι K v := by
  simp [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]

theorem spec_a4_theta_pow_aux (a : U) (a' : U') :
    ((theta (K := K) (W := W) a a' : ExteriorAlgebra K (Space K W U U'))) ^ finrank K W =
      ((-1 : K) ^ (finrank K W * (finrank K W - 1) / 2) * ((finrank K W).factorial : K)) •
        ((detW (K := K) (W := W) (U' := U') a : ExteriorAlgebra K (Space K W U U')) *
          (detWDual (K := K) (W := W) (U := U) a' : ExteriorAlgebra K (Space K W U U'))) := by
  set b := Module.finBasis K W
  set x : Fin (finrank K W) → ExteriorAlgebra K (Space K W U U') :=
    fun i => ExteriorAlgebra.ι K (vectorIn (U' := U') a (b i))
  set y : Fin (finrank K W) → ExteriorAlgebra K (Space K W U U') :=
    fun i => ExteriorAlgebra.ι K (dualIn (U := U) a' (b.dualBasis i))
  have hθ : ((theta (K := K) (W := W) a a' : ExteriorAlgebra K (Space K W U U'))) =
      ∑ i, x i * y i := by
    rw [theta_eq_sum b, Submodule.coe_sum]
    simp only [wedgePair_apply, a4_coe_wedgePair, x, y]
  have hx : ((detW (K := K) (W := W) (U' := U') a : ExteriorAlgebra K (Space K W U U'))) =
      (List.ofFn x).prod := by
    rw [detW_eq, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]
    rfl
  have hy : ((detWDual (K := K) (W := W) (U := U) a' : ExteriorAlgebra K (Space K W U U'))) =
      (List.ofFn y).prod := by
    rw [detWDual_eq, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]
    rfl
  have hyx : ∀ i j, y i * x j = -(x j * y i) := fun i j => a4_ι_anticomm _ _
  have hmem : ∀ i, x i * y i ∈ ⋀[K]^2 (Space K W U U') := by
    intro i
    rw [← a4_coe_wedgePair]
    exact Submodule.coe_mem _
  have hc : ∀ i j, Commute (x i * y i) (x j * y j) := by
    intro i j
    have := a3b_mul_anticomm (hmem i) (hmem j)
    rw [show ((-1 : ℤˣ) ^ (2 * 2)) = 1 by decide, one_smul] at this
    exact this
  have hsq : ∀ i, x i * y i * (x i * y i) = 0 := by
    intro i
    rw [mul_assoc, ← mul_assoc (y i), hyx, neg_mul, mul_neg, neg_eq_zero, ← mul_assoc,
      ← mul_assoc, show x i * x i = 0 from ExteriorAlgebra.ι_sq_zero _, zero_mul, zero_mul]
  rw [hθ, (a4_sum_pow_of_sq_eq_zero _ _ hc hsq).1, a4_prod_pairs _ x y hyx, hx, hy, mul_smul,
    Nat.cast_smul_eq_nsmul K, Algebra.smul_def ((-1 : K) ^ _), map_pow, map_neg, map_one,
    mul_smul_comm]

theorem a4_ιMulti_ne_zero {M : Type*} [AddCommGroup M] [Module K M] {n : ℕ} {u : Fin n → M}
    (hu : LinearIndependent K u) : exteriorPower.ιMulti K n u ≠ 0 := by
  intro h0
  have hli := exteriorPower.ιMulti_family_linearIndependent_field (n := n) hu
  let s : Set.powersetCard (Fin n) n := ⟨Finset.univ, by simp [Set.powersetCard]⟩
  apply hli.ne_zero s
  let e := (Set.powersetCard.ofFinEmbEquiv (I := Fin n) (n := n)).symm s
  let σ : Equiv.Perm (Fin n) :=
    Equiv.ofBijective e (Finite.injective_iff_bijective.mp e.injective)
  change exteriorPower.ιMulti K n (u ∘ σ) = 0
  rw [AlternatingMap.map_perm, h0, smul_zero]

theorem a4_vectorIn_linearIndependent :
    LinearIndependent K (Fin.append
      (fun i => ((Module.finBasis K W i ⊗ₜ[K] (1 : K), 0) : Space K W K K))
      (fun i => ((0, (Module.finBasis K W).dualBasis i ⊗ₜ[K] (1 : K)) : Space K W K K))) := by
  rw [← linearIndependent_equiv finSumFinEquiv]
  have : (Fin.append
      (fun i => ((Module.finBasis K W i ⊗ₜ[K] (1 : K), 0) : Space K W K K))
      (fun i => ((0, (Module.finBasis K W).dualBasis i ⊗ₜ[K] (1 : K)) : Space K W K K))) ∘
        finSumFinEquiv =
      Sum.elim (LinearMap.inl K _ _ ∘ fun i => (TensorProduct.rid K W).symm (Module.finBasis K W i))
        (LinearMap.inr K _ _ ∘ fun i =>
          (TensorProduct.rid K (Module.Dual K W)).symm ((Module.finBasis K W).dualBasis i)) := by
    ext (i | j) <;> simp [-Fin.natAdd_eq_addNat]
  rw [this]
  exact linearIndependent_inl_union_inr'
    ((Module.finBasis K W).linearIndependent.map' _ (TensorProduct.rid K W).symm.ker)
    ((Module.finBasis K W).dualBasis.linearIndependent.map' _
      (TensorProduct.rid K (Module.Dual K W)).symm.ker)

theorem a4_detW_mul_detWDual_ne_zero :
    (detW (K := K) (W := W) (U' := K) (1 : K) : ExteriorAlgebra K (Space K W K K)) *
      (detWDual (K := K) (W := W) (U := K) (1 : K) : ExteriorAlgebra K (Space K W K K)) ≠ 0 := by
  rw [← a3b_coe_wedge, detW_eq, detWDual_eq, wedge_ιMulti, ne_eq, ZeroMemClass.coe_eq_zero]
  exact a4_ιMulti_ne_zero a4_vectorIn_linearIndependent

end AnyField

theorem spec_a4_theta_sq_charTwo_aux :
    ((theta (K := ZMod 2) (W := Fin 2 → ZMod 2) (U := ZMod 2) (U' := ZMod 2) 1 1 :
        ExteriorAlgebra (ZMod 2) (Space (ZMod 2) (Fin 2 → ZMod 2) (ZMod 2) (ZMod 2)))) ^ 2 = 0 ∧
      (detW (K := ZMod 2) (W := Fin 2 → ZMod 2) (U' := ZMod 2) (1 : ZMod 2) :
          ExteriorAlgebra (ZMod 2) (Space (ZMod 2) (Fin 2 → ZMod 2) (ZMod 2) (ZMod 2))) *
        (detWDual (K := ZMod 2) (W := Fin 2 → ZMod 2) (U := ZMod 2) (1 : ZMod 2) :
          ExteriorAlgebra (ZMod 2) (Space (ZMod 2) (Fin 2 → ZMod 2) (ZMod 2) (ZMod 2))) ≠ 0 := by
  refine ⟨?_, a4_detW_mul_detWDual_ne_zero⟩
  have h2 : finrank (ZMod 2) (Fin 2 → ZMod 2) = 2 := Module.finrank_fin_fun _
  have hp : ((theta (K := ZMod 2) (W := Fin 2 → ZMod 2) (U := ZMod 2) (U' := ZMod 2) 1 1 :
        ExteriorAlgebra (ZMod 2) (Space (ZMod 2) (Fin 2 → ZMod 2) (ZMod 2) (ZMod 2)))) ^ 2 =
      ((theta (K := ZMod 2) (W := Fin 2 → ZMod 2) (U := ZMod 2) (U' := ZMod 2) 1 1 :
        ExteriorAlgebra (ZMod 2) (Space (ZMod 2) (Fin 2 → ZMod 2) (ZMod 2) (ZMod 2)))) ^
          finrank (ZMod 2) (Fin 2 → ZMod 2) := by rw [h2]
  rw [hp, spec_a4_theta_pow_aux]
  have h0 : ((-1 : ZMod 2) ^ (finrank (ZMod 2) (Fin 2 → ZMod 2) *
      (finrank (ZMod 2) (Fin 2 → ZMod 2) - 1) / 2) *
        ((finrank (ZMod 2) (Fin 2 → ZMod 2)).factorial : ZMod 2)) = 0 := by
    rw [h2]; decide
  rw [h0, zero_smul]

variable {K : Type*} [Field K] [CharZero K]

section OneBlock

variable {W U U' : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup U] [Module K U] [AddCommGroup U'] [Module K U']

theorem spec_a4_exteriorDer_counted_aux {k α β : ℕ} {g : ⋀[K]^k (Space K W U U')}
    (hg : CountedGeneratorProduct k α β g) (f : Module.End K W) :
    exteriorDer k (multiplicityLie K W U U' f) g =
      (((α : K) - β) * LinearMap.trace K W f) • g := by
  induction hg with
  | unit => simp [exteriorDer_ιMulti]
  | theta a a' => simpa [lie_eq_exteriorDer] using lie_theta f a a'
  | detW a => simpa [lie_eq_exteriorDer] using lie_detW f a
  | detWDual a' => simpa [lie_eq_exteriorDer] using lie_detWDual f a'
  | wedge hv hw ihv ihw =>
    rw [exteriorDer_wedge, ihv, ihw, map_smul, LinearMap.smul_apply, map_smul, ← add_smul]
    congr 1
    push_cast
    ring

/-- The ordered product of the contractions `θ(p.1, p.2)`, `p ∈ l`, in the exterior algebra.
Source: PW v0.3, Lemma 4.1(c) (products of contractions); a proof device for S7. -/
private def a4ThetaProd (l : List (U × U')) : ExteriorAlgebra K (Space K W U U') :=
  (l.map fun p => (theta (K := K) (W := W) p.1 p.2 : ExteriorAlgebra K (Space K W U U'))).prod

example : a4ThetaProd (K := K) (W := W) ([] : List (U × U')) = 1 := rfl

/-- The ordered product of the determinants `det(W ⊗ a)`, `a ∈ l`, in the exterior algebra.
Source: PW v0.3, Lemma 4.1(c) (`c` factors `det(W ⊗ x)`); a proof device for S7. -/
private def a4DetProd (l : List U) : ExteriorAlgebra K (Space K W U U') :=
  (l.map fun a => (detW (K := K) (W := W) (U' := U') a : ExteriorAlgebra K (Space K W U U'))).prod

example : a4DetProd (K := K) (W := W) (U' := U') ([] : List U) = 1 := rfl

/-- The ordered product of the dual determinants `det(W^∨ ⊗ a')`, `a' ∈ l`.
Source: PW v0.3, Lemma 4.1(c) (`|c|` factors `det(W^∨ ⊗ x')`); a proof device for S7. -/
private def a4DetDualProd (l : List U') : ExteriorAlgebra K (Space K W U U') :=
  (l.map fun a' =>
    (detWDual (K := K) (W := W) (U := U) a' : ExteriorAlgebra K (Space K W U U'))).prod

example : a4DetDualProd (K := K) (W := W) (U := U) ([] : List U') = 1 := rfl

omit [CharZero K] in
theorem a4_counted_cast {n n' α α' β β' : ℕ} {g : ⋀[K]^n (Space K W U U')}
    (hg : CountedGeneratorProduct n α β g) (hn : n = n') (hα : α = α') (hβ : β = β') :
    ∃ g' : ⋀[K]^n' (Space K W U U'), CountedGeneratorProduct n' α' β' g' ∧
      (g' : ExteriorAlgebra K (Space K W U U')) = g := by
  subst hn hα hβ
  exact ⟨g, hg, rfl⟩

omit [CharZero K] in
theorem a4_exists_thetaProd (l : List (U × U')) :
    ∃ g : ⋀[K]^(2 * l.length) (Space K W U U'), CountedGeneratorProduct (2 * l.length) 0 0 g ∧
      (g : ExteriorAlgebra K (Space K W U U')) = a4ThetaProd (K := K) (W := W) l := by
  induction l with
  | nil =>
    obtain ⟨g, hg, hgc⟩ := a4_counted_cast (K := K) (W := W) (U := U) (U' := U')
      CountedGeneratorProduct.unit (show 0 = 2 * ([] : List (U × U')).length by simp) rfl rfl
    exact ⟨g, hg, by rw [hgc, a3b_coe_unit]; rfl⟩
  | cons p l ih =>
    obtain ⟨g, hg, hgc⟩ := ih
    obtain ⟨g', hg', hgc'⟩ := a4_counted_cast ((CountedGeneratorProduct.theta p.1 p.2).wedge hg)
      (show 2 + 2 * l.length = 2 * (p :: l).length by simp; ring) rfl rfl
    refine ⟨g', hg', ?_⟩
    rw [hgc', a3b_coe_wedge, hgc]
    simp [a4ThetaProd]

omit [CharZero K] in
theorem a4_exists_detProd (l : List U) :
    ∃ g : ⋀[K]^(finrank K W * l.length) (Space K W U U'),
      CountedGeneratorProduct (finrank K W * l.length) l.length 0 g ∧
      (g : ExteriorAlgebra K (Space K W U U')) = a4DetProd (K := K) (W := W) (U' := U') l := by
  induction l with
  | nil =>
    obtain ⟨g, hg, hgc⟩ := a4_counted_cast (K := K) (W := W) (U := U) (U' := U')
      CountedGeneratorProduct.unit (show 0 = finrank K W * ([] : List U).length by simp) rfl rfl
    exact ⟨g, hg, by rw [hgc, a3b_coe_unit]; rfl⟩
  | cons a l ih =>
    obtain ⟨g, hg, hgc⟩ := ih
    obtain ⟨g', hg', hgc'⟩ := a4_counted_cast ((CountedGeneratorProduct.detW a).wedge hg)
      (show finrank K W + finrank K W * l.length = finrank K W * (a :: l).length by
        simp only [List.length_cons]; ring)
      (show 1 + l.length = (a :: l).length by simp only [List.length_cons]; ring) rfl
    refine ⟨g', hg', ?_⟩
    rw [hgc', a3b_coe_wedge, hgc]
    simp [a4DetProd]

omit [CharZero K] in
theorem a4_exists_detDualProd (l : List U') :
    ∃ g : ⋀[K]^(finrank K W * l.length) (Space K W U U'),
      CountedGeneratorProduct (finrank K W * l.length) 0 l.length g ∧
      (g : ExteriorAlgebra K (Space K W U U')) = a4DetDualProd (K := K) (W := W) (U := U) l := by
  induction l with
  | nil =>
    obtain ⟨g, hg, hgc⟩ := a4_counted_cast (K := K) (W := W) (U := U) (U' := U')
      CountedGeneratorProduct.unit (show 0 = finrank K W * ([] : List U').length by simp) rfl rfl
    exact ⟨g, hg, by rw [hgc, a3b_coe_unit]; rfl⟩
  | cons a l ih =>
    obtain ⟨g, hg, hgc⟩ := ih
    obtain ⟨g', hg', hgc'⟩ := a4_counted_cast ((CountedGeneratorProduct.detWDual a).wedge hg)
      (show finrank K W + finrank K W * l.length = finrank K W * (a :: l).length by
        simp only [List.length_cons]; ring)
      rfl (show 1 + l.length = (a :: l).length by simp only [List.length_cons]; ring)
    refine ⟨g', hg', ?_⟩
    rw [hgc', a3b_coe_wedge, hgc]
    simp [a4DetDualProd]

omit [CharZero K] in
theorem a4_exists_normal (l : List (U × U')) (as : List U) (as' : List U') :
    ∃ g : ⋀[K]^(2 * l.length + finrank K W * (as.length + as'.length)) (Space K W U U'),
      CountedGeneratorProduct (2 * l.length + finrank K W * (as.length + as'.length))
        as.length as'.length g ∧
      (g : ExteriorAlgebra K (Space K W U U')) =
        a4ThetaProd (K := K) (W := W) l * a4DetProd (K := K) (U' := U') as *
          a4DetDualProd (K := K) (W := W) (U := U) as' := by
  obtain ⟨g1, hg1, h1⟩ := a4_exists_thetaProd (K := K) (W := W) l
  obtain ⟨g2, hg2, h2⟩ := a4_exists_detProd (K := K) (W := W) (U' := U') as
  obtain ⟨g3, hg3, h3⟩ := a4_exists_detDualProd (K := K) (W := W) (U := U) as'
  obtain ⟨g, hg, hgc⟩ := a4_counted_cast ((hg1.wedge hg2).wedge hg3)
    (show 2 * l.length + finrank K W * as.length + finrank K W * as'.length =
      2 * l.length + finrank K W * (as.length + as'.length) by ring)
    (show 0 + as.length + 0 = as.length by simp) (show 0 + 0 + as'.length = as'.length by simp)
  exact ⟨g, hg, by rw [hgc, a3b_coe_wedge, a3b_coe_wedge, h1, h2, h3]⟩

omit [CharZero K] in
theorem a4ThetaProd_append (l1 l2 : List (U × U')) :
    a4ThetaProd (K := K) (W := W) (l1 ++ l2) =
      a4ThetaProd (K := K) (W := W) l1 * a4ThetaProd (K := K) (W := W) l2 := by
  simp [a4ThetaProd]

omit [CharZero K] in
theorem a4DetProd_append (l1 l2 : List U) :
    a4DetProd (K := K) (W := W) (U' := U') (l1 ++ l2) =
      a4DetProd (K := K) (W := W) (U' := U') l1 * a4DetProd (K := K) (W := W) (U' := U') l2 := by
  simp [a4DetProd]

omit [CharZero K] in
theorem a4DetDualProd_append (l1 l2 : List U') :
    a4DetDualProd (K := K) (W := W) (U := U) (l1 ++ l2) =
      a4DetDualProd (K := K) (W := W) (U := U) l1 * a4DetDualProd (K := K) (W := W) (U := U) l2 := by
  simp [a4DetDualProd]

omit [CharZero K] in
theorem a4_commute_of_even {M : Type*} [AddCommGroup M] [Module K M] {i j : ℕ} (hi : Even i)
    {x y : ExteriorAlgebra K M} (hx : x ∈ ⋀[K]^i M) (hy : y ∈ ⋀[K]^j M) : Commute x y := by
  have h := a3b_mul_anticomm hx hy
  rw [(hi.mul_left j).neg_one_pow, one_smul] at h
  exact h

omit [CharZero K] in
theorem a4_counted_eq_smul {k α β : ℕ} {g : ⋀[K]^k (Space K W U U')}
    (hg : CountedGeneratorProduct k α β g) :
    ∃ (r : K) (l : List (U × U')) (as : List U) (as' : List U'),
      (g : ExteriorAlgebra K (Space K W U U')) =
        r • (a4ThetaProd (K := K) (W := W) l * a4DetProd (K := K) (U' := U') as *
          a4DetDualProd (K := K) (W := W) (U := U) as') ∧
      as.length = α ∧ as'.length = β ∧ k = 2 * l.length + finrank K W * (α + β) := by
  induction hg with
  | unit => exact ⟨1, [], [], [], by simp [a4ThetaProd, a4DetProd, a4DetDualProd],
      rfl, rfl, by simp⟩
  | theta a a' => exact ⟨1, [(a, a')], [], [],
      by simp [a4ThetaProd, a4DetProd, a4DetDualProd], rfl, rfl, by simp⟩
  | detW a => exact ⟨1, [], [a], [],
      by simp [a4ThetaProd, a4DetProd, a4DetDualProd], rfl, rfl, by simp⟩
  | detWDual a' => exact ⟨1, [], [], [a'],
      by simp [a4ThetaProd, a4DetProd, a4DetDualProd], rfl, rfl, by simp⟩
  | @wedge k l α β γ δ v w hv hw ihv ihw =>
    obtain ⟨r, l1, as1, bs1, h1, ha1, hb1, hk1⟩ := ihv
    obtain ⟨s, l2, as2, bs2, h2, ha2, hb2, hk2⟩ := ihw
    obtain ⟨t2, -, ht2⟩ := a4_exists_thetaProd (K := K) (W := W) (U := U) (U' := U') l2
    obtain ⟨d1, -, hd1⟩ := a4_exists_detProd (K := K) (W := W) (U := U) (U' := U') as1
    obtain ⟨d2, -, hd2⟩ := a4_exists_detProd (K := K) (W := W) (U := U) (U' := U') as2
    obtain ⟨e1, -, he1⟩ := a4_exists_detDualProd (K := K) (W := W) (U := U) (U' := U') bs1
    have hT2 := ht2 ▸ t2.2
    have hD1 := hd1 ▸ d1.2
    have hD2 := hd2 ▸ d2.2
    have hB1 := he1 ▸ e1.2
    have hc1 : Commute (a4ThetaProd (K := K) (W := W) l2)
        (a4DetProd (K := K) (U' := U') as1 * a4DetDualProd (K := K) (W := W) (U := U) bs1) :=
      ((a4_commute_of_even (even_two_mul _) hT2 hD1).mul_right
        (a4_commute_of_even (even_two_mul _) hT2 hB1))
    have hc2 := a3b_mul_anticomm hB1 hD2
    rw [Units.smul_def, ← Int.cast_smul_eq_zsmul K] at hc2
    set ε := (((((-1 : ℤˣ) ^ (finrank K W * as2.length * (finrank K W * bs1.length)) :
        ℤˣ) : ℤ) : K))
    set T1 := a4ThetaProd (K := K) (W := W) l1
    set T2 := a4ThetaProd (K := K) (W := W) l2
    set D1 := a4DetProd (K := K) (W := W) (U' := U') as1
    set D2 := a4DetProd (K := K) (W := W) (U' := U') as2
    set B1 := a4DetDualProd (K := K) (W := W) (U := U) bs1
    set B2 := a4DetDualProd (K := K) (W := W) (U := U) bs2
    have hprod : T1 * D1 * B1 * (T2 * D2 * B2) = ε • (T1 * T2 * (D1 * D2) * (B1 * B2)) :=
      calc T1 * D1 * B1 * (T2 * D2 * B2) = T1 * (D1 * B1 * T2) * D2 * B2 := by
            simp only [mul_assoc]
        _ = T1 * T2 * D1 * (B1 * D2) * B2 := by rw [← hc1.eq]; simp only [mul_assoc]
        _ = ε • (T1 * T2 * (D1 * D2) * (B1 * B2)) := by
            rw [hc2]; simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
    refine ⟨r * s * ε, l1 ++ l2, as1 ++ as2, bs1 ++ bs2, ?_,
      by rw [List.length_append, ha1, ha2], by rw [List.length_append, hb1, hb2],
      by subst hk1 hk2 ha1 ha2 hb1 hb2; simp only [List.length_append]; ring⟩
    rw [a3b_coe_wedge, h1, h2, a4ThetaProd_append, a4DetProd_append, a4DetDualProd_append,
      smul_mul_smul_comm, hprod, smul_smul]

theorem a4_detW_mul_detWDual (a : U) (a' : U') :
    (detW (K := K) (W := W) (U' := U') a : ExteriorAlgebra K (Space K W U U')) *
        (detWDual (K := K) (W := W) (U := U) a' : ExteriorAlgebra K (Space K W U U')) =
      ((-1 : K) ^ (finrank K W * (finrank K W - 1) / 2) * ((finrank K W).factorial : K))⁻¹ •
        a4ThetaProd (K := K) (W := W) (List.replicate (finrank K W) (a, a')) := by
  have hs : ((-1 : K) ^ (finrank K W * (finrank K W - 1) / 2) *
      ((finrank K W).factorial : K)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  rw [a4ThetaProd, List.map_replicate, List.prod_replicate, spec_a4_theta_pow_aux, smul_smul,
    inv_mul_cancel₀ hs, one_smul]

theorem a4_normal_mem_span (l : List (U × U')) (as : List U) (as' : List U') :
    a4ThetaProd (K := K) (W := W) l * a4DetProd (K := K) (U' := U') as *
        a4DetDualProd (K := K) (W := W) (U := U) as' ∈ Submodule.span K
      {z | ∃ (l' : List (U × U')) (bs : List U) (bs' : List U'),
        z = a4ThetaProd (K := K) (W := W) l' * a4DetProd (K := K) (U' := U') bs *
          a4DetDualProd (K := K) (W := W) (U := U) bs' ∧ (bs = [] ∨ bs' = []) ∧
        (bs.length : ℤ) - bs'.length = (as.length : ℤ) - as'.length ∧
        2 * l'.length + finrank K W * (bs.length + bs'.length) =
          2 * l.length + finrank K W * (as.length + as'.length)} := by
  induction as' generalizing l as with
  | nil => exact Submodule.subset_span ⟨l, as, [], rfl, Or.inr rfl, rfl, rfl⟩
  | cons a' as1 ih =>
    rcases as.eq_nil_or_concat with rfl | ⟨as0, a, rfl⟩
    · exact Submodule.subset_span ⟨l, [], a' :: as1, rfl, Or.inl rfl, rfl, rfl⟩
    obtain ⟨t, -, ht⟩ := a4_exists_thetaProd (K := K) (W := W) (U := U) (U' := U')
      (List.replicate (finrank K W) (a, a'))
    obtain ⟨d, -, hd⟩ := a4_exists_detProd (K := K) (W := W) (U := U) (U' := U') as0
    have hc : Commute (a4ThetaProd (K := K) (W := W) (List.replicate (finrank K W) (a, a')))
        (a4DetProd (K := K) (U' := U') as0) :=
      a4_commute_of_even (even_two_mul _) (ht ▸ t.2) (hd ▸ d.2)
    have key : a4ThetaProd (K := K) (W := W) l * a4DetProd (K := K) (U' := U') (as0.concat a) *
        a4DetDualProd (K := K) (W := W) (U := U) (a' :: as1) =
        ((-1 : K) ^ (finrank K W * (finrank K W - 1) / 2) * ((finrank K W).factorial : K))⁻¹ •
          (a4ThetaProd (K := K) (W := W) (l ++ List.replicate (finrank K W) (a, a')) *
            a4DetProd (K := K) (U' := U') as0 * a4DetDualProd (K := K) (W := W) (U := U) as1) := by
      have h1 : a4DetProd (K := K) (W := W) (U' := U') (as0.concat a) =
          a4DetProd (K := K) (W := W) (U' := U') as0 *
            (detW (K := K) (W := W) (U' := U') a : ExteriorAlgebra K (Space K W U U')) := by
        simp [a4DetProd]
      have h2 : a4DetDualProd (K := K) (W := W) (U := U) (a' :: as1) =
          (detWDual (K := K) (W := W) (U := U) a' : ExteriorAlgebra K (Space K W U U')) *
            a4DetDualProd (K := K) (W := W) (U := U) as1 := by
        simp [a4DetDualProd]
      rw [h1, h2, a4ThetaProd_append]
      calc _ = a4ThetaProd (K := K) (W := W) l * a4DetProd (K := K) (U' := U') as0 *
            ((detW (K := K) (W := W) (U' := U') a : ExteriorAlgebra K (Space K W U U')) *
              (detWDual (K := K) (W := W) (U := U) a' : ExteriorAlgebra K (Space K W U U'))) *
            a4DetDualProd (K := K) (W := W) (U := U) as1 := by simp only [mul_assoc]
        _ = _ := by
          rw [a4_detW_mul_detWDual]
          simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
          rw [← mul_assoc (a4DetProd (K := K) (U' := U') as0), ← hc.eq, mul_assoc]
    rw [key]
    refine Submodule.smul_mem _ _ (Submodule.span_mono ?_ (ih _ _))
    rintro z ⟨l', bs, bs', hz, hor, h1, h2⟩
    refine ⟨l', bs, bs', hz, hor, ?_, ?_⟩
    · simp only [List.length_concat, List.length_cons] at h1 ⊢
      push_cast at h1 ⊢
      linarith
    · simp only [List.length_append, List.length_replicate, List.length_concat,
        List.length_cons] at h2 ⊢
      rw [h2]
      ring

theorem spec_a4_counted_span_normal_aux (k : ℕ) (c : ℤ) :
    Submodule.span K {g : ⋀[K]^k (Space K W U U') |
        ∃ α β : ℕ, (α : ℤ) - β = c ∧ CountedGeneratorProduct k α β g} =
      Submodule.span K {g : ⋀[K]^k (Space K W U U') |
        ∃ α β : ℕ, (α : ℤ) - β = c ∧ (α = 0 ∨ β = 0) ∧ CountedGeneratorProduct k α β g} := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro g ⟨α, β, hc, hg⟩
    obtain ⟨r, l, as, as', hgr, hα, hβ, hk⟩ := a4_counted_eq_smul hg
    set S := {g : ⋀[K]^k (Space K W U U') |
      ∃ α β : ℕ, (α : ℤ) - β = c ∧ (α = 0 ∨ β = 0) ∧ CountedGeneratorProduct k α β g}
    have hmap : ((⋀[K]^k (Space K W U U')).subtype g) ∈
        Submodule.map (⋀[K]^k (Space K W U U')).subtype (Submodule.span K S) := by
      rw [← Submodule.span_image, Submodule.coe_subtype, hgr]
      refine Submodule.smul_mem _ _ (Submodule.span_mono ?_ (a4_normal_mem_span l as as'))
      rintro z ⟨l', bs, bs', rfl, hor, h1, h2⟩
      obtain ⟨g', hg', hgc'⟩ := a4_exists_normal (K := K) (W := W) l' bs bs'
      obtain ⟨g'', hg'', hgc''⟩ := a4_counted_cast hg'
        (show _ = k by rw [h2, hk, hα, hβ]) rfl rfl
      refine ⟨g'', ⟨bs.length, bs'.length, ?_, ?_, hg''⟩, by
        rw [hgc'', hgc']⟩
      · rw [h1, hα, hβ, hc]
      · rcases hor with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
    obtain ⟨y, hy, hyg⟩ := hmap
    rw [Subtype.ext hyg] at hy
    exact hy
  · exact Submodule.span_mono fun g ⟨α, β, hc, _, hg⟩ => ⟨α, β, hc, hg⟩

omit [CharZero K] in
theorem a4_generatorProduct_of_counted {k α β : ℕ} {g : ⋀[K]^k (Space K W U U')}
    (hg : CountedGeneratorProduct k α β g) : GeneratorProduct k g := by
  induction hg with
  | unit => exact GeneratorProduct.unit
  | theta a a' => exact GeneratorProduct.theta a a'
  | detW a => exact GeneratorProduct.detW a
  | detWDual a' => exact GeneratorProduct.detWDual a'
  | wedge _ _ ihv ihw => exact GeneratorProduct.wedge ihv ihw

omit [CharZero K] in
theorem a4_counted_of_generatorProduct {k : ℕ} {g : ⋀[K]^k (Space K W U U')}
    (hg : GeneratorProduct k g) : ∃ α β : ℕ, CountedGeneratorProduct k α β g := by
  induction hg with
  | unit => exact ⟨0, 0, CountedGeneratorProduct.unit⟩
  | theta a a' => exact ⟨0, 0, CountedGeneratorProduct.theta a a'⟩
  | detW a => exact ⟨1, 0, CountedGeneratorProduct.detW a⟩
  | detWDual a' => exact ⟨0, 1, CountedGeneratorProduct.detWDual a'⟩
  | wedge _ _ ihv ihw =>
    obtain ⟨α, β, hv⟩ := ihv
    obtain ⟨γ, δ, hw⟩ := ihw
    exact ⟨α + γ, β + δ, hv.wedge hw⟩

theorem spec_a4_isotypic_eq_span_aux [Nontrivial W] (k : ℕ) (c : ℤ) :
    generatedDegree (K := K) (W := W) (U := U) (U' := U') k ⊓
        (⨅ f : Module.End K W, LinearMap.ker (exteriorDer k (multiplicityLie K W U U' f) -
          ((c : K) * LinearMap.trace K W f) • LinearMap.id)) =
      Submodule.span K {g : ⋀[K]^k (Space K W U U') |
        ∃ α β : ℕ, (α : ℤ) - β = c ∧ (α = 0 ∨ β = 0) ∧ CountedGeneratorProduct k α β g} := by
  set V : ℤ → Submodule K (⋀[K]^k (Space K W U U')) := fun c' => Submodule.span K
    {g | ∃ α β : ℕ, (α : ℤ) - β = c' ∧ CountedGeneratorProduct k α β g} with hVdef
  set D := exteriorDer k (multiplicityLie K W U U' LinearMap.id)
  have hm : (finrank K W : K) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hVE : ∀ c' : ℤ, V c' ≤ D.eigenspace ((c' : K) * finrank K W) := by
    intro c'
    rw [hVdef, Submodule.span_le]
    rintro g ⟨α, β, hc', hg⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, spec_a4_exteriorDer_counted_aux hg,
      LinearMap.trace_id, ← hc']
    push_cast
    rfl
  apply le_antisymm
  · rintro y ⟨hy, hker⟩
    rw [← spec_a4_counted_span_normal_aux]
    have hyV : y ∈ ⨆ c', V c' := by
      have hle : generatedDegree (K := K) (W := W) (U := U) (U' := U') k ≤ ⨆ c', V c' := by
        rw [generatedDegree, Submodule.span_le]
        intro g hg
        obtain ⟨α, β, hc⟩ := a4_counted_of_generatorProduct hg
        exact Submodule.mem_iSup_of_mem ((α : ℤ) - β) (Submodule.subset_span ⟨α, β, rfl, hc⟩)
      exact hle hy
    have hyE : y ∈ D.eigenspace ((c : K) * finrank K W) := by
      have h := (Submodule.mem_iInf _).mp hker LinearMap.id
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply,
        LinearMap.id_apply, LinearMap.trace_id] at h
      exact Module.End.mem_eigenspace_iff.mpr h
    obtain ⟨z, hz, hyz⟩ : ∃ z ∈ V c, y - z ∈ ⨆ (c' : ℤ) (_ : c' ≠ c), V c' := by
      refine Submodule.iSup_induction V (motive := fun y =>
        ∃ z ∈ V c, y - z ∈ ⨆ (c' : ℤ) (_ : c' ≠ c), V c') hyV ?_ ?_ ?_
      · intro i x hx
        by_cases h : i = c
        · subst h
          exact ⟨x, hx, by rw [sub_self]; exact Submodule.zero_mem _⟩
        · refine ⟨0, Submodule.zero_mem _, ?_⟩
          rw [sub_zero]
          exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem h hx)
      · exact ⟨0, Submodule.zero_mem _, by rw [sub_zero]; exact Submodule.zero_mem _⟩
      · rintro x y ⟨z1, hz1, h1⟩ ⟨z2, hz2, h2⟩
        refine ⟨z1 + z2, Submodule.add_mem _ hz1 hz2, ?_⟩
        rw [show x + y - (z1 + z2) = (x - z1) + (y - z2) by abel]
        exact Submodule.add_mem _ h1 h2
    have hle : (⨆ (c' : ℤ) (_ : c' ≠ c), V c') ≤
        ⨆ (μ : K) (_ : μ ≠ (c : K) * finrank K W), D.eigenspace μ := by
      refine iSup₂_le fun c' hc' => ?_
      refine le_iSup₂_of_le ((c' : K) * finrank K W) ?_ (hVE c')
      intro h
      exact hc' (Int.cast_injective (mul_right_cancel₀ hm h))
    have h0 : y - z = 0 := by
      have hd := (Module.End.eigenspaces_iSupIndep D) ((c : K) * finrank K W)
      exact (Submodule.disjoint_def.mp hd) _ (Submodule.sub_mem _ hyE (hVE c hz)) (hle hyz)
    rw [sub_eq_zero.mp h0]
    exact hz
  · rw [Submodule.span_le]
    rintro g ⟨α, β, hc, -, hg⟩
    refine ⟨Submodule.subset_span (a4_generatorProduct_of_counted hg), ?_⟩
    refine (Submodule.mem_iInf _).mpr fun f => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, spec_a4_exteriorDer_counted_aux hg f,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, ← hc]
    push_cast
    rfl

end OneBlock

section Main

variable {e : ℕ} {W U U' : Fin e → Type*}
  [∀ v, AddCommGroup (W v)] [∀ v, Module K (W v)] [∀ v, FiniteDimensional K (W v)]
  [∀ v, AddCommGroup (U v)] [∀ v, Module K (U v)]
  [∀ v, AddCommGroup (U' v)] [∀ v, Module K (U' v)]

omit [CharZero K] [∀ v, FiniteDimensional K (W v)] in
theorem a4_piMap_comp_single (f : (v : Fin e) → Module.End K (W v)) (v : Fin e) :
    (LinearMap.piMap fun v => multiplicityLie K (W v) (U v) (U' v) (f v)).comp
        (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v) =
      (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v).comp
        (multiplicityLie K (W v) (U v) (U' v) (f v)) := by
  refine LinearMap.ext fun y => funext fun w => ?_
  rcases eq_or_ne w v with rfl | h
  · simp
  · simp [Pi.single_eq_of_ne h]

theorem spec_a4_exteriorDer_multiCounted_aux {k : ℕ} {α β : Fin e → ℕ}
    {x : ⋀[K]^k (MultiSpace K W U U')} (hx : MultiCountedProduct k α β x)
    (f : (v : Fin e) → Module.End K (W v)) :
    exteriorDer k (LinearMap.piMap fun v => multiplicityLie K (W v) (U v) (U' v) (f v)) x =
      (∑ v, ((α v : K) - β v) * LinearMap.trace K (W v) (f v)) • x := by
  induction hx with
  | unit => simp [exteriorDer_ιMulti]
  | @block v k α β g hg =>
    rw [exteriorDer_map _ _ _ _ (a4_piMap_comp_single f v), spec_a4_exteriorDer_counted_aux hg,
      map_smul]
    congr 1
    rw [Finset.sum_eq_single v]
    · simp
    · intro w _ hw
      simp [Pi.single_eq_of_ne hw]
    · simp
  | @wedge k l α β γ δ x y _ _ ihx ihy =>
    rw [exteriorDer_wedge, ihx, ihy, LinearMap.map_smul₂, LinearMap.map_smul, ← add_smul]
    congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Pi.add_apply, Nat.cast_add]
    ring

omit [CharZero K] in
theorem a4_b_generatorProduct_of_counted {W₀ U₀ U₀' : Type*} [AddCommGroup W₀] [Module K W₀]
    [FiniteDimensional K W₀] [AddCommGroup U₀] [Module K U₀] [AddCommGroup U₀'] [Module K U₀']
    {k α β : ℕ} {g : ⋀[K]^k (Space K W₀ U₀ U₀')} (hg : CountedGeneratorProduct k α β g) :
    GeneratorProduct k g := by
  induction hg with
  | unit => exact GeneratorProduct.unit
  | theta a a' => exact GeneratorProduct.theta a a'
  | detW a => exact GeneratorProduct.detW a
  | detWDual a' => exact GeneratorProduct.detWDual a'
  | wedge _ _ ih₁ ih₂ => exact GeneratorProduct.wedge ih₁ ih₂

omit [CharZero K] in
theorem a4_b_counted_of_generatorProduct {W₀ U₀ U₀' : Type*} [AddCommGroup W₀] [Module K W₀]
    [FiniteDimensional K W₀] [AddCommGroup U₀] [Module K U₀] [AddCommGroup U₀'] [Module K U₀']
    {k : ℕ} {g : ⋀[K]^k (Space K W₀ U₀ U₀')} (hg : GeneratorProduct k g) :
    ∃ α β : ℕ, CountedGeneratorProduct k α β g := by
  induction hg with
  | unit => exact ⟨0, 0, CountedGeneratorProduct.unit⟩
  | theta a a' => exact ⟨0, 0, CountedGeneratorProduct.theta a a'⟩
  | detW a => exact ⟨1, 0, CountedGeneratorProduct.detW a⟩
  | detWDual a' => exact ⟨0, 1, CountedGeneratorProduct.detWDual a'⟩
  | wedge _ _ ih₁ ih₂ =>
    obtain ⟨α, β, h₁⟩ := ih₁
    obtain ⟨γ, δ, h₂⟩ := ih₂
    exact ⟨α + γ, β + δ, CountedGeneratorProduct.wedge h₁ h₂⟩

omit [CharZero K] in
theorem a4_multiGeneratorProduct_of_counted {k : ℕ} {α β : Fin e → ℕ}
    {x : ⋀[K]^k (MultiSpace K W U U')} (hx : MultiCountedProduct k α β x) :
    MultiGeneratorProduct k x := by
  induction hx with
  | unit => exact MultiGeneratorProduct.unit
  | block v hg => exact MultiGeneratorProduct.block v (a4_b_generatorProduct_of_counted hg)
  | wedge _ _ ih₁ ih₂ => exact MultiGeneratorProduct.wedge ih₁ ih₂

omit [CharZero K] in
theorem a4_multiCounted_of_generatorProduct {k : ℕ} {x : ⋀[K]^k (MultiSpace K W U U')}
    (hx : MultiGeneratorProduct k x) : ∃ α β : Fin e → ℕ, MultiCountedProduct k α β x := by
  induction hx with
  | unit => exact ⟨0, 0, MultiCountedProduct.unit⟩
  | block v hg =>
    obtain ⟨α, β, h⟩ := a4_b_counted_of_generatorProduct hg
    exact ⟨_, _, MultiCountedProduct.block v h⟩
  | wedge _ _ ih₁ ih₂ =>
    obtain ⟨α, β, h₁⟩ := ih₁
    obtain ⟨γ, δ, h₂⟩ := ih₂
    exact ⟨α + γ, β + δ, MultiCountedProduct.wedge h₁ h₂⟩

set_option linter.unusedSectionVars false in
theorem spec_a4_multiGeneratedDegree_eq_span_counted_aux (k : ℕ) :
    multiGeneratedDegree (K := K) (W := W) (U := U) (U' := U') k =
      Submodule.span K {x | ∃ α β : Fin e → ℕ, MultiCountedProduct k α β x} := by
  unfold multiGeneratedDegree
  congr 1
  ext x
  exact ⟨a4_multiCounted_of_generatorProduct, fun ⟨_, _, h⟩ => a4_multiGeneratorProduct_of_counted h⟩

omit [CharZero K] in
/-- A vector of the kernel of `D` in the span of finitely many eigenvectors of `D` with nonzero
eigenvalues is zero. -/
theorem a4_c_eq_zero_of_mem_span_eigen {V : Type*} [AddCommGroup V] [Module K V]
    (D : Module.End K V) (F : Finset V) (hF : ∀ x ∈ F, ∃ μ : K, μ ≠ 0 ∧ D x = μ • x) {z : V}
    (hz : z ∈ Submodule.span K (F : Set V)) (hDz : D z = 0) : z = 0 := by
  classical
  induction F using Finset.induction_on generalizing z with
  | empty => simpa using hz
  | insert v F _ ih =>
    have hF' : ∀ x ∈ F, ∃ μ : K, μ ≠ 0 ∧ D x = μ • x := fun x hx =>
      hF x (Finset.mem_insert_of_mem hx)
    obtain ⟨μ, hμ, hDv⟩ := hF v (Finset.mem_insert_self v F)
    have hinv : Submodule.span K (F : Set V) ≤ (Submodule.span K (F : Set V)).comap D := by
      rw [Submodule.span_le]
      intro x hx
      obtain ⟨ν, _, hDx⟩ := hF' x hx
      rw [SetLike.mem_coe, Submodule.mem_comap, hDx]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hx)
    rw [Finset.coe_insert, Submodule.mem_span_insert] at hz
    obtain ⟨a, z', hz', rfl⟩ := hz
    have hz'D : D z' = -(a • μ • v) := by
      rw [map_add, map_smul, hDv] at hDz
      exact eq_neg_of_add_eq_zero_right hDz
    have hmem : μ • (a • v + z') ∈ Submodule.span K (F : Set V) := by
      have h : μ • (a • v + z') = μ • z' - D z' := by rw [hz'D]; module
      rw [h]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hz') (hinv hz')
    have hmem' : a • v + z' ∈ Submodule.span K (F : Set V) := by
      have := Submodule.smul_mem _ μ⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ hμ, one_smul] at this
    exact ih hF' hmem' hDz

omit [CharZero K] in
/-- In the span of a set of eigenvectors of `D`, the kernel of `D` is spanned by the
eigenvectors of eigenvalue `0`. -/
theorem a4_c_mem_span_ker {V : Type*} [AddCommGroup V] [Module K V] (D : Module.End K V)
    (S : Set V) (hS : ∀ x ∈ S, ∃ μ : K, D x = μ • x) {y : V} (hy : y ∈ Submodule.span K S)
    (hDy : D y = 0) : y ∈ Submodule.span K {x | x ∈ S ∧ D x = 0} := by
  have hsub : S ⊆ {x | x ∈ S ∧ D x = 0} ∪ {x | x ∈ S ∧ ∃ μ : K, μ ≠ 0 ∧ D x = μ • x} := by
    intro x hx
    obtain ⟨μ, hμ⟩ := hS x hx
    by_cases h0 : μ = 0
    · exact Or.inl ⟨hx, by rw [hμ, h0, zero_smul]⟩
    · exact Or.inr ⟨hx, μ, h0, hμ⟩
  have hy' := Submodule.span_mono hsub hy
  rw [Submodule.span_union, Submodule.mem_sup] at hy'
  obtain ⟨y₀, hy₀, y₁, hy₁, rfl⟩ := hy'
  have hD0 : D y₀ = 0 := by
    have : Submodule.span K {x | x ∈ S ∧ D x = 0} ≤ LinearMap.ker D := by
      rw [Submodule.span_le]
      rintro x ⟨_, hx⟩
      exact hx
    exact this hy₀
  have hD1 : D y₁ = 0 := by rwa [map_add, hD0, zero_add] at hDy
  obtain ⟨T, hT, hy₁T⟩ := Submodule.mem_span_finite_of_mem_span hy₁
  have : y₁ = 0 := a4_c_eq_zero_of_mem_span_eigen D T (fun x hx => (hT hx).2) hy₁T hD1
  rw [this, add_zero]
  exact hy₀

omit [CharZero K] in
/-- In the span of a set of joint eigenvectors of a family `D`, the joint kernel of finitely many
`D i` is spanned by the joint eigenvectors that they kill. -/
theorem a4_c_mem_span_iInf_ker {V ι : Type*} [AddCommGroup V] [Module K V]
    (D : ι → Module.End K V) (I : Finset ι) (S : Set V)
    (hS : ∀ x ∈ S, ∀ i, ∃ μ : K, D i x = μ • x) {y : V} (hy : y ∈ Submodule.span K S)
    (hDy : ∀ i ∈ I, D i y = 0) : y ∈ Submodule.span K {x | x ∈ S ∧ ∀ i ∈ I, D i x = 0} := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using hy
  | insert i I _ ih =>
    have h1 := ih (fun j hj => hDy j (Finset.mem_insert_of_mem hj))
    have h2 := a4_c_mem_span_ker (D i) _ (fun x hx => hS x hx.1 i) h1
      (hDy i (Finset.mem_insert_self i I))
    refine Submodule.span_mono ?_ h2
    rintro x ⟨⟨hx, hxI⟩, hxi⟩
    refine ⟨hx, fun j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hxi
    · exact hxI j hj

/-- A block scalar `t_v · id` acts on a counted product by `Σ_v c_v t_v dim W_v`. -/
theorem a4_c_exteriorDer_torus (k : ℕ) (t : Fin e → K) {α β : Fin e → ℕ}
    {x : ⋀[K]^k (MultiSpace K W U U')} (hx : MultiCountedProduct k α β x) :
    exteriorDer k (LinearMap.piMap fun v =>
        multiplicityLie K (W v) (U v) (U' v) (t v • LinearMap.id)) x =
      (∑ v, ((α v : K) - β v) * (t v * finrank K (W v))) • x := by
  rw [spec_a4_exteriorDer_multiCounted_aux hx]
  simp only [map_smul, LinearMap.trace_id, smul_eq_mul]

theorem spec_a4_torus_invariants_aux [∀ v, Nontrivial (W v)] (k : ℕ) :
    multiGeneratedDegree (K := K) (W := W) (U := U) (U' := U') k ⊓
        (⨅ t : {t : Fin e → K // ∑ v, t v * (finrank K (W v) : K) = 0},
          LinearMap.ker (exteriorDer k (LinearMap.piMap fun v =>
            multiplicityLie K (W v) (U v) (U' v) (t.1 v • LinearMap.id)))) =
      constWeightDegree (K := K) (W := W) (U := U) (U' := U') k := by
  apply le_antisymm
  · intro y hy
    rw [Submodule.mem_inf, Submodule.mem_iInf] at hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [spec_a4_multiGeneratedDegree_eq_span_counted_aux] at hy1
    let tt : Fin e × Fin e → Fin e → K := fun p =>
      Pi.single p.1 (finrank K (W p.2) : K) - Pi.single p.2 (finrank K (W p.1) : K)
    have htt : ∀ p, ∑ v, tt p v * (finrank K (W v) : K) = 0 := by
      intro p
      simp only [tt, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Pi.single_apply, ite_mul,
        zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring
    have hmem := a4_c_mem_span_iInf_ker (fun p => exteriorDer k (LinearMap.piMap fun v =>
        multiplicityLie K (W v) (U v) (U' v) (tt p v • LinearMap.id))) Finset.univ
      {x | ∃ α β : Fin e → ℕ, MultiCountedProduct k α β x}
      (fun x hx p => by
        obtain ⟨α, β, hx⟩ := hx
        exact ⟨_, a4_c_exteriorDer_torus k (tt p) hx⟩)
      hy1 (fun p _ => hy2 ⟨tt p, htt p⟩)
    refine (Submodule.span_le.mpr ?_) hmem
    rintro x ⟨⟨α, β, hx⟩, hker⟩
    by_cases hx0 : x = 0
    · rw [hx0]; exact Submodule.zero_mem _
    have hconst : ∀ v w, (α v : ℤ) - β v = (α w : ℤ) - β w := by
      intro v w
      have h := hker (v, w) (Finset.mem_univ _)
      rw [a4_c_exteriorDer_torus k (tt (v, w)) hx, smul_eq_zero] at h
      have hs := h.resolve_right hx0
      simp only [tt, Pi.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib, Pi.single_apply,
        ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true] at hs
      have hv : (finrank K (W v) : K) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
      have hw : (finrank K (W w) : K) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
      have h3 : (((α v : ℤ) - β v : ℤ) : K) = (((α w : ℤ) - β w : ℤ) : K) := by
        push_cast
        have h4 : (((α v : K) - β v) - ((α w : K) - β w)) *
            ((finrank K (W v) : K) * finrank K (W w)) = 0 := by linear_combination hs
        rcases mul_eq_zero.mp h4 with h5 | h5
        · exact sub_eq_zero.mp h5
        · exact absurd h5 (mul_ne_zero hv hw)
      exact Int.cast_injective h3
    rcases isEmpty_or_nonempty (Fin e) with he | he
    · exact Submodule.subset_span ⟨0, α, β, fun v => isEmptyElim v, hx⟩
    · obtain ⟨v₀⟩ := he
      exact Submodule.subset_span ⟨(α v₀ : ℤ) - β v₀, α, β, fun v => hconst v v₀, hx⟩
  · rw [constWeightDegree, Submodule.span_le]
    rintro x ⟨c, α, β, hc, hx⟩
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, spec_a4_multiGeneratedDegree_eq_span_counted_aux]
      exact Submodule.subset_span ⟨α, β, hx⟩
    · rw [SetLike.mem_coe, Submodule.mem_iInf]
      intro t
      rw [LinearMap.mem_ker, a4_c_exteriorDer_torus k t.1 hx]
      have hc' : ∀ v, ((α v : K) - β v) = (c : K) := fun v => by
        rw [← hc v]; push_cast; ring
      simp only [hc', ← Finset.mul_sum, t.2, mul_zero, zero_smul]

theorem spec_a4_traceZero_invariants_aux [∀ v, FiniteDimensional K (U v)]
    [∀ v, FiniteDimensional K (U' v)] [∀ v, Nontrivial (W v)] (k : ℕ) :
    (⨅ f : {f : (v : Fin e) → Module.End K (W v) // ∑ v, LinearMap.trace K (W v) (f v) = 0},
        LinearMap.ker (exteriorDer k
          (LinearMap.piMap fun v => multiplicityLie K (W v) (U v) (U' v) (f.1 v)))) =
      constWeightDegree (K := K) (W := W) (U := U) (U' := U') k := by
  apply le_antisymm
  · intro y hy
    rw [Submodule.mem_iInf] at hy
    rw [← spec_a4_torus_invariants_aux k]
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [← spec_a3b_invariants_eq_multiGeneratedDegree k, Submodule.mem_iInf]
      intro f
      exact hy ⟨fun v => (f v : Module.End K (W v)), by
        simp only [(mem_slEnd).mp (f _).2, Finset.sum_const_zero]⟩
    · rw [Submodule.mem_iInf]
      intro t
      exact hy ⟨fun v => t.1 v • LinearMap.id, by
        simpa only [map_smul, LinearMap.trace_id, smul_eq_mul] using t.2⟩
  · rw [constWeightDegree, Submodule.span_le]
    rintro x ⟨c, α, β, hc, hx⟩
    rw [SetLike.mem_coe, Submodule.mem_iInf]
    intro f
    rw [LinearMap.mem_ker, spec_a4_exteriorDer_multiCounted_aux hx]
    have hc' : ∀ v, ((α v : K) - β v) = (c : K) := fun v => by
      rw [← hc v]; push_cast; ring
    simp only [hc', ← Finset.mul_sum, f.2, mul_zero, zero_smul]

omit [CharZero K] in
/-- Reordering a product of homogeneous elements of an exterior algebra changes it by a scalar. -/
theorem a4_c_prod_perm {M : Type*} [AddCommGroup M] [Module K M]
    {l₁ l₂ : List (ExteriorAlgebra K M)} (h : l₁.Perm l₂)
    (hl : ∀ a ∈ l₁, ∃ i, a ∈ ⋀[K]^i M) : ∃ s : K, l₂.prod = s • l₁.prod := by
  induction h with
  | nil => exact ⟨1, by rw [one_smul]⟩
  | cons x _ ih =>
    obtain ⟨s, hs⟩ := ih fun a ha => hl a (List.mem_cons_of_mem x ha)
    exact ⟨s, by rw [List.prod_cons, List.prod_cons, hs, mul_smul_comm]⟩
  | swap x y l =>
    obtain ⟨i, hi⟩ := hl y (by simp)
    obtain ⟨j, hj⟩ := hl x (by simp)
    refine ⟨((((-1 : ℤˣ) ^ (i * j) : ℤˣ) : ℤ) : K), ?_⟩
    rw [List.prod_cons, List.prod_cons, List.prod_cons, List.prod_cons, ← mul_assoc, ← mul_assoc,
      a3b_mul_anticomm hj hi, Units.smul_def, smul_mul_assoc, Int.cast_smul_eq_zsmul]
  | trans h₁₂ _ ih₁ ih₂ =>
    obtain ⟨s, hs⟩ := ih₁ hl
    obtain ⟨t, ht⟩ := ih₂ fun a ha => hl a (h₁₂.symm.subset ha)
    exact ⟨t * s, by rw [ht, hs, smul_smul]⟩

omit [CharZero K] in
theorem a4_c_coe_ofFn {α : Type*} : ∀ {n : ℕ} (f : Fin n → α),
    ((List.ofFn f : List α) : Multiset α) = ∑ j, {f j}
  | 0, _ => by simp
  | n + 1, f => by
    rw [List.ofFn_succ, Fin.sum_univ_succ, ← a4_c_coe_ofFn, ← Multiset.cons_coe,
      Multiset.singleton_add]

omit [CharZero K] in
theorem a4_c_coe_flatten_ofFn {α : Type*} : ∀ {n : ℕ} (F : Fin n → List α),
    (((List.ofFn F).flatten : List α) : Multiset α) = ∑ v, ((F v : List α) : Multiset α)
  | 0, _ => by simp
  | n + 1, F => by
    rw [List.ofFn_succ, List.flatten_cons, ← Multiset.coe_add, a4_c_coe_flatten_ofFn,
      Fin.sum_univ_succ]

omit [CharZero K] in
theorem a4_c_ofFn_append_comp {α β : Type*} {m n : ℕ} (f : α → β) (a : Fin m → α)
    (b : Fin n → α) :
    List.ofFn (fun j => f (Fin.append a b j)) =
      List.ofFn (fun j => f (a j)) ++ List.ofFn (fun j => f (b j)) := by
  rw [← List.ofFn_fin_append]
  congr 1
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp

omit [CharZero K] in
/-- An ordered product of spans lies in the span of the ordered products of generators. -/
theorem a4_c_prod_ofFn_span_le {A : Type*} [Ring A] [Algebra K A] :
    ∀ (n : ℕ) (G : Fin n → Set A),
      (List.ofFn fun v => Submodule.span K (G v)).prod ≤
        Submodule.span K {z | ∃ y : Fin n → A, (∀ v, y v ∈ G v) ∧ z = (List.ofFn y).prod}
  | 0, G => by
    rw [List.ofFn_zero, List.prod_nil, Submodule.one_eq_span, Submodule.span_le,
      Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨Fin.elim0, fun v => v.elim0, by simp⟩
  | n + 1, G => by
    rw [List.ofFn_succ, List.prod_cons]
    refine (mul_le_mul' le_rfl (a4_c_prod_ofFn_span_le n fun v => G v.succ)).trans ?_
    rw [Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨a, ha, _, ⟨y, hy, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨Fin.cons a y, fun v => ?_, by simp [List.ofFn_succ]⟩
    refine Fin.cases ?_ (fun i => ?_) v
    · simpa using ha
    · simpa using hy i

omit [CharZero K] in
/-- A counted generator product of one block is, up to a scalar, a product of contractions times
`α` factors `det(W ⊗ a)` times `β` factors `det(W^∨ ⊗ a')`. -/
theorem a4_c_counted_eq_smul {X Y Z : Type*} [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [AddCommGroup Y] [Module K Y] [AddCommGroup Z] [Module K Z] {k α β : ℕ}
    {g : ⋀[K]^k (Space K X Y Z)} (hg : CountedGeneratorProduct k α β g) :
    ∃ (l : List (Y × Z)) (a : Fin α → Y) (a' : Fin β → Z) (s : K),
      (g : ExteriorAlgebra K (Space K X Y Z)) = s •
        ((l.map fun p => (theta (K := K) (W := X) p.1 p.2 : ExteriorAlgebra K (Space K X Y Z))).prod *
          (List.ofFn fun j =>
            (detW (K := K) (W := X) (U' := Z) (a j) : ExteriorAlgebra K (Space K X Y Z))).prod *
          (List.ofFn fun j =>
            (detWDual (K := K) (W := X) (U := Y) (a' j) : ExteriorAlgebra K (Space K X Y Z))).prod) := by
  induction hg with
  | unit => exact ⟨[], Fin.elim0, Fin.elim0, 1, by simp⟩
  | theta a a' => exact ⟨[(a, a')], Fin.elim0, Fin.elim0, 1, by simp⟩
  | detW a => exact ⟨[], fun _ => a, Fin.elim0, 1, by simp⟩
  | detWDual a' => exact ⟨[], Fin.elim0, fun _ => a', 1, by simp⟩
  | wedge _ _ ih₁ ih₂ =>
    obtain ⟨l, a, a', s, hs⟩ := ih₁
    obtain ⟨m, b, b', t, ht⟩ := ih₂
    set θf := fun p : Y × Z => (theta (K := K) (W := X) p.1 p.2 : ExteriorAlgebra K (Space K X Y Z))
    set df := fun y : Y => (detW (K := K) (W := X) (U' := Z) y : ExteriorAlgebra K (Space K X Y Z))
    set df' := fun z : Z => (detWDual (K := K) (W := X) (U := Y) z : ExteriorAlgebra K (Space K X Y Z))
    have hperm : ((l ++ m).map θf ++ List.ofFn (fun j => df (Fin.append a b j)) ++
        List.ofFn (fun j => df' (Fin.append a' b' j))).Perm
        (l.map θf ++ List.ofFn (fun j => df (a j)) ++ List.ofFn (fun j => df' (a' j)) ++
          (m.map θf ++ List.ofFn (fun j => df (b j)) ++ List.ofFn (fun j => df' (b' j)))) := by
      rw [← Multiset.coe_eq_coe]
      simp only [List.map_append, a4_c_ofFn_append_comp, ← Multiset.coe_add]
      abel
    obtain ⟨r, hr⟩ := a4_c_prod_perm hperm (by
      intro x hx
      simp only [List.mem_append, List.mem_map, List.mem_ofFn] at hx
      rcases hx with ((⟨p, _, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩)
      · exact ⟨2, Subtype.mem _⟩
      · exact ⟨_, Subtype.mem _⟩
      · exact ⟨_, Subtype.mem _⟩)
    refine ⟨l ++ m, Fin.append a b, Fin.append a' b', s * t * r, ?_⟩
    rw [a3b_coe_wedge_c, hs, ht, smul_mul_smul_comm, mul_smul (s * t) r]
    congr 1
    simpa only [List.prod_append, mul_assoc] using hr

omit [CharZero K] in
/-- Every `MultiCountedProduct` of weights `(α, β)` lies in the member of weight `α - β` of any
family of submodules of the exterior algebra indexed by weights that contains `1` at weight `0`,
the block images of counted products at their weights, and is closed under multiplication. -/
theorem a4_c_mem_of_multiCountedProduct
    (R : (Fin e → ℤ) → Submodule K (ExteriorAlgebra K (MultiSpace K W U U')))
    (h1 : (1 : ExteriorAlgebra K (MultiSpace K W U U')) ∈ R 0)
    (hblock : ∀ (v : Fin e) (n α β : ℕ) (g : ⋀[K]^n (Space K (W v) (U v) (U' v))),
      CountedGeneratorProduct n α β g →
        ExteriorAlgebra.map (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)
          (g : ExteriorAlgebra K (Space K (W v) (U v) (U' v))) ∈ R (Pi.single v ((α : ℤ) - β)))
    (hmul : ∀ a b, R a * R b ≤ R (a + b)) {k : ℕ} {α β : Fin e → ℕ}
    {x : ⋀[K]^k (MultiSpace K W U U')} (hx : MultiCountedProduct k α β x) :
    (x : ExteriorAlgebra K (MultiSpace K W U U')) ∈ R (fun v => (α v : ℤ) - β v) := by
  induction hx with
  | unit =>
    rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply]
    convert h1 using 2
    funext v
    simp
  | block v hg =>
    rw [exteriorPower.coe_map]
    convert hblock v _ _ _ _ hg using 2
    funext w
    by_cases h : w = v
    · subst h; simp
    · simp [h]
  | wedge _ _ ihx ihy =>
    rw [a3b_coe_wedge_c]
    convert hmul _ _ (Submodule.mul_mem_mul ihx ihy) using 2
    funext v
    simp only [Pi.add_apply, Nat.cast_add]
    ring

omit [CharZero K] in
/-- Products of block images of counted products, with their total weights. -/
theorem a4_c_mcp_mul {z z' : ExteriorAlgebra K (MultiSpace K W U U')} {α β α' β' : Fin e → ℕ}
    (h : ∃ (d : ℕ) (y : ⋀[K]^d (MultiSpace K W U U')), MultiCountedProduct d α β y ∧ (y : _) = z)
    (h' : ∃ (d : ℕ) (y : ⋀[K]^d (MultiSpace K W U U')),
      MultiCountedProduct d α' β' y ∧ (y : _) = z') :
    ∃ (d : ℕ) (y : ⋀[K]^d (MultiSpace K W U U')),
      MultiCountedProduct d (α + α') (β + β') y ∧ (y : _) = z * z' := by
  obtain ⟨d, y, hy, rfl⟩ := h
  obtain ⟨d', y', hy', rfl⟩ := h'
  exact ⟨_, _, MultiCountedProduct.wedge hy hy', a3b_coe_wedge_c y y'⟩

omit [CharZero K] in
theorem a4_c_mcp_prod_ofFn : ∀ (n : ℕ) (f : Fin n → ExteriorAlgebra K (MultiSpace K W U U'))
    (α β : Fin n → Fin e → ℕ),
    (∀ i, ∃ (d : ℕ) (y : ⋀[K]^d (MultiSpace K W U U')),
      MultiCountedProduct d (α i) (β i) y ∧ (y : _) = f i) →
    ∃ (d : ℕ) (y : ⋀[K]^d (MultiSpace K W U U')),
      MultiCountedProduct d (∑ i, α i) (∑ i, β i) y ∧ (y : _) = (List.ofFn f).prod
  | 0, _, _, _, _ => ⟨0, _, MultiCountedProduct.unit, by
      simp [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply]⟩
  | n + 1, f, α, β, h => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ, Fin.sum_univ_succ]
    exact a4_c_mcp_mul (h 0) (a4_c_mcp_prod_ofFn n _ _ _ fun i => h i.succ)

omit [CharZero K] in
theorem a4_c_mcp_prod_map_theta : ∀ (l : List ((v : Fin e) × U v × U' v)),
    ∃ (d : ℕ) (y : ⋀[K]^d (MultiSpace K W U U')),
      MultiCountedProduct d 0 0 y ∧
        (y : _) = (l.map fun p => blockTheta (K := K) (W := W) p.1 p.2.1 p.2.2).prod
  | [] => ⟨0, _, MultiCountedProduct.unit, by
      simp [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply]⟩
  | p :: l => by
    rw [List.map_cons, List.prod_cons, ← add_zero (0 : Fin e → ℕ)]
    refine a4_c_mcp_mul ⟨2, exteriorPower.map 2
      (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) p.1) (theta p.2.1 p.2.2), ?_, ?_⟩
      (a4_c_mcp_prod_map_theta l)
    · have := MultiCountedProduct.block (W := W) (U := U) (U' := U') p.1
        (CountedGeneratorProduct.theta (K := K) (W := W p.1) p.2.1 p.2.2)
      rwa [Pi.single_zero] at this
    · rw [exteriorPower.coe_map]; rfl

omit [CharZero K] in
/-- Regrouping block-ordered products of contractions and determinant-type factors into the
normal form, up to a scalar. -/
theorem a4_c_regroup {X : Fin e → Type*} (δ : (v : Fin e) → X v → ExteriorAlgebra K (MultiSpace K W U U'))
    (hδ : ∀ v x, ∃ i, δ v x ∈ ⋀[K]^i (MultiSpace K W U U')) (n : ℕ)
    (l : (v : Fin e) → List (U v × U' v)) (a : (v : Fin e) → Fin n → X v) :
    ∃ s : K, (List.ofFn fun v =>
        ((l v).map fun p => blockTheta (K := K) (W := W) v p.1 p.2).prod *
          (List.ofFn fun j => δ v (a v j)).prod).prod =
      s • (((List.ofFn fun v => (l v).map fun p => (⟨v, p⟩ : (v : Fin e) × U v × U' v)).flatten.map
          fun p => blockTheta (K := K) (W := W) p.1 p.2.1 p.2.2).prod *
        (List.ofFn fun j => (List.ofFn fun v => δ v (a v j)).prod).prod) := by
  set LL := (List.ofFn fun v => ((l v).map fun p => blockTheta (K := K) (W := W) v p.1 p.2) ++
    List.ofFn fun j => δ v (a v j)).flatten
  set RR := ((List.ofFn fun v => (l v).map fun p => (⟨v, p⟩ : (v : Fin e) × U v × U' v)).flatten.map
      fun p => blockTheta (K := K) (W := W) p.1 p.2.1 p.2.2) ++
    (List.ofFn fun j => List.ofFn fun v => δ v (a v j)).flatten
  have hL : (List.ofFn fun v =>
        ((l v).map fun p => blockTheta (K := K) (W := W) v p.1 p.2).prod *
          (List.ofFn fun j => δ v (a v j)).prod).prod = LL.prod := by
    simp only [LL, List.prod_flatten, List.map_ofFn, Function.comp_def, List.prod_append]
  have hR : ((List.ofFn fun v => (l v).map fun p => (⟨v, p⟩ : (v : Fin e) × U v × U' v)).flatten.map
          fun p => blockTheta (K := K) (W := W) p.1 p.2.1 p.2.2).prod *
        (List.ofFn fun j => (List.ofFn fun v => δ v (a v j)).prod).prod = RR.prod := by
    simp only [RR, List.prod_append, List.prod_flatten, List.map_ofFn, Function.comp_def]
  have hperm : RR.Perm LL := by
    rw [← Multiset.coe_eq_coe]
    simp only [RR, LL, List.map_flatten, List.map_ofFn, Function.comp_def, List.map_map,
      ← Multiset.coe_add, a4_c_coe_flatten_ofFn, a4_c_coe_ofFn, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
  obtain ⟨s, hs⟩ := a4_c_prod_perm hperm (by
    intro x hx
    simp only [RR, List.mem_append, List.mem_map, List.mem_flatten, List.mem_ofFn] at hx
    rcases hx with ⟨p, _, rfl⟩ | ⟨_, ⟨j, rfl⟩, hx⟩
    · refine ⟨2, ?_⟩
      rw [blockTheta, ← exteriorPower.coe_map]
      exact Subtype.mem _
    · obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hx
      exact hδ _ _)
  exact ⟨s, by rw [hL, hR, hs]⟩

omit [CharZero K] in
/-- For independent submodules `E`, the part of `⨆ i, V i` in `E χ`, with `V i ≤ E (g i)`, lies in
the sum of the `V i` with `g i = χ`. -/
theorem a4_c_inf_iSup_le_of_iSupIndep {M ι κ : Type*} [AddCommGroup M] [Module K M]
    (E : κ → Submodule K M) (hE : iSupIndep E) (V : ι → Submodule K M) (g : ι → κ)
    (hV : ∀ i, V i ≤ E (g i)) (χ : κ) :
    E χ ⊓ ⨆ i, V i ≤ ⨆ (i) (_ : g i = χ), V i := by
  classical
  rintro y ⟨hy0, hy⟩
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hy
  set a := ∑ i ∈ f.support with g i = χ, f i
  set b := ∑ i ∈ f.support with ¬ g i = χ, f i
  have hab : (f.sum fun _ x => x) = a + b := (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have ha : a ∈ ⨆ (i) (_ : g i = χ), V i :=
    Submodule.sum_mem _ fun i hi =>
      Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem (Finset.mem_filter.1 hi).2 (hf i))
  have haE : (⨆ (i) (_ : g i = χ), V i) ≤ E χ := iSup₂_le fun i hi => hi ▸ hV i
  have hbE : b ∈ E χ := by
    have : b = (f.sum fun _ x => x) - a := by rw [hab]; abel
    rw [this]
    exact Submodule.sub_mem _ hy0 (haE ha)
  have hb' : b ∈ ⨆ (χ' : κ) (_ : χ' ≠ χ), E χ' :=
    Submodule.sum_mem _ fun i hi =>
      Submodule.mem_iSup_of_mem (g i) (Submodule.mem_iSup_of_mem (Finset.mem_filter.1 hi).2 (hV i (hf i)))
  have hb0 : b = 0 := Submodule.disjoint_def.1 (hE χ) b hbE hb'
  rw [hab, hb0, add_zero]
  exact ha

omit [CharZero K] in
theorem a4_c_prod_ofFn_smul {A : Type*} [Ring A] [Algebra K A] :
    ∀ (n : ℕ) (s : Fin n → K) (z : Fin n → A),
      (List.ofFn fun i => s i • z i).prod = (∏ i, s i) • (List.ofFn z).prod
  | 0, _, _ => by simp
  | n + 1, s, z => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, a4_c_prod_ofFn_smul n,
      Fin.prod_univ_succ, smul_mul_smul_comm]

omit [CharZero K] in
/-- An ordered product over the blocks of scalar multiples of contraction products times `n`
determinant-type factors is a scalar multiple of a normal-form product. -/
theorem a4_c_ofFn_eq_normal {X : Fin e → Type*}
    (δ : (v : Fin e) → X v → ExteriorAlgebra K (MultiSpace K W U U'))
    (hδ : ∀ v x, ∃ i, δ v x ∈ ⋀[K]^i (MultiSpace K W U U')) (n : ℕ)
    (y : Fin e → ExteriorAlgebra K (MultiSpace K W U U'))
    (hy : ∀ v, ∃ (l : List (U v × U' v)) (a : Fin n → X v) (s : K),
      y v = s • (((l.map fun p => blockTheta (K := K) (W := W) v p.1 p.2).prod) *
        (List.ofFn fun j => δ v (a j)).prod)) :
    ∃ (l : List ((v : Fin e) × U v × U' v)) (a : Fin n → (v : Fin e) → X v) (s : K),
      (List.ofFn y).prod = s • ((l.map fun p => blockTheta (K := K) (W := W) p.1 p.2.1 p.2.2).prod *
        (List.ofFn fun j => (List.ofFn fun v => δ v (a j v)).prod).prod) := by
  choose l a s hs using hy
  obtain ⟨r, hr⟩ := a4_c_regroup δ hδ n l a
  refine ⟨(List.ofFn fun v => (l v).map fun p => (⟨v, p⟩ : (v : Fin e) × U v × U' v)).flatten,
    fun j v => a v j, (∏ v, s v) * r, ?_⟩
  rw [show y = fun v => s v • (((l v).map fun p => blockTheta (K := K) (W := W) v p.1 p.2).prod *
      (List.ofFn fun j => δ v (a v j)).prod) from funext hs, a4_c_prod_ofFn_smul, hr, smul_smul]


omit [CharZero K] in
theorem a4_c_block_detW_normal (v : Fin e) {n a b N : ℕ}
    {g : ⋀[K]^n (Space K (W v) (U v) (U' v))} (hg : CountedGeneratorProduct n a b g)
    (ha : a = N) (hb : b = 0) :
    ∃ (l : List (U v × U' v)) (x : Fin N → U v) (s : K),
      ExteriorAlgebra.map (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)
          (g : ExteriorAlgebra K (Space K (W v) (U v) (U' v))) =
        s • (((l.map fun p => blockTheta (K := K) (W := W) v p.1 p.2).prod) *
          (List.ofFn fun j => ExteriorAlgebra.map
            (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)
            ((detW (K := K) (W := W v) (U' := U' v) (x j) :
              ExteriorAlgebra K (Space K (W v) (U v) (U' v))))).prod) := by
  subst ha hb
  obtain ⟨l, x, x', s, hs⟩ := a4_c_counted_eq_smul hg
  refine ⟨l, x, s, ?_⟩
  rw [hs, map_smul, map_mul, map_mul, map_list_prod, map_list_prod, map_list_prod, List.ofFn_zero,
    List.map_nil, List.prod_nil, mul_one, List.map_map, List.map_ofFn]
  rfl

omit [CharZero K] in
theorem a4_c_block_detWDual_normal (v : Fin e) {n a b N : ℕ}
    {g : ⋀[K]^n (Space K (W v) (U v) (U' v))} (hg : CountedGeneratorProduct n a b g)
    (ha : a = 0) (hb : b = N) :
    ∃ (l : List (U v × U' v)) (x : Fin N → U' v) (s : K),
      ExteriorAlgebra.map (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)
          (g : ExteriorAlgebra K (Space K (W v) (U v) (U' v))) =
        s • (((l.map fun p => blockTheta (K := K) (W := W) v p.1 p.2).prod) *
          (List.ofFn fun j => ExteriorAlgebra.map
            (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)
            ((detWDual (K := K) (W := W v) (U := U v) (x j) :
              ExteriorAlgebra K (Space K (W v) (U v) (U' v))))).prod) := by
  subst ha hb
  obtain ⟨l, x, x', s, hs⟩ := a4_c_counted_eq_smul hg
  refine ⟨l, x', s, ?_⟩
  rw [hs, map_smul, map_mul, map_mul, map_list_prod, map_list_prod, map_list_prod, List.ofFn_zero,
    List.map_nil, List.prod_nil, mul_one, List.map_map, List.map_ofFn]
  rfl

omit [CharZero K] [∀ v, FiniteDimensional K (W v)] in
theorem a4_c_map_single_mem_exteriorPower (v : Fin e) {n : ℕ}
    (g : ⋀[K]^n (Space K (W v) (U v) (U' v))) :
    ExteriorAlgebra.map (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)
        (g : ExteriorAlgebra K (Space K (W v) (U v) (U' v))) ∈ ⋀[K]^n (MultiSpace K W U U') := by
  rw [← exteriorPower.coe_map]
  exact Subtype.mem _

omit [CharZero K] in
/-- An ordered product over the blocks of images of normal-form counted products of one weight
`c` lies in the span of the normal products. -/
theorem a4_c_ofFn_mem_span_normal (c : ℤ) (n : Fin e → ℕ)
    (y : Fin e → ExteriorAlgebra K (MultiSpace K W U U'))
    (hy : ∀ v, ∃ (a b : ℕ) (g : ⋀[K]^(n v) (Space K (W v) (U v) (U' v))), (a : ℤ) - b = c ∧
      (a = 0 ∨ b = 0) ∧ CountedGeneratorProduct (n v) a b g ∧
      ExteriorAlgebra.map (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)
        (g : ExteriorAlgebra K (Space K (W v) (U v) (U' v))) = y v) :
    (List.ofFn y).prod ∈
      Submodule.span K (centreNormalProducts (K := K) (W := W) (U := U) (U' := U')) := by
  rcases le_or_gt 0 c with hc | hc
  · obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hc
    obtain ⟨l, x, s, hs⟩ := a4_c_ofFn_eq_normal
      (fun v (u : U v) => ExteriorAlgebra.map
        (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)
        ((detW (K := K) (W := W v) (U' := U' v) u : ExteriorAlgebra K (Space K (W v) (U v) (U' v)))))
      (fun v u => ⟨_, a4_c_map_single_mem_exteriorPower v _⟩) N y (fun v => by
        obtain ⟨a, b, g, hab, h0, hg, hgy⟩ := hy v
        rw [← hgy]
        exact a4_c_block_detW_normal v hg (by omega) (by omega))
    rw [hs]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨l, N, x, rfl⟩))
  · obtain ⟨N, hN⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 hc.le)
    obtain ⟨l, x, s, hs⟩ := a4_c_ofFn_eq_normal
      (fun v (u : U' v) => ExteriorAlgebra.map
        (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)
        ((detWDual (K := K) (W := W v) (U := U v) u :
          ExteriorAlgebra K (Space K (W v) (U v) (U' v)))))
      (fun v u => ⟨_, a4_c_map_single_mem_exteriorPower v _⟩) N y (fun v => by
        obtain ⟨a, b, g, hab, h0, hg, hgy⟩ := hy v
        rw [← hgy]
        exact a4_c_block_detWDual_normal v hg (by omega) (by omega))
    rw [hs]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨l, N, x, rfl⟩))


omit [CharZero K] in
/-- Every normal product is the coercion of a counted product of constant weight. -/
theorem a4_c_normal_mem_iSup (y : ExteriorAlgebra K (MultiSpace K W U U'))
    (hy : y ∈ centreNormalProducts (K := K) (W := W) (U := U) (U' := U')) :
    ∃ (d : ℕ) (z : ⋀[K]^d (MultiSpace K W U U')),
      z ∈ constWeightDegree (K := K) (W := W) (U := U) (U' := U') d ∧ (z : _) = y := by
  have hθ := fun l => a4_c_mcp_prod_map_theta (K := K) (W := W) (U := U) (U' := U') l
  rcases hy with ⟨l, c, x, rfl⟩ | ⟨l, c, x, rfl⟩
  · have hD : ∀ j, ∃ (d : ℕ) (y : ⋀[K]^d (MultiSpace K W U U')),
        MultiCountedProduct d (∑ i : Fin e, Pi.single i 1) (∑ _i : Fin e, 0) y ∧
          (y : _) = multiDetW (K := K) (W := W) (U' := U') (x j) := fun j =>
      a4_c_mcp_prod_ofFn e _ _ _ fun i => ⟨_, _, by
        simpa only [Pi.single_zero] using MultiCountedProduct.block (W := W) (U := U) (U' := U') i
          (CountedGeneratorProduct.detW (K := K) (W := W i) (U' := U' i) (x j i)),
        exteriorPower.coe_map _ _⟩
    obtain ⟨d, z, hz, hzy⟩ := a4_c_mcp_mul (hθ l) (a4_c_mcp_prod_ofFn c _ _ _ hD)
    refine ⟨d, z, Submodule.subset_span ⟨c, _, _, fun v => ?_, hz⟩, hzy⟩
    simp [Finset.sum_apply, Pi.single_apply]
  · have hD : ∀ j, ∃ (d : ℕ) (y : ⋀[K]^d (MultiSpace K W U U')),
        MultiCountedProduct d (∑ _i : Fin e, 0) (∑ i : Fin e, Pi.single i 1) y ∧
          (y : _) = multiDetWDual (K := K) (W := W) (U := U) (x j) := fun j =>
      a4_c_mcp_prod_ofFn e _ _ _ fun i => ⟨_, _, by
        simpa only [Pi.single_zero] using MultiCountedProduct.block (W := W) (U := U) (U' := U') i
          (CountedGeneratorProduct.detWDual (K := K) (W := W i) (U := U i) (x j i)),
        exteriorPower.coe_map _ _⟩
    obtain ⟨d, z, hz, hzy⟩ := a4_c_mcp_mul (hθ l) (a4_c_mcp_prod_ofFn c _ _ _ hD)
    refine ⟨d, z, Submodule.subset_span ⟨-c, _, _, fun v => ?_, hz⟩, hzy⟩
    simp [Finset.sum_apply, Pi.single_apply]

theorem spec_a4_constWeightDegree_eq_normal_aux (k : ℕ) :
    Submodule.map (⋀[K]^k (MultiSpace K W U U')).subtype
        (constWeightDegree (K := K) (W := W) (U := U) (U' := U') k) =
      ⋀[K]^k (MultiSpace K W U U') ⊓
        Submodule.span K (centreNormalProducts (K := K) (W := W) (U := U) (U' := U')) := by
  classical
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap, constWeightDegree, Submodule.span_le]
    rintro x ⟨c, α, β, hc, hx⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, Submodule.coe_subtype]
    refine ⟨x.2, ?_⟩
    set B : (v : Fin e) → ℕ → ℤ → Submodule K (ExteriorAlgebra K (MultiSpace K W U U')) :=
      fun v n c => Submodule.span K
        (⇑((ExteriorAlgebra.map
            (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)).toLinearMap ∘ₗ
          (⋀[K]^n (Space K (W v) (U v) (U' v))).subtype) ''
          {g | ∃ a b : ℕ, (a : ℤ) - b = c ∧ CountedGeneratorProduct n a b g}) with hB
    have hBdeg : ∀ v n c, B v n c ≤ ⋀[K]^n (MultiSpace K W U U') := by
      intro v n c
      rw [hB, Submodule.span_le]
      rintro _ ⟨g, _, rfl⟩
      exact a4_c_map_single_mem_exteriorPower v g
    have hB1 : ∀ v, (1 : ExteriorAlgebra K (MultiSpace K W U U')) ∈ B v 0 0 := by
      intro v
      refine Submodule.subset_span ⟨_, ⟨0, 0, by simp, CountedGeneratorProduct.unit⟩, ?_⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        AlgHom.toLinearMap_apply, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply,
        map_one]
    have hBmul : ∀ v n m c c', B v n c * B v m c' ≤ B v (n + m) (c + c') := by
      intro v n m c c'
      rw [hB, Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨_, ⟨g, ⟨a, b, hab, hg⟩, rfl⟩, _, ⟨g', ⟨a', b', hab', hg'⟩, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨exteriorPower.wedge K _ n m g g',
        ⟨a + a', b + b', by push_cast; omega, hg.wedge hg'⟩, ?_⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        AlgHom.toLinearMap_apply, a3b_coe_wedge_c, map_mul]
    have hxR := a4_c_mem_of_multiCountedProduct
      (fun w => ⨆ d : Fin e → ℕ, (List.ofFn fun v => B v (d v) (w v)).prod) ?_ ?_ ?_ hx
    · have hw : (fun v => (α v : ℤ) - β v) = fun _ => c := funext hc
      rw [hw] at hxR
      suffices H : (⨆ d : Fin e → ℕ, (List.ofFn fun v => B v (d v) c).prod) ≤
          Submodule.span K (centreNormalProducts (K := K) (W := W) (U := U) (U' := U')) from H hxR
      refine iSup_le fun d => ?_
      have hBn : ∀ v, B v (d v) c ≤ Submodule.span K
          {z | ∃ (a b : ℕ) (g : ⋀[K]^(d v) (Space K (W v) (U v) (U' v))), (a : ℤ) - b = c ∧
            (a = 0 ∨ b = 0) ∧ CountedGeneratorProduct (d v) a b g ∧
            ExteriorAlgebra.map (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)
              (g : ExteriorAlgebra K (Space K (W v) (U v) (U' v))) = z} := by
        intro v
        simp only [hB]
        rw [Submodule.span_image, spec_a4_counted_span_normal_aux, ← Submodule.span_image]
        refine Submodule.span_mono ?_
        rintro _ ⟨g, ⟨a, b, hab, h0, hg⟩, rfl⟩
        exact ⟨a, b, g, hab, h0, hg, rfl⟩
      refine (a3b_prod_ofFn_mono _ _ _ hBn).trans ((a4_c_prod_ofFn_span_le _ _).trans ?_)
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      exact a4_c_ofFn_mem_span_normal c d y hy
    · refine Submodule.mem_iSup_of_mem 0 (Submodule.one_le.mp
        (a3b_one_le_prod_ofFn _ _ fun v => Submodule.one_le.mpr (hB1 v)))
    · intro v n a b g hg
      refine Submodule.mem_iSup_of_mem (Pi.single v n) (a3b_mem_prod_ofFn_of_mem _ _ v ?_ ?_)
      · intro w hw
        simp only [Pi.single_eq_of_ne hw]
        exact Submodule.one_le.mpr (hB1 w)
      · simp only [Pi.single_eq_same]
        exact Submodule.subset_span ⟨g, ⟨a, b, rfl, hg⟩, rfl⟩
    · intro a b
      rw [Submodule.iSup_mul]
      refine iSup_le fun d => ?_
      rw [Submodule.mul_iSup]
      refine iSup_le fun d' => ?_
      rw [a3b_prod_ofFn_mul _ _ _ fun i j => a3b_submodule_commute (hBdeg _ _ _) (hBdeg _ _ _)]
      refine le_trans ?_ (le_iSup _ (d + d'))
      exact a3b_prod_ofFn_mono _ _ _ fun v => hBmul v _ _ _ _
  · have hle : Submodule.span K (centreNormalProducts (K := K) (W := W) (U := U) (U' := U')) ≤
        ⨆ d, Submodule.map (⋀[K]^d (MultiSpace K W U U')).subtype
          (constWeightDegree (K := K) (W := W) (U := U) (U' := U') d) := by
      rw [Submodule.span_le]
      intro y hy
      obtain ⟨d, z, hz, rfl⟩ := a4_c_normal_mem_iSup y hy
      exact Submodule.mem_iSup_of_mem d ⟨z, hz, rfl⟩
    refine (inf_le_inf_left _ hle).trans ?_
    refine (a4_c_inf_iSup_le_of_iSupIndep (fun i => ⋀[K]^i (MultiSpace K W U U'))
      (DirectSum.Decomposition.isInternal _).submodule_iSupIndep _ id
      (fun d => Submodule.map_subtype_le _ _) k).trans ?_
    exact (iSup_iSup_eq_left (f := fun d (_ : d = k) => Submodule.map
      (⋀[K]^d (MultiSpace K W U U')).subtype
      (constWeightDegree (K := K) (W := W) (U := U) (U' := U') d))).le

end Main

theorem spec_a4_constWeightDegree_fin_one_aux {W U U' : Fin 1 → Type*}
    [∀ v, AddCommGroup (W v)] [∀ v, Module K (W v)] [∀ v, FiniteDimensional K (W v)]
    [∀ v, AddCommGroup (U v)] [∀ v, Module K (U v)]
    [∀ v, AddCommGroup (U' v)] [∀ v, Module K (U' v)] (k : ℕ) :
    constWeightDegree (K := K) (W := W) (U := U) (U' := U') k =
      multiGeneratedDegree (K := K) (W := W) (U := U) (U' := U') k := by
  rw [spec_a4_multiGeneratedDegree_eq_span_counted_aux k, constWeightDegree]
  congr 1
  ext x
  constructor
  · rintro ⟨_, α, β, _, hx⟩
    exact ⟨α, β, hx⟩
  · rintro ⟨α, β, hx⟩
    refine ⟨(α 0 : ℤ) - β 0, α, β, fun v => ?_, hx⟩
    rw [Subsingleton.elim v 0]

omit [CharZero K] in
theorem a4_l2_ιMulti_ne_zero {M : Type*} [AddCommGroup M] [Module K M] {n : ℕ} {v : Fin n → M}
    (hv : LinearIndependent K v) : exteriorPower.ιMulti K n v ≠ 0 := by
  have h := (exteriorPower.ιMulti_family_linearIndependent_field (n := n) hv).ne_zero
    (Set.powersetCard.ofFinEmbEquiv (RelEmbedding.refl ((· ≤ ·) : Fin n → Fin n → Prop)))
  rwa [exteriorPower.ιMulti_family, Equiv.symm_apply_apply] at h

omit [CharZero K] in
theorem a4_detW_one_ne_zero {W₀ U₀' : Type*} [AddCommGroup W₀] [Module K W₀]
    [FiniteDimensional K W₀] [AddCommGroup U₀'] [Module K U₀'] :
    detW (K := K) (W := W₀) (U' := U₀') (1 : K) ≠ 0 := by
  rw [detW_eq]
  apply a4_l2_ιMulti_ne_zero
  have hj : LinearMap.ker ((LinearMap.inl K (W₀ ⊗[K] K) (Dual K W₀ ⊗[K] U₀')).comp
      (TensorProduct.rid K W₀).symm.toLinearMap) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact LinearMap.inl_injective.comp (TensorProduct.rid K W₀).symm.injective
  exact (Module.finBasis K W₀).linearIndependent.map' _ hj

theorem spec_a4_nonconstant_not_invariant_aux :
    (exteriorPower.map (finrank K K) (LinearMap.single K (fun _ : Fin 2 => Space K K K K) 0)
        (detW (K := K) (W := K) (U' := K) (1 : K)) :
          ⋀[K]^(finrank K K) (MultiSpace K (fun _ : Fin 2 => K) (fun _ => K) (fun _ => K))) ∈
      multiGeneratedDegree (K := K) (W := fun _ : Fin 2 => K) (U := fun _ => K) (U' := fun _ => K)
        (finrank K K) ∧
    (exteriorPower.map (finrank K K) (LinearMap.single K (fun _ : Fin 2 => Space K K K K) 0)
        (detW (K := K) (W := K) (U' := K) (1 : K)) :
          ⋀[K]^(finrank K K) (MultiSpace K (fun _ : Fin 2 => K) (fun _ => K) (fun _ => K))) ∉
      (⨅ f : {f : (v : Fin 2) → Module.End K K // ∑ v, LinearMap.trace K K (f v) = 0},
        LinearMap.ker (exteriorDer (finrank K K)
          (LinearMap.piMap fun v => multiplicityLie K K K K (f.1 v)))) := by
  have hx : MultiCountedProduct (K := K) (W := fun _ : Fin 2 => K) (U := fun _ => K)
      (U' := fun _ => K) (finrank K K) (Pi.single 0 1) (Pi.single 0 0)
      (exteriorPower.map (finrank K K) (LinearMap.single K (fun _ : Fin 2 => Space K K K K) 0)
        (detW (K := K) (W := K) (U' := K) (1 : K))) :=
    MultiCountedProduct.block 0 (CountedGeneratorProduct.detW 1)
  refine ⟨Submodule.subset_span
    (MultiGeneratorProduct.block 0 (GeneratorProduct.detW (1 : K))), fun hmem => ?_⟩
  let f₀ : {f : (v : Fin 2) → Module.End K K // ∑ v, LinearMap.trace K K (f v) = 0} :=
    ⟨![LinearMap.id, -LinearMap.id], by simp [Fin.sum_univ_two]⟩
  have h0 := LinearMap.mem_ker.mp (Submodule.mem_iInf _ |>.mp hmem f₀)
  rw [spec_a4_exteriorDer_multiCounted_aux hx] at h0
  have hsum : (∑ v : Fin 2, (((Pi.single 0 1 : Fin 2 → ℕ) v : K) - (Pi.single 0 0 : Fin 2 → ℕ) v) *
      LinearMap.trace K K (f₀.1 v)) = 1 := by
    simp [f₀, Fin.sum_univ_two]
  rw [hsum, one_smul] at h0
  refine a4_detW_one_ne_zero (K := K) (W₀ := K) (U₀' := K) ?_
  have hinj : Function.Injective (LinearMap.single K (fun _ : Fin 2 => Space K K K K) 0) :=
    fun a b h => by simpa using congr_fun h 0
  exact exteriorPower.map_injective_field hinj (by rw [h0, map_zero])

end HodgeLean.Foundations
