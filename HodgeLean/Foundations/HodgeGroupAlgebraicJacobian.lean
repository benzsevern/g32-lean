import HodgeLean.Foundations.MatrixAlgGroupLie

/-! # The Jacobian bound in characteristic zero (Track G2, helper for the Lie bridge)

`g2l_linearIndependent_grad`: modulo a prime `P` preserved by derivations `δ_1, …, δ_N`, with
coordinates `s_l` whose Jacobian `det (δ_j s_l)` is a unit modulo `P`, and with every
algebraically independent family of `R ⧸ P` of size at most `N`, algebraically independent
elements have linearly independent gradients. The proof extends the given family by coordinates
`s_l` to a maximal algebraically independent family; every other `s_l` satisfies a relation of
least degree, whose derivative in `s_l` does not vanish (characteristic zero), so the gradients
of the extended family span. `g2l_card_le_of_jacobian` is the resulting dimension bound.

Sources: Matsumura, *Commutative Ring Theory*, §26 (derivations and separability); Borel,
*Linear Algebraic Groups*, 2nd ed., AG.15 (separating transcendence bases).
-/

noncomputable section
set_option maxHeartbeats 400000

namespace HodgeLean.Foundations

open MvPolynomial

variable {k : Type*} [Field k]

/-- In characteristic zero, a polynomial with `∂F/∂x_i = 0` does not depend on `x_i`. -/
theorem g2l_aeval_eq_of_pderiv_eq_zero [CharZero k] {σ : Type*} [DecidableEq σ]
    {B : Type*} [CommRing B] [Algebra k B] (F : MvPolynomial σ k) (i : σ)
    (hF : pderiv i F = 0) (x x' : σ → B) (hx : ∀ v, v ≠ i → x v = x' v) :
    aeval x F = aeval x' F := by
  have hsupp : ∀ m ∈ F.support, m i = 0 := by
    intro m hm
    by_contra hne
    have hle : Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    have hc := coeff_pderiv (i := i) F (m - Finsupp.single i 1)
    rw [hF, AddMonoidAlgebra.coeff_zero, tsub_add_cancel_of_le hle] at hc
    have h1 : (((m - Finsupp.single i (1 : ℕ)) i : ℕ) : k) + 1 ≠ 0 :=
      Nat.cast_add_one_ne_zero _
    exact (mem_support_iff.mp hm) ((mul_eq_zero.mp hc.symm).resolve_right h1)
  rw [aeval_eq_eval₂Hom, aeval_eq_eval₂Hom, coe_eval₂Hom, coe_eval₂Hom, eval₂_eq, eval₂_eq]
  refine Finset.sum_congr rfl fun m hm => ?_
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  have : v ≠ i := fun h => (Finsupp.mem_support_iff.mp hv) (h ▸ hsupp m hm)
  rw [hx v this]

/-- The chain rule for a derivation along a polynomial expression, in `K`-vector form. -/
theorem g2l_grad_aeval {R K : Type*} [CommRing R] [Algebra k R] [Field K] (π : R →+* K) {N : ℕ}
    (δ : Fin N → Derivation k R R) {σ : Type*} [Fintype σ] (z : σ → R) (F : MvPolynomial σ k) :
    (fun j => π (δ j (aeval z F))) = ∑ v, π (aeval z (pderiv v F)) • fun j => π (δ j (z v)) := by
  funext j
  rw [g1s_derivation_aeval, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_mul, Pi.smul_apply, smul_eq_mul]

/-- **Jacobian criterion, characteristic zero.** Let `P` be a prime of `R`, `δ_1, …, δ_N`
derivations preserving `P`, and `s_1, …, s_N` with `det (δ_j s_l) ∉ P`, and suppose every
algebraically independent family in `R ⧸ P` has at most `N` members. Then the gradients
`(δ_j y_i)_j` of elements `y_i` algebraically independent modulo `P` are linearly independent
over the fraction field of `R ⧸ P`. -/
theorem g2l_linearIndependent_grad [CharZero k] {R : Type*} [CommRing R] [Algebra k R]
    (P : Ideal R) [hP : P.IsPrime] {N : ℕ} (δ : Fin N → Derivation k R R)
    (hδ : ∀ j, ∀ x ∈ P, δ j x ∈ P) (s : Fin N → R)
    (hdet : (Matrix.of fun j l => δ j (s l)).det ∉ P)
    (htr : ∀ (J : Type) [Fintype J] (z : J → R ⧸ P), AlgebraicIndependent k z →
      Fintype.card J ≤ N)
    {m : ℕ} (y : Fin m → R) (hy : AlgebraicIndependent k fun i => Ideal.Quotient.mk P (y i)) :
    LinearIndependent (FractionRing (R ⧸ P)) fun i (j : Fin N) =>
      algebraMap (R ⧸ P) (FractionRing (R ⧸ P)) (Ideal.Quotient.mk P (δ j (y i))) := by
  classical
  set K := FractionRing (R ⧸ P)
  let π : R →+* K := (algebraMap (R ⧸ P) K).comp (Ideal.Quotient.mk P)
  have hπ : ∀ x, π x = 0 ↔ x ∈ P := fun x => by
    simp only [π, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ P) K), Ideal.Quotient.eq_zero_iff_mem]
  let grad : R → Fin N → K := fun x j => π (δ j x)
  have hgradP : ∀ x ∈ P, grad x = 0 := fun x hx => funext fun j => (hπ _).mpr (hδ j x hx)
  let fam : Fin m ⊕ Fin N → R := Sum.elim y s
  let famb : Fin m ⊕ Fin N → R ⧸ P := fun v => Ideal.Quotient.mk P (fam v)
  let good : Set (Fin m ⊕ Fin N) → Prop := fun J =>
    Set.range Sum.inl ⊆ J ∧ AlgebraicIndepOn k famb J
  have hgood0 : good (Set.range Sum.inl) := by
    refine ⟨le_rfl, ?_⟩
    let e := Equiv.ofInjective (Sum.inl : Fin m → Fin m ⊕ Fin N) Sum.inl_injective
    have := hy.comp e.symm e.symm.injective
    convert this using 1
    funext v
    simp only [Function.comp_apply, famb, fam]
    rw [← Equiv.apply_ofInjective_symm Sum.inl_injective v]
    rfl
  have : Nonempty {J // good J} := ⟨⟨_, hgood0⟩⟩
  obtain ⟨⟨J, hJ⟩, hJmax⟩ := Finite.exists_max (fun J : {J // good J} => J.1.ncard)
  have hmax : ∀ x ∉ J, ¬ AlgebraicIndepOn k famb (insert x J) := by
    intro x hx hind
    have hgood' : good (insert x J) := ⟨hJ.1.trans (Set.subset_insert _ _), hind⟩
    have := hJmax ⟨_, hgood'⟩
    simp only at this
    rw [Set.ncard_insert_of_notMem hx (Set.toFinite J)] at this
    omega
  let G : J → Fin N → K := fun v => grad (fam v)
  have hspan_s : ∀ l, grad (s l) ∈ Submodule.span K (Set.range G) := by
    intro l
    by_cases hl : Sum.inr l ∈ J
    · exact Submodule.subset_span ⟨⟨_, hl⟩, rfl⟩
    have hni := hmax _ hl
    rw [AlgebraicIndepOn.insert_iff hl] at hni
    let zb : Option J → R ⧸ P := fun o => o.elim (famb (Sum.inr l)) (fun v => famb v)
    have hnot : ¬ AlgebraicIndependent k zb := by
      intro h
      rw [AlgebraicIndependent.option_iff] at h
      apply hni
      refine ⟨hJ.2, ?_⟩
      rw [Set.image_eq_range]
      exact h.2
    rw [algebraicIndependent_iff] at hnot
    push Not at hnot
    obtain ⟨F, hF0, hFne⟩ := hnot
    have hex : ∃ d, ∃ F : MvPolynomial (Option J) k, F ≠ 0 ∧ aeval zb F = 0 ∧
        F.totalDegree = d := ⟨_, F, hFne, hF0, rfl⟩
    obtain ⟨F0, hF0ne, hF0z, hF0d⟩ := Nat.find_spec hex
    have hmin : ∀ F' : MvPolynomial (Option J) k, F' ≠ 0 → aeval zb F' = 0 →
        Nat.find hex ≤ F'.totalDegree := fun F' h1 h2 => Nat.find_min' hex ⟨F', h1, h2, rfl⟩
    have hinj : Function.Injective (algebraMap k (R ⧸ P)) := (algebraMap k (R ⧸ P)).injective
    have hpd : aeval zb (pderiv none F0) ≠ 0 := by
      intro hz
      by_cases hpd0 : pderiv none F0 = 0
      · let F' : MvPolynomial J k := aeval (fun o : Option J => o.elim 0 X) F0
        have hren : rename some F' = F0 := by
          rw [comp_aeval_apply]
          conv_rhs => rw [← aeval_X_left_apply F0]
          refine g2l_aeval_eq_of_pderiv_eq_zero F0 none hpd0 _ _ fun o ho => ?_
          cases o with
          | none => exact absurd rfl ho
          | some v => simp
        have hF'ne : F' ≠ 0 := fun h => hF0ne (by rw [← hren, h, map_zero])
        have hF'z : aeval (fun v : J => famb v) F' = 0 := by
          rw [comp_aeval_apply, ← hF0z]
          refine g2l_aeval_eq_of_pderiv_eq_zero F0 none hpd0 _ _ fun o ho => ?_
          cases o with
          | none => exact absurd rfl ho
          | some v => simp [zb]
        exact hF'ne ((algebraicIndependent_iff.mp hJ.2) F' hF'z)
      · have hd0 : Nat.find hex ≠ 0 := by
          intro h0
          rw [h0] at hF0d
          rw [totalDegree_eq_zero_iff_eq_C.mp hF0d, aeval_C] at hF0z
          rw [map_eq_zero_iff _ hinj] at hF0z
          exact hF0ne (by rw [totalDegree_eq_zero_iff_eq_C.mp hF0d, hF0z, C_0])
        have hlt : (pderiv none F0).totalDegree < Nat.find hex :=
          lt_of_le_of_lt (hF0d ▸ g1s_totalDegree_pderiv_le none F0) (by omega)
        exact absurd (hmin _ hpd0 hz) (not_le.mpr hlt)
    let z : Option J → R := fun o => o.elim (s l) (fun v => fam v)
    have hmk : ∀ F : MvPolynomial (Option J) k,
        Ideal.Quotient.mk P (aeval z F) = aeval zb F := by
      intro F
      rw [← Ideal.Quotient.mkₐ_eq_mk k, comp_aeval_apply]
      have : (fun i => Ideal.Quotient.mkₐ k P (z i)) = zb := by
        funext o
        cases o <;> rfl
      rw [this]
    have hFP : aeval z F0 ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, hmk]
      exact hF0z
    have hrel := g2l_grad_aeval π δ z F0
    have h0 : (fun j => π (δ j (aeval z F0))) = 0 := hgradP _ hFP
    rw [h0, Fintype.sum_option] at hrel
    have hc : π (aeval z (pderiv none F0)) ≠ 0 := by
      rw [Ne, hπ, ← Ideal.Quotient.eq_zero_iff_mem, hmk]
      exact hpd
    have hsl : grad (s l) = -(π (aeval z (pderiv none F0)))⁻¹ •
        ∑ v : J, π (aeval z (pderiv (some v) F0)) • grad (fam v) := by
      have h1 := hrel.symm
      rw [add_eq_zero_iff_eq_neg] at h1
      have h2 : grad (s l) = (π (aeval z (pderiv none F0)))⁻¹ •
          (π (aeval z (pderiv none F0)) • grad (s l)) := by
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [h2]
      change _ • (_ • (fun j => π (δ j (z none)))) = _
      rw [h1, smul_neg, neg_smul]
      rfl
    rw [hsl]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun v _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩))
  have hsind : LinearIndependent K (fun l => grad (s l)) := by
    have hdetK : (Matrix.of fun l j => π (δ j (s l))).det ≠ 0 := by
      have : (Matrix.of fun l j => π (δ j (s l))) =
          Matrix.transpose (π.mapMatrix (Matrix.of fun j l => δ j (s l))) := by
        ext l j
        rfl
      rw [this, Matrix.det_transpose, ← RingHom.map_det, Ne, hπ]
      exact hdet
    exact Matrix.linearIndependent_rows_of_det_ne_zero hdetK
  have htop : Submodule.span K (Set.range fun l => grad (s l)) = ⊤ :=
    hsind.span_eq_top_of_card_eq_finrank' (by simp)
  have hGtop : ⊤ ≤ Submodule.span K (Set.range G) := by
    rw [← htop, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    exact hspan_s l
  have hcard : Fintype.card J ≤ Module.finrank K (Fin N → K) := by
    rw [Module.finrank_fin_fun]
    exact htr J _ hJ.2
  have hGind := linearIndependent_of_top_le_span_of_card_le_finrank hGtop hcard
  have := hGind.comp (fun i : Fin m => (⟨Sum.inl i, hJ.1 ⟨i, rfl⟩⟩ : J))
    (fun i i' h => Sum.inl_injective (congrArg Subtype.val h))
  convert this using 1
  funext i j
  rfl

/-- **Dimension bound from the Jacobian.** In the setting of `g2l_linearIndependent_grad`, if the
gradients of `y_1, …, y_m` factor, modulo `P`, through `r` vectors (`δ_j y_i ≡ Σ_q c_jq e_qi`),
then `m ≤ r`. -/
theorem g2l_card_le_of_jacobian [CharZero k] {R : Type*} [CommRing R] [Algebra k R]
    (P : Ideal R) [P.IsPrime] {N : ℕ} (δ : Fin N → Derivation k R R)
    (hδ : ∀ j, ∀ x ∈ P, δ j x ∈ P) (s : Fin N → R)
    (hdet : (Matrix.of fun j l => δ j (s l)).det ∉ P)
    (htr : ∀ (J : Type) [Fintype J] (z : J → R ⧸ P), AlgebraicIndependent k z →
      Fintype.card J ≤ N)
    {m r : ℕ} (y : Fin m → R) (hy : AlgebraicIndependent k fun i => Ideal.Quotient.mk P (y i))
    (c : Fin N → Fin r → R) (e : Fin r → Fin m → R)
    (hrel : ∀ j i, δ j (y i) - ∑ q, c j q * e q i ∈ P) : m ≤ r := by
  classical
  set K := FractionRing (R ⧸ P)
  let π : R →+* K := (algebraMap (R ⧸ P) K).comp (Ideal.Quotient.mk P)
  have hπ : ∀ x, π x = 0 ↔ x ∈ P := fun x => by
    simp only [π, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ P) K), Ideal.Quotient.eq_zero_iff_mem]
  have hind := g2l_linearIndependent_grad P δ hδ s hdet htr y hy
  let col : Fin r → Fin N → K := fun q j => π (c j q)
  have hsub : Set.range (fun i (j : Fin N) =>
      algebraMap (R ⧸ P) K (Ideal.Quotient.mk P (δ j (y i)))) ≤
      Submodule.span K (Set.range col) := by
    rintro _ ⟨i, rfl⟩
    have : (fun j : Fin N => algebraMap (R ⧸ P) K (Ideal.Quotient.mk P (δ j (y i)))) =
        ∑ q, π (e q i) • col q := by
      funext j
      have h := (hπ _).mpr (hrel j i)
      rw [map_sub, sub_eq_zero, map_sum] at h
      change π (δ j (y i)) = _
      rw [h, Finset.sum_apply]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_mul, Pi.smul_apply, smul_eq_mul, mul_comm]
    change (fun j : Fin N => algebraMap (R ⧸ P) K (Ideal.Quotient.mk P (δ j (y i)))) ∈ _
    rw [this]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
  have h := linearIndependent_le_span_aux' _ hind (Set.range col) hsub
  simp only [Fintype.card_fin] at h
  exact h.trans ((Fintype.card_range_le col).trans (by simp))

end HodgeLean.Foundations
