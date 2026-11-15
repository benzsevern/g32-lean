import HodgeLean.Foundations.AnalyticDivisorAlgebraic9

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic10

open Filter Polynomial Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6

theorem spec_simultaneous_coefficient_representatives_aux {n : ℕ}
    (P g : Polynomial (AnalyticGerm n)) :
    ∃ (a b : ℕ → (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ)),
      U ∈ nhds (0 : Fin n → ℂ) ∧
      (∀ j, AnalyticOnNhd ℂ (a j) U) ∧ (∀ j, AnalyticOnNhd ℂ (b j) U) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j) = (P.coeff j).1) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (b j) = (g.coeff j).1) := by
  classical
  choose a ha hga using fun j ↦ (P.coeff j).2
  choose b hb hgb using fun j ↦ (g.coeff j).2
  have hEA : ∀ᶠ x in nhds (0 : Fin n → ℂ), ∀ j ∈ P.support, AnalyticAt ℂ (a j) x :=
    P.support.eventually_all.mpr fun j _ ↦ (ha j).eventually_analyticAt
  have hEB : ∀ᶠ x in nhds (0 : Fin n → ℂ), ∀ j ∈ g.support, AnalyticAt ℂ (b j) x :=
    g.support.eventually_all.mpr fun j _ ↦ (hb j).eventually_analyticAt
  obtain ⟨U, hU, hAU⟩ := (hEA.and hEB).exists_mem
  let a' : ℕ → (Fin n → ℂ) → ℂ := fun j ↦ if j ∈ P.support then a j else 0
  let b' : ℕ → (Fin n → ℂ) → ℂ := fun j ↦ if j ∈ g.support then b j else 0
  have haU : ∀ j, AnalyticOnNhd ℂ (a' j) U := by
    intro j x hx
    by_cases hj : j ∈ P.support
    · change AnalyticAt ℂ (if j ∈ P.support then a j else 0) x
      rw [if_pos hj]
      exact (hAU x hx).1 j hj
    · change AnalyticAt ℂ (if j ∈ P.support then a j else 0) x
      rw [if_neg hj]
      exact analyticAt_const
  have hbU : ∀ j, AnalyticOnNhd ℂ (b' j) U := by
    intro j x hx
    by_cases hj : j ∈ g.support
    · change AnalyticAt ℂ (if j ∈ g.support then b j else 0) x
      rw [if_pos hj]
      exact (hAU x hx).2 j hj
    · change AnalyticAt ℂ (if j ∈ g.support then b j else 0) x
      rw [if_neg hj]
      exact analyticAt_const
  refine ⟨a', b', U, hU, haU, hbU, ?_, ?_⟩
  · intro j
    by_cases hj : j ∈ P.support
    · dsimp [a']
      rw [if_pos hj]
      exact hga j
    · have hc : P.coeff j = 0 := by simpa [Polynomial.mem_support_iff] using hj
      rw [hc]
      apply Filter.EventuallyEq.germ_eq
      exact Filter.Eventually.of_forall fun _ ↦ by simp [a', hc]
  · intro j
    by_cases hj : j ∈ g.support
    · dsimp [b']
      rw [if_pos hj]
      exact hgb j
    · have hc : g.coeff j = 0 := by simpa [Polynomial.mem_support_iff] using hj
      rw [hc]
      apply Filter.EventuallyEq.germ_eq
      exact Filter.Eventually.of_forall fun _ ↦ by simp [b', hc]

theorem spec_resultant_fixed_degree_of_monic_aux {R : Type*} [CommRing R]
    (P g : Polynomial R) (hP : P.Monic) (N : ℕ) (hg : g.natDegree ≤ N) :
    P.resultant g P.natDegree N = P.resultant g := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hg
  rw [resultant_add_right_deg _ _ _ _ _ le_rfl]
  simp [hP.leadingCoeff]

theorem spec_monic_fibre_ne_zero_aux {n : ℕ} (P : Polynomial (AnalyticGerm n))
    (hP : P.Monic) (a : ℕ → (Fin n → ℂ) → ℂ)
    (x : Fin n → ℂ) (hlead : a P.natDegree x = 1) :
    P.sum (fun j _ ↦ monomial j (a j x)) ≠ 0 := by
  intro hz
  have hc := congrArg (fun Q : ℂ[X] ↦ Q.coeff P.natDegree) hz
  simpa [Polynomial.sum, coeff_monomial, hP.coeff_natDegree, hlead] using hc

private theorem coeff_sum_monomial_gaga10a {A B : Type*} [Semiring A] [Semiring B]
    (P : Polynomial A) (c : ℕ → B) (i : ℕ) :
    (P.sum fun j _ ↦ monomial j (c j)).coeff i = if i ∈ P.support then c i else 0 := by
  classical
  simp only [Polynomial.sum, finsetSum_coeff, coeff_monomial]
  exact Finset.sum_ite_eq' _ _ _

private theorem map_sum_monomial_gaga10a {A B C : Type*} [Semiring A] [Semiring B] [Semiring C]
    (P : Polynomial A) (c : ℕ → B) (φ : B →+* C) :
    (P.sum fun j _ ↦ monomial j (c j)).map φ = P.sum fun j _ ↦ monomial j (φ (c j)) := by
  simp only [Polynomial.sum, Polynomial.map_sum, map_monomial]

private theorem analyticOnNhd_fibre_coeff_gaga10a {n : ℕ} {A : Type*} [Semiring A]
    (P : Polynomial A)
    (a : ℕ → (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ)) (ha : ∀ j, AnalyticOnNhd ℂ (a j) U)
    (i : ℕ) : AnalyticOnNhd ℂ (fun x ↦ (P.sum fun j _ ↦ monomial j (a j x)).coeff i) U := by
  classical
  simp only [coeff_sum_monomial_gaga10a]
  by_cases hi : i ∈ P.support
  · simpa only [hi, ↓reduceIte] using ha i
  · simpa only [hi, ↓reduceIte] using analyticOnNhd_const

theorem spec_fixed_degree_resultant_analytic_aux {n m N : ℕ}
    (P g : Polynomial (AnalyticGerm n))
    (a b : ℕ → (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ))
    (ha : ∀ j, AnalyticOnNhd ℂ (a j) U)
    (hb : ∀ j, AnalyticOnNhd ℂ (b j) U) :
    AnalyticOnNhd ℂ (fun x ↦
      (P.sum fun j _ ↦ monomial j (a j x)).resultant
        (g.sum fun j _ ↦ monomial j (b j x)) m N) U := by
  classical
  have hentry : ∀ i k : Fin (m + N), AnalyticOnNhd ℂ (fun x ↦
      sylvester (P.sum fun j _ ↦ monomial j (a j x))
        (g.sum fun j _ ↦ monomial j (b j x)) m N i k) U := by
    intro i k
    induction k using Fin.addCases with
    | left k =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs
      · exact analyticOnNhd_fibre_coeff_gaga10a g b U hb _
      · exact analyticOnNhd_const
    | right k =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs
      · exact analyticOnNhd_fibre_coeff_gaga10a P a U ha _
      · exact analyticOnNhd_const
  intro x hx
  simp only [resultant, Matrix.det_apply']
  refine Finset.analyticAt_fun_sum _ fun σ _ ↦ analyticAt_const.mul ?_
  exact Finset.analyticAt_fun_prod _ fun i _ ↦ hentry (σ i) i x hx

theorem spec_resultant_representative_aux {n : ℕ}
    (P g : Polynomial (AnalyticGerm n)) (hP : P.Monic) :
    ∃ (a b : ℕ → (Fin n → ℂ) → ℂ) (R : (Fin n → ℂ) → ℂ)
        (U : Set (Fin n → ℂ)),
      U ∈ nhds (0 : Fin n → ℂ) ∧
      (∀ j, AnalyticOnNhd ℂ (a j) U) ∧ (∀ j, AnalyticOnNhd ℂ (b j) U) ∧
      AnalyticOnNhd ℂ R U ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j) = (P.coeff j).1) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (b j) = (g.coeff j).1) ∧
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) R = (P.resultant g).1 ∧
      (∀ x ∈ U, R x = (P.sum fun j _ ↦ monomial j (a j x)).resultant
        (g.sum fun j _ ↦ monomial j (b j x))) ∧
      (∀ x ∈ U, P.sum (fun j _ ↦ monomial j (a j x)) ≠ 0) := by
  classical
  obtain ⟨a, b, U, hU, ha, hb, hga, hgb⟩ :=
    spec_simultaneous_coefficient_representatives_aux P g
  have hlead : ∀ᶠ x in nhds (0 : Fin n → ℂ), a P.natDegree x = 1 := by
    have h1 : @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a P.natDegree) =
        @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (fun _ ↦ 1) := by
      rw [hga, hP.coeff_natDegree]; rfl
    exact Filter.Germ.coe_eq.mp h1
  obtain ⟨V, hV, hVlead⟩ := hlead.exists_mem
  set dP := P.natDegree
  set dg := g.natDegree
  let R : (Fin n → ℂ) → ℂ := fun x ↦ (P.sum fun j _ ↦ monomial j (a j x)).resultant
    (g.sum fun j _ ↦ monomial j (b j x)) dP dg
  let Pf : Polynomial ((Fin n → ℂ) → ℂ) := P.sum fun j _ ↦ monomial j (a j)
  let Gf : Polynomial ((Fin n → ℂ) → ℂ) := g.sum fun j _ ↦ monomial j (b j)
  have hR : R = Pf.resultant Gf dP dg := by
    funext x
    have := resultant_map_map Pf Gf dP dg (Pi.evalRingHom (fun _ : Fin n → ℂ ↦ ℂ) x)
    rw [map_sum_monomial_gaga10a, map_sum_monomial_gaga10a] at this
    exact this
  have hPmap : Pf.map (Filter.Germ.coeRingHom (nhds (0 : Fin n → ℂ))) =
      P.map (analyticGermSubring n).subtype := by
    ext i
    rw [map_sum_monomial_gaga10a, coeff_sum_monomial_gaga10a, coeff_map]
    split_ifs with hi
    · exact hga i
    · rw [Polynomial.notMem_support_iff.mp hi]; rfl
  have hGmap : Gf.map (Filter.Germ.coeRingHom (nhds (0 : Fin n → ℂ))) =
      g.map (analyticGermSubring n).subtype := by
    ext i
    rw [map_sum_monomial_gaga10a, coeff_sum_monomial_gaga10a, coeff_map]
    split_ifs with hi
    · exact hgb i
    · rw [Polynomial.notMem_support_iff.mp hi]; rfl
  have hfib : ∀ x ∈ V, (P.sum fun j _ ↦ monomial j (a j x)).Monic ∧
      (P.sum fun j _ ↦ monomial j (a j x)).natDegree = dP := by
    intro x hx
    have hle : (P.sum fun j _ ↦ monomial j (a j x)).natDegree ≤ dP := by
      refine natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ ?_
      rw [coeff_sum_monomial_gaga10a, ite_eq_right_iff]
      intro hs
      exact absurd (le_natDegree_of_mem_supp i hs) (not_le.mpr hi)
    have hc : (P.sum fun j _ ↦ monomial j (a j x)).coeff dP = 1 := by
      rw [coeff_sum_monomial_gaga10a]
      split_ifs with hs
      · exact hVlead x hx
      · exact absurd (natDegree_mem_support_of_nonzero hP.ne_zero) hs
    have hm : (P.sum fun j _ ↦ monomial j (a j x)).Monic :=
      monic_of_natDegree_le_of_coeff_eq_one _ hle hc
    exact ⟨hm, le_antisymm hle (le_natDegree_of_ne_zero (by rw [hc]; exact one_ne_zero))⟩
  refine ⟨a, b, R, U ∩ V, Filter.inter_mem hU hV, fun j ↦ (ha j).mono Set.inter_subset_left,
    fun j ↦ (hb j).mono Set.inter_subset_left,
    (spec_fixed_degree_resultant_analytic_aux P g a b U ha hb).mono Set.inter_subset_left,
    hga, hgb, ?_, ?_, ?_⟩
  · rw [hR]
    change Filter.Germ.coeRingHom (nhds (0 : Fin n → ℂ)) (Pf.resultant Gf dP dg) = _
    rw [← resultant_map_map, hPmap, hGmap, resultant_map_map]
    rfl
  · intro x hx
    obtain ⟨hm, hd⟩ := hfib x hx.2
    simp only [R]
    rw [← hd]
    apply spec_resultant_fixed_degree_of_monic_aux _ _ hm
    refine natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ ?_
    rw [coeff_sum_monomial_gaga10a, ite_eq_right_iff]
    intro hs
    exact absurd (le_natDegree_of_mem_supp i hs) (not_le.mpr hi)
  · intro x hx
    exact (hfib x hx.2).1.ne_zero

theorem spec_discriminant_representative_aux {n : ℕ}
    (P : Polynomial (AnalyticGerm n)) (hP : P.Monic) :
    ∃ (a : ℕ → (Fin n → ℂ) → ℂ) (D : (Fin n → ℂ) → ℂ)
        (U : Set (Fin n → ℂ)),
      U ∈ nhds (0 : Fin n → ℂ) ∧ (∀ j, AnalyticOnNhd ℂ (a j) U) ∧
      AnalyticOnNhd ℂ D U ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j) = (P.coeff j).1) ∧
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) D = P.discr.1 ∧
      (∀ x ∈ U, D x = (P.sum fun j _ ↦ monomial j (a j x)).discr) ∧
      (∀ x ∈ U, P.sum (fun j _ ↦ monomial j (a j x)) ≠ 0) := by
  classical
  obtain ⟨a, _, U₀, hU₀, ha, _, haP, _⟩ :=
    spec_simultaneous_coefficient_representatives_aux P P
  let F : (Fin n → ℂ) → ℂ[X] := fun x ↦
    P.sum fun j _ ↦ monomial j (a j x)
  let D : (Fin n → ℂ) → ℂ := fun x ↦
    (AnalyticDivisorAlgebraic5.gaga5b_sylvesterDerivAt (F x) P.natDegree).det *
      (-1) ^ (P.natDegree * (P.natDegree - 1) / 2)
  have hlead : ∀ᶠ x in nhds (0 : Fin n → ℂ), a P.natDegree x = 1 := by
    apply Filter.Germ.coe_eq.mp
    change (a P.natDegree : Filter.Germ (nhds (0 : Fin n → ℂ)) ℂ) = 1
    simpa [hP.coeff_natDegree] using haP P.natDegree
  obtain ⟨V, hV, hleadV⟩ := hlead.exists_mem
  let W := U₀ ∩ V
  have hW : W ∈ nhds (0 : Fin n → ℂ) := inter_mem hU₀ hV
  have hdeg : ∀ x ∈ W, (F x).natDegree = P.natDegree := by
    intro x hx
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · dsimp [F]
      apply natDegree_sum_le_of_forall_le
      intro j hj
      exact (natDegree_monomial_le _).trans (le_natDegree_of_ne_zero (mem_support_iff.mp hj))
    · dsimp [F]
      simp [Polynomial.sum, coeff_monomial, hP.coeff_natDegree, hleadV x hx.2]
  have hDW : ∀ x ∈ W, D x = (F x).discr := by
    intro x hx
    exact (AnalyticDivisorAlgebraic5.gaga5b_discr_eq_sylvesterDerivAt (hdeg x hx)).symm
  have hc : ∀ x ∈ W, ∀ k, AnalyticAt ℂ (fun z ↦ (F z).coeff k) x := by
    intro x hx k
    dsimp [F]
    simp_rw [coeff_sum]
    simp only [Polynomial.sum, coeff_monomial]
    refine Finset.analyticAt_fun_sum _ fun j hj ↦ ?_
    split_ifs
    · exact ha j x hx.1
    · exact analyticAt_const
  have hc' : ∀ x ∈ W, ∀ k,
      AnalyticAt ℂ (fun z ↦ (derivative (F z)).coeff k) x := by
    intro x hx k
    simp only [coeff_derivative]
    exact (hc x hx _).mul analyticAt_const
  have hDA : AnalyticOnNhd ℂ D W := by
    intro x hx
    dsimp [D]
    refine AnalyticAt.mul
      (AnalyticDivisorAlgebraic5.gaga5b_analyticAt_det fun i j ↦ ?_) analyticAt_const
    unfold AnalyticDivisorAlgebraic5.gaga5b_sylvesterDerivAt
    split_ifs
    · exact analyticAt_const
    simp only [Matrix.updateRow_apply]
    split_ifs
    all_goals try exact analyticAt_const
    unfold sylvester
    simp only [Matrix.of_apply]
    induction j using Fin.addCases with
    | left j =>
      simp only [Fin.addCases_left]
      split_ifs
      · exact hc x hx _
      · exact analyticAt_const
    | right j =>
      simp only [Fin.addCases_right]
      split_ifs
      · exact hc' x hx _
      · exact analyticAt_const
  have hcoeff (k : ℕ) :
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (fun x ↦ (F x).coeff k) =
        (P.coeff k).1 := by
    dsimp [F]
    simp_rw [coeff_sum]
    by_cases hk : k ∈ P.support
    · calc
        _ = @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a k) := by
          apply congrArg Filter.Germ.ofFun
          funext x
          simp [Polynomial.sum, coeff_monomial, hk]
        _ = _ := haP k
    · have hPk : P.coeff k = 0 := by simpa [mem_support_iff] using hk
      rw [hPk]
      apply congrArg Filter.Germ.ofFun
      funext x
      simp [Polynomial.sum, coeff_monomial, hk]
  have hcoeff' (k : ℕ) :
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (fun x ↦ (derivative (F x)).coeff k) =
        ((derivative P).coeff k).1 := by
    simp only [coeff_derivative]
    change (↑(fun x ↦ (F x).coeff (k + 1)) :
      Filter.Germ (nhds (0 : Fin n → ℂ)) ℂ) * (k + 1) =
        (P.coeff (k + 1)).1 * (k + 1)
    rw [hcoeff]
  have hDP : @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) D = P.discr.1 := by
    change (D : Filter.Germ (nhds (0 : Fin n → ℂ)) ℂ) = P.discr.1
    rw [Polynomial.discr]
    dsimp [D, AnalyticDivisorAlgebraic5.gaga5b_sylvesterDerivAt]
    unfold sylvesterDeriv
    split_ifs
    · change ((Matrix.det 0 : ℂ) : Filter.Germ (nhds (0 : Fin n → ℂ)) ℂ) *
          (-1) ^ (P.natDegree * (P.natDegree - 1) / 2) = _
      simp [‹P.natDegree = 0›]
      exact (AnalyticGerm n).subtype.map_one
    · let M : (Fin n → ℂ) → Matrix (Fin (P.natDegree - 1 + P.natDegree))
          (Fin (P.natDegree - 1 + P.natDegree)) ℂ := fun x ↦
        ((derivative (F x)).sylvester (F x) (P.natDegree - 1) P.natDegree).updateRow
          ⟨2 * P.natDegree - 2, by lia⟩
          (fun j ↦ if ↑j = P.natDegree - 2 then 1 else
            if ↑j = 2 * P.natDegree - 2 then (P.natDegree : ℂ) else 0)
      let MP := ((derivative P).sylvester P (P.natDegree - 1) P.natDegree).updateRow
          ⟨2 * P.natDegree - 2, by lia⟩
          (fun j ↦ if ↑j = P.natDegree - 2 then 1 else
            if ↑j = 2 * P.natDegree - 2 then (P.natDegree : AnalyticGerm n) else 0)
      let MF : Matrix (Fin (P.natDegree - 1 + P.natDegree))
          (Fin (P.natDegree - 1 + P.natDegree)) ((Fin n → ℂ) → ℂ) :=
        fun i j x ↦ M x i j
      change (↑(fun x ↦ (M x).det) : Filter.Germ (nhds (0 : Fin n → ℂ)) ℂ) *
          (-1) ^ (P.natDegree * (P.natDegree - 1) / 2) =
        (MP.det).1 * (-1) ^ (P.natDegree * (P.natDegree - 1) / 2)
      congr 1
      rw [show (↑(fun x ↦ (M x).det) : Filter.Germ (nhds (0 : Fin n → ℂ)) ℂ) =
          ((Filter.Germ.coeRingHom (nhds (0 : Fin n → ℂ))).mapMatrix MF).det by
        rw [← RingHom.map_det]
        apply congrArg Filter.Germ.ofFun
        funext x
        rw [Matrix.det_apply, Matrix.det_apply]
        simp [MF]]
      rw [show (MP.det).1 = ((AnalyticGerm n).subtype.mapMatrix MP).det by
        exact (AnalyticGerm n).subtype.map_det MP]
      congr 1
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
      dsimp [MF, M, MP]
      simp only [Matrix.updateRow_apply]
      split_ifs
      all_goals try rfl
      unfold sylvester
      simp only [Matrix.of_apply]
      induction j using Fin.addCases with
      | left j =>
        simp only [Fin.addCases_left]
        split_ifs
        · exact hcoeff _
        · rfl
      | right j =>
        simp only [Fin.addCases_right]
        split_ifs
        · exact hcoeff' _
        · rfl
  refine ⟨a, D, W, hW, fun j x hx ↦ ha j x hx.1, hDA, haP, hDP, ?_, ?_⟩
  · exact hDW
  · intro x hx
    exact spec_monic_fibre_ne_zero_aux P hP a x (hleadV x hx.2)

theorem spec_resultant_nonzero_fibre_avoids_common_root_aux {n : ℕ}
    (P g : Polynomial (AnalyticGerm n)) (hP : P.Monic) :
    ∃ (a b : ℕ → (Fin n → ℂ) → ℂ) (R : (Fin n → ℂ) → ℂ)
        (U : Set (Fin n → ℂ)),
      U ∈ nhds (0 : Fin n → ℂ) ∧ AnalyticOnNhd ℂ R U ∧
      (∀ j, AnalyticOnNhd ℂ (a j) U) ∧
      (∀ j, AnalyticOnNhd ℂ (b j) U) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j) = (P.coeff j).1) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (b j) = (g.coeff j).1) ∧
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) R = (P.resultant g).1 ∧
      ∀ x ∈ U, R x ≠ 0 → ∀ w : ℂ,
        (P.sum fun j _ ↦ monomial j (a j x)).eval w ≠ 0 ∨
          (g.sum fun j _ ↦ monomial j (b j x)).eval w ≠ 0 := by
  obtain ⟨a, b, R, U, hU, ha, hb, hR, haP, hbg, hRR, hcompat, hfibre⟩ :=
    spec_resultant_representative_aux P g hP
  refine ⟨a, b, R, U, hU, hR, ha, hb, haP, hbg, hRR, ?_⟩
  intro x hxU hx w
  apply AnalyticDivisorAlgebraic9.spec_resultant_specialization_avoids_common_root
    P g a b R U hU ha hb hR
  · intro j
    apply Subtype.ext
    exact haP j
  · intro j
    apply Subtype.ext
    exact hbg j
  · apply Subtype.ext
    exact hRR
  · exact hfibre
  · exact hcompat
  · exact hxU
  · exact hx

theorem spec_discriminant_nonzero_fibre_simple_roots_aux {n : ℕ}
    (P : Polynomial (AnalyticGerm n)) (hP : P.Monic) :
    ∃ (a : ℕ → (Fin n → ℂ) → ℂ) (D : (Fin n → ℂ) → ℂ)
        (U : Set (Fin n → ℂ)),
      U ∈ nhds (0 : Fin n → ℂ) ∧ AnalyticOnNhd ℂ D U ∧
      (∀ j, AnalyticOnNhd ℂ (a j) U) ∧
      (∀ j, @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) (a j) = (P.coeff j).1) ∧
      @Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0) D = P.discr.1 ∧
      ∀ x ∈ U, D x ≠ 0 → ∀ w : ℂ,
        (P.sum fun j _ ↦ monomial j (a j x)).eval w = 0 →
          (P.sum fun j _ ↦ monomial j (a j x)).derivative.eval w ≠ 0 := by
  obtain ⟨a, D, U, hU, ha, hD, haP, hDD, hcompat, hfibre⟩ :=
    spec_discriminant_representative_aux P hP
  refine ⟨a, D, U, hU, hD, ha, haP, hDD, ?_⟩
  intro x hxU hx w hw
  apply AnalyticDivisorAlgebraic9.spec_discriminant_specialization_simple_root
    P a D U hU ha hD
  · intro j
    apply Subtype.ext
    exact haP j
  · apply Subtype.ext
    exact hDD
  · exact hfibre
  · exact hcompat
  · exact hxU
  · exact hx
  · exact hw

end HodgeLean.Foundations.AnalyticDivisorAlgebraic10
