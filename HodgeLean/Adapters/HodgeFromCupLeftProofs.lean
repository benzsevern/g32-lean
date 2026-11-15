import HodgeLean.Adapters.HodgeOpposedAbelian
import HodgeLean.Adapters.CupFilteredDeRham

/-! # Open obligations of stage `HodgeFromCupLeft`

One `_aux` obligation per statement of `HodgeFromCupLeft.lean`, all open. The statements, their
sources and their falsification checks are in `docs/specs/HodgeFromCupLeft.md`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open HodgeLean.RealDefs
open scoped TensorProduct

namespace HodgeLean.Adapters

theorem spec_bettiDeRhamHQ_cupC_cupMultiC_mem_of_cupLeft_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    {a k m : ℕ} (h : a + k = m) (u : Fin a → ℂ ⊗[ℚ] HQ X 1)
    (hu : ∀ i, bettiDeRhamHQ X 1 (u i) ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X))
    (q : ℤ) (y : ℂ ⊗[ℚ] HQ X k) (hy : bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X)) :
    bettiDeRhamHQ X m (μ.cupC h (μ.cupMultiC a u) y) ∈ F^((a : ℤ) + q) H_dR^(m : ℤ)(X) := by
  induction a generalizing m with
  | zero =>
    obtain rfl : m = k := by omega
    rw [cupC_one_unit]
    simpa using hy
  | succ a ih =>
    rw [CupProduct.cupMultiC_succ, cupC_assoc μ (Nat.add_comm 1 a) (rfl : a + k = a + k) h
      (by omega)]
    have := hL (show 1 + (a + k) = m by omega) ((a : ℤ) + q) (u 0) _ (hu 0)
      (ih rfl (Fin.tail u) fun i => hu i.succ)
    convert this using 2
    push_cast
    ring

/-- Graded commutativity of the complexified cup product. -/
theorem hlredA_cupC_comm {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (μ : CupProduct X) {i j k : ℕ} (h : i + j = k) (h' : j + i = k)
    (a : ℂ ⊗[ℚ] HQ X i) (b : ℂ ⊗[ℚ] HQ X j) :
    μ.cupC h' b a = ((-1 : ℂ) ^ (i * j)) • μ.cupC h a b := by
  induction a using TensorProduct.inductionOn with
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha', smul_add]
  | tmul z a =>
    induction b using TensorProduct.inductionOn with
    | add b b' hb hb' => simp only [map_add, LinearMap.add_apply, hb, hb', smul_add]
    | tmul w b =>
      rw [CupProduct.cupC_tmul, CupProduct.cupC_tmul, μ.graded_comm h h', TensorProduct.tmul_smul,
        ← algebraMap_smul ℂ, mul_comm w z]
      congr 1
      push_cast
      rfl

theorem spec_cupC_cupMultiC_eq_zero_of_cupLeft_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    {n a m : ℕ} (h : n + a = m) (p : ℤ) (x : ℂ ⊗[ℚ] HQ X n)
    (hx : bettiDeRhamHQ X n x ∈ F^p H_dR^(n : ℤ)(X)) (u : Fin a → ℂ ⊗[ℚ] HQ X 1)
    (hu : ∀ i, bettiDeRhamHQ X 1 (u i) ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X))
    (hpa : (dim X.left : ℤ) < p + a) :
    μ.cupC h x (μ.cupMultiC a u) = 0 := by
  have hβ := (HodgeLean.Foundations.spec_bettiDeRhamIso_abelian X).bijective
  have h' : a + n = m := by omega
  have hmem := spec_bettiDeRhamHQ_cupC_cupMultiC_mem_of_cupLeft_aux X hL h' u hu p x hx
  rw [spec_hodgeFiltration_eq_bot_of_dim_lt X (by omega) _, Submodule.mem_bot] at hmem
  have h0 : μ.cupC h' (μ.cupMultiC a u) x = 0 := (hβ m).1 (hmem.trans (map_zero _).symm)
  rw [hlredA_cupC_comm μ h' h, h0, smul_zero]

/-- With `hL`, a filtered class cups to zero with an iterated cup of degree-one classes once its
level plus the number of marked factors in `F^1` exceeds `dim X`. A marked factor in front is
cupped onto the class (raising its level by `hL`); an unmarked one is moved to the back by graded
commutativity, so no unmarked factor is ever cupped onto a filtered class. -/
theorem hlredA_cupC_cupMultiC_eq_zero {X : Over (Spec ↧ℂ)} [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X)) :
    ∀ (j : ℕ) (v : Fin j → ℂ ⊗[ℚ] HQ X 1) (c : Fin j → Bool),
      (∀ i, c i = true → bettiDeRhamHQ X 1 (v i) ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X)) →
      ∀ {n m : ℕ} (h : n + j = m) (p : ℤ) (x : ℂ ⊗[ℚ] HQ X n),
        bettiDeRhamHQ X n x ∈ F^p H_dR^(n : ℤ)(X) →
        (dim X.left : ℤ) < p + (∑ i, if c i then (1 : ℤ) else 0) →
        μ.cupC h x (μ.cupMultiC j v) = 0
  | 0, v, c, _, n, m, h, p, x, hx, hpc => by
    have hβ := (HodgeLean.Foundations.spec_bettiDeRhamIso_abelian X).bijective
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hpc
    rw [spec_hodgeFiltration_eq_bot_of_dim_lt X hpc _, Submodule.mem_bot] at hx
    rw [(hβ n).1 (hx.trans (map_zero _).symm), map_zero, LinearMap.zero_apply]
  | j + 1, v, c, hc, n, m, h, p, x, hx, hpc => by
    have hβ := (HodgeLean.Foundations.spec_bettiDeRhamIso_abelian X).bijective
    rw [Fin.sum_univ_succ] at hpc
    rw [CupProduct.cupMultiC_succ]
    by_cases h0 : c 0 = true
    · rw [← cupC_assoc μ (show n + 1 = n + 1 from rfl) (Nat.add_comm 1 j) (by omega) h]
      have hx' : bettiDeRhamHQ X (n + 1) (μ.cupC rfl x (v 0)) ∈
          F^(1 + p) H_dR^((n + 1 : ℕ) : ℤ)(X) := by
        rw [hlredA_cupC_comm μ (Nat.add_comm 1 n) rfl, map_smul]
        exact Submodule.smul_mem _ _ (hL (Nat.add_comm 1 n) p (v 0) x (hc 0 h0) hx)
      refine hlredA_cupC_cupMultiC_eq_zero hL j (Fin.tail v) (Fin.tail c)
        (fun i hi => hc i.succ hi) (by omega) (1 + p) _ hx' ?_
      simp only [h0, ↓reduceIte] at hpc
      refine lt_of_lt_of_eq hpc ?_
      rw [← add_assoc, add_comm p 1]
      rfl
    · rw [hlredA_cupC_comm μ rfl (Nat.add_comm 1 j), map_smul,
        ← cupC_assoc μ (show n + j = n + j from rfl) rfl (by omega) h,
        hlredA_cupC_cupMultiC_eq_zero hL j (Fin.tail v) (Fin.tail c)
          (fun i hi => hc i.succ hi) rfl p x hx ?_, map_zero, LinearMap.zero_apply, smul_zero]
      simp only [h0, Bool.false_eq_true, ↓reduceIte, zero_add] at hpc
      exact hpc

theorem spec_cupC_eq_zero_of_mem_cupWedgePiece_of_cupLeft_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    {n j m : ℕ} (h : n + j = m) (p a : ℤ) (x : ℂ ⊗[ℚ] HQ X n)
    (hx : bettiDeRhamHQ X n x ∈ F^p H_dR^(n : ℤ)(X)) (y : ℂ ⊗[ℚ] HQ X j)
    (hy : bettiDeRhamHQ X j y ∈ cupWedgePiece X μ j (a, (j : ℤ) - a))
    (hpa : (dim X.left : ℤ) < p + a) :
    μ.cupC h x y = 0 := by
  classical
  have _hT := hT
  have hβ := (HodgeLean.Foundations.spec_bettiDeRhamIso_abelian X).bijective
  rw [cupWedgePiece_eq_map_span] at hy
  obtain ⟨y', hy', hyy'⟩ := hy
  obtain rfl := (hβ j).1 hyy'
  clear hyy'
  induction hy' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨d, v, hd, hv, rfl⟩ := hz
    by_cases hall : ∀ i, d i = (1, 0) ∨ d i = (0, 1)
    swap
    · obtain ⟨i, hi⟩ := not_forall.mp hall
      rw [not_or] at hi
      have := hv i
      rw [cohomologyHodgePiece_one_eq_bot X (d i) hi.1 hi.2] at this
      rw [(μ.cupMultiC _).map_coord_zero i ((Submodule.mem_bot ℂ).mp this), map_zero]
    refine hlredA_cupC_cupMultiC_eq_zero hL j v (fun i => decide (d i = (1, 0)))
      (fun i hi => ?_) h p x hx ?_
    · have := bettiDeRhamHQ_mem_of_mem_cohomologyHodgePiece_one (hv i)
      rwa [of_decide_eq_true hi] at this
    · have e1 : (HodgeBlocks.totalBidegree j d).1 =
          ∑ i, if decide (d i = (1, 0)) then (1 : ℤ) else 0 := by
        simp only [HodgeBlocks.totalBidegree]
        refine Finset.sum_congr rfl fun i _ => ?_
        rcases hall i with h' | h' <;> simp [h']
      rw [← e1, hd]
      exact hpa
  | zero => rw [map_zero]
  | add z z' _ _ hz hz' => rw [map_add, hz, hz', add_zero]
  | smul r z _ hz => rw [map_smul, hz, smul_zero]

theorem spec_hodgeFiltration_le_iSup_cupWedgePiece_of_cupLeft_aux (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    (n : ℕ) (p : ℤ) :
    F^p H_dR^(n : ℤ)(X) ≤ ⨆ (p' : ℤ) (_ : p ≤ p'), cupWedgePiece X μ n (p', (n : ℤ) - p') := by
  by_cases hn : 2 * dim X.left < n
  · have := spec_subsingleton_deRhamCohomology_of_lt X n hn
    intro α _
    rw [Subsingleton.elim α 0]
    exact zero_mem _
  push Not at hn
  set g := dim X.left with hg
  set m := 2 * g - n with hm
  have hnm : n + m = 2 * g := by omega
  have hmZ : (m : ℤ) = 2 * (g : ℤ) - n := by omega
  have hβ := HodgeLean.Foundations.spec_bettiDeRhamIso_abelian X
  let e := LinearEquiv.ofBijective (bettiDeRhamHQ X n) (hβ.bijective n)
  have he : ∀ w, bettiDeRhamHQ X n (e.symm w) = w := fun w => e.apply_symm_apply w
  intro α hα
  have htop : α ∈ ⨆ i, cupWedgePiece X μ n i := by
    rw [(spec_cupWedgePiece_isInternal X hT n).submodule_iSup_eq_top]
    exact Submodule.mem_top
  have key := mem_iSup_compl_of_forall_eq_zero (S := {i : ℤ × ℤ | i.1 < p}) htop ?_
  · refine (show (⨆ (i : ℤ × ℤ) (_ : i ∉ {i : ℤ × ℤ | i.1 < p}), cupWedgePiece X μ n i) ≤ _ from
      iSup₂_le fun i hi => ?_) key
    by_cases hi' : i.1 + i.2 = n
    · have hi'' : i = (i.1, (n : ℤ) - i.1) := Prod.ext rfl (by simp only; omega)
      rw [hi'']
      exact le_iSup₂_of_le (f := fun (p' : ℤ) (_ : p ≤ p') =>
        cupWedgePiece X μ n (p', (n : ℤ) - p')) i.1 (by simpa using hi) le_rfl
    · rw [spec_cupWedgePiece_eq_bot X μ n i hi']
      exact bot_le
  intro i hi z hz c hc hzc
  by_cases hi' : i.1 + i.2 = n
  swap
  · rw [spec_cupWedgePiece_eq_bot X μ n i hi'] at hz
    exact (Submodule.mem_bot ℂ).mp hz
  obtain ⟨r, s⟩ := i
  simp only at hi'
  obtain rfl : s = n - r := by omega
  simp only [Set.mem_ofPred_eq] at hi
  suffices e.symm z = 0 by rw [← he z, this, map_zero]
  refine spec_eq_zero_of_cupC_cupWedgePiece_aux X hT hnm r (e.symm z) (by rwa [he]) fun y hy => ?_
  let Φ : H_dR^(n : ℤ)(X) →ₗ[ℂ] H_dR^((2 * g : ℕ) : ℤ)(X) :=
    bettiDeRhamHQ X (2 * g) ∘ₗ (μ.cupC hnm).flip y ∘ₗ e.symm.toLinearMap
  have hΦ : ∀ w, Φ w = bettiDeRhamHQ X (2 * g) (μ.cupC hnm (e.symm w) y) := fun w => rfl
  have hΦα : Φ α = 0 := by
    rw [hΦ, spec_cupC_eq_zero_of_mem_cupWedgePiece_of_cupLeft_aux X hT hL hnm p ((g : ℤ) - r)
      (e.symm α) (by rwa [he]) y hy (by omega), map_zero]
  have hΦc : Φ c = 0 := by
    have hle : (⨆ (j : ℤ × ℤ) (_ : j ≠ (r, (n : ℤ) - r)), cupWedgePiece X μ n j) ≤
        LinearMap.ker Φ := by
      refine iSup₂_le fun j hj w hw => ?_
      rw [LinearMap.mem_ker, hΦ]
      by_cases hj' : j.1 + j.2 = n
      · have hmem := spec_cupC_mem_cupWedgePiece_aux X μ hnm (x := e.symm w) (y := y)
          (by rw [he]; exact hw) hy
        have hj1 : j.1 ≠ r := fun h => hj (Prod.ext h (by simp only; omega))
        have hpair : (j.1 + ((g : ℤ) - r), j.2 + ((m : ℤ) - ((g : ℤ) - r))) =
            (j.1 + ((g : ℤ) - r), ((2 * g : ℕ) : ℤ) - (j.1 + ((g : ℤ) - r))) :=
          Prod.ext rfl (by simp only; push_cast; omega)
        rw [hpair, spec_cupWedgePiece_top_eq_bot_aux X hT _ (by omega)] at hmem
        exact (Submodule.mem_bot ℂ).mp hmem
      · rw [spec_cupWedgePiece_eq_bot X μ n j hj'] at hw
        simp only [(Submodule.mem_bot ℂ).mp hw, map_zero, LinearMap.zero_apply]
    exact hle hc
  have hΦz : Φ z = 0 := by
    have := congrArg Φ hzc
    rw [map_add, hΦα, hΦc, add_zero] at this
    exact this.symm
  rw [hΦ] at hΦz
  exact (hβ.bijective (2 * g)).1 (hΦz.trans (map_zero _).symm)

theorem spec_opposed_of_cupLeft_aux (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X} (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X))
    (n : ℕ) (p : ℤ) :
    hodgePiece X p ((n : ℤ) + 1 - p) n = ⊥ := by
  exact spec_opposed_of_hodgeFiltration_le X hT n
    (spec_hodgeFiltration_le_iSup_cupWedgePiece_of_cupLeft_aux X hT hL n) p

theorem spec_cupFiltered_of_cupLeft_alone_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X)) :
    CupFiltered X μ := by
  exact spec_cupFiltered_of_cupLeft X hT hL
    (fun n _ _ p _ _ => spec_opposed_of_cupLeft_aux X hT hL n p)

theorem spec_hodgeDecomposition_of_cupLeft_alone_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X}
    (hT : TorusCohomology μ)
    (hL : ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
      bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
      bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
      bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X)) :
    HodgeDecomposition X := by
  exact spec_hodgeDecomposition_of_cupFiltered X hT
    (spec_cupFiltered_of_cupLeft_alone_aux X hT hL)

theorem spec_cupFiltered_iff_cupLeft_aux (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {μ : CupProduct X} (hT : TorusCohomology μ) :
    CupFiltered X μ ↔
      ∀ {k m : ℕ} (h : 1 + k = m) (q : ℤ) (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k),
        bettiDeRhamHQ X 1 x ∈ F^1 H_dR^((1 : ℕ) : ℤ)(X) →
        bettiDeRhamHQ X k y ∈ F^q H_dR^(k : ℤ)(X) →
        bettiDeRhamHQ X m (μ.cupC h x y) ∈ F^(1 + q) H_dR^(m : ℤ)(X) := by
  exact ⟨fun hC => fun h q x y hx hy => hC.mem h 1 q x y hx hy,
    fun hL => spec_cupFiltered_of_cupLeft_alone_aux X hT hL⟩

end HodgeLean.Adapters
