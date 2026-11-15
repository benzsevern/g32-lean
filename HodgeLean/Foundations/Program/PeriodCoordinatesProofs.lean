import HodgeLean.Foundations.Program.PeriodCoordinatesDefs

/-! # B6-4a: graph-coordinate obligations -/

noncomputable section
open scoped TensorProduct Matrix Topology
open HodgeLean.Papers Filter Set
namespace HodgeLean.Foundations.Program

theorem b64_graphCoord_negFrame_aux (z : Fin 9 → ℂ) :
    b64_graphCoord (b64_negFrame z) = z := by
  have hh : b64_headBlock (b64_negFrame z) = 1 := by
    ext i j
    rw [b64_headBlock, Matrix.of_apply, b64_negFrame_repr, Matrix.one_apply]
    simp [Prod.ext_iff, Fin.ext_iff, eq_comm]
    refine (Finset.sum_eq_zero fun x _ => ?_).symm
    rw [ite_eq_right_iff]
    intro h
    omega
  have ht : b64_tailBlock (b64_negFrame z) = g32m_toMat z := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [b64_tailBlock, b64_negFrame_repr, Fin.sum_univ_succ]
  simp only [b64_graphCoord, hh, ht, inv_one, mul_one]
  funext k
  simp [b60c_matrixCoordinates, g32m_toMat]

theorem b64_negFrame_span_aux (z : Fin 9 → ℂ) :
    b60_F z ⊓ b64_Eminus = Submodule.span ℂ (Set.range (b64_negFrame z)) := by
  have hle : Submodule.span ℂ (Set.range (b64_negFrame z)) ≤ b60_F z ⊓ b64_Eminus := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    refine ⟨Submodule.subset_span ⟨(0, j), rfl⟩, ?_⟩
    apply Module.End.mem_eigenspace_iff.mpr
    simpa [b64_negFrame] using b60_omegaC_frame z (0, j)
  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have hli : LinearIndependent ℂ (b64_negFrame z) := by
    exact (b60_frame_independent z).comp (fun j : Fin 3 => (0, j))
      (by intro a b h; exact congrArg Prod.snd h)
  rw [finrank_span_eq_card hli]
  exact (b60_weil_dimensions z).2.symm

theorem b64_negFrame_head_entry (z : Fin 9 → ℂ) (i j : Fin 3) :
    b60c_eigenBasis.repr (b64_negFrame z j) (0, Fin.castAdd 3 i) =
      if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [b64_negFrame_repr, Fin.sum_univ_succ]

theorem b64_negFrame_tail_entry (z : Fin 9 → ℂ) (i j : Fin 3) :
    b60c_eigenBasis.repr (b64_negFrame z j) (0, Fin.natAdd 3 i) = g32m_toMat z i j := by
  fin_cases i <;> fin_cases j <;> simp [b64_negFrame_repr, Fin.sum_univ_succ]

theorem b64_matrixCoordinates_toMat (z : Fin 9 → ℂ) :
    b60c_matrixCoordinates (g32m_toMat z) = z := by
  funext k
  simp [b60c_matrixCoordinates, g32m_toMat]

theorem b64_graphCoord_of_span_aux (z : Fin 9 → ℂ) (v : Fin 3 → ℂ ⊗[ℤ] b60_Lattice)
    (hv : Submodule.span ℂ (Set.range v) = Submodule.span ℂ (Set.range (b64_negFrame z))) :
    IsUnit (b64_headBlock v) ∧ b64_graphCoord v = z := by
  classical
  have hsum (c : Fin 3 → ℂ) (i : Fin 3) :
      b60c_eigenBasis.repr (∑ j, c j • b64_negFrame z j) (0, Fin.castAdd 3 i) = c i := by
    simp [map_sum, b64_negFrame_head_entry]
  have hunit : IsUnit (b64_headBlock v) := by
    apply Matrix.mulVec_surjective_iff_isUnit.mp
    intro y
    have hm : ∑ i, y i • b64_negFrame z i ∈ Submodule.span ℂ (Set.range v) := by
      rw [hv]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hm
    refine ⟨c, ?_⟩
    funext i
    have hi := congrArg (fun x => b60c_eigenBasis.repr x (0, Fin.castAdd 3 i)) hc
    rw [hsum] at hi
    simpa [b64_headBlock, Matrix.mulVec, dotProduct, map_sum, mul_comm] using hi
  have ht : b64_tailBlock v = g32m_toMat z * b64_headBlock v := by
    ext i j
    have hm : v j ∈ Submodule.span ℂ (Set.range (b64_negFrame z)) := by
      rw [← hv]
      exact Submodule.subset_span ⟨j, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hm
    have hh (k : Fin 3) : b64_headBlock v k j = c k := by
      rw [b64_headBlock, Matrix.of_apply, ← hc, hsum]
    rw [b64_tailBlock, Matrix.of_apply, ← hc]
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul, b64_negFrame_tail_entry, Matrix.mul_apply, hh]
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _
  refine ⟨hunit, ?_⟩
  rw [b64_graphCoord, ht, Matrix.mul_nonsing_inv_cancel_right (b64_headBlock v) (g32m_toMat z)
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit), b64_matrixCoordinates_toMat]


theorem b64_linearIndependent_of_head (v : Fin 3 → ℂ ⊗[ℤ] b60_Lattice)
    (hu : IsUnit (b64_headBlock v)) : LinearIndependent ℂ v := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hm : b64_headBlock v *ᵥ c = 0 := by
    funext k
    have h := congrArg (fun x => b60c_eigenBasis.repr x (0, Fin.castAdd 3 k)) hc
    simpa [b64_headBlock, Matrix.mulVec, dotProduct, map_sum, mul_comm] using h
  have hz := (Matrix.mulVec_injective_iff_isUnit.mpr hu) (hm.trans (Matrix.mulVec_zero _).symm)
  exact congrFun hz i

theorem b64_span_negFrame_graphCoord_aux (v : Fin 3 → ℂ ⊗[ℤ] b60_Lattice)
    (hv : ∀ j, v j ∈ b64_Eminus) (hu : IsUnit (b64_headBlock v)) :
    Submodule.span ℂ (Set.range v) =
      Submodule.span ℂ (Set.range (b64_negFrame (b64_graphCoord v))) := by
  classical
  let z := b64_graphCoord v
  have hz : g32m_toMat z * b64_headBlock v = b64_tailBlock v := by
    dsimp only [z, b64_graphCoord]
    rw [b60c_toMat_matrixCoordinates, Matrix.nonsing_inv_mul_cancel_right
      (b64_headBlock v) (b64_tailBlock v) ((Matrix.isUnit_iff_isUnit_det _).mp hu)]
  have heq (j : Fin 3) : v j = ∑ k, b64_headBlock v k j • b64_negFrame z k := by
    apply b60c_eigenBasis.repr.injective
    ext ⟨a, i⟩
    change b60c_eigenBasis.repr (v j) (a, i) =
      b60c_eigenBasis.repr (∑ k, b64_headBlock v k j • b64_negFrame z k) (a, i)
    fin_cases a
    · change b60c_eigenBasis.repr (v j) (0, i) =
        b60c_eigenBasis.repr (∑ k, b60c_eigenBasis.repr (v j) (0, Fin.castAdd 3 k) •
          b64_negFrame z k) (0, i)
      refine Fin.addCases (m := 3) (n := 3) (fun k => ?_) (fun k => ?_) i
      · simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
          Finsupp.smul_apply, smul_eq_mul, b64_negFrame_head_entry]
        simp
      · have h := congrFun (congrFun hz k) j
        simp only [Matrix.mul_apply, b64_tailBlock, b64_headBlock, Matrix.of_apply] at h
        rw [← h]
        simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
          Finsupp.smul_apply, smul_eq_mul, b64_negFrame_tail_entry]
        apply Finset.sum_congr rfl
        intro l _
        exact mul_comm _ _
    · have hj : b60_omegaC (v j) =
          ((if (0 : Fin 2) = 0 then -1 else 1) * Complex.I * (Real.sqrt 3 : ℂ)) • v j := by
        simpa using (Module.End.mem_eigenspace_iff.mp (hv j))
      change b60c_eigenBasis.repr (v j) (1, i) = _
      rw [b60c_eigen_support 0 1 (by decide) _ hj]
      simp [map_sum, b64_negFrame_repr]
  have hle : Submodule.span ℂ (Set.range v) ≤ Submodule.span ℂ (Set.range (b64_negFrame z)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    rw [heq j]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [finrank_span_eq_card (b64_linearIndependent_of_head v hu)]
  have hli : LinearIndependent ℂ (b64_negFrame z) :=
    (b60_frame_independent z).comp (fun j : Fin 3 => (0, j))
      (by intro a b h; exact congrArg Prod.snd h)
  rw [finrank_span_eq_card hli]


theorem b64_coordOf_eq_aux (z : Fin 9 → ℂ) : b64_coordOf (b60_F z) = z := by
  classical
  have hex : ∃ w : Fin 9 → ℂ, b60_F z = b60_F w := ⟨z, rfl⟩
  unfold b64_coordOf
  rw [dite_eq_left hex]
  have hs : Submodule.span ℂ (Set.range (b64_negFrame hex.choose)) =
      Submodule.span ℂ (Set.range (b64_negFrame z)) := by
    rw [← b64_negFrame_span_aux, ← b64_negFrame_span_aux]
    exact congrArg (fun G => G ⊓ b64_Eminus) hex.choose_spec.symm
  exact (b64_graphCoord_negFrame_aux hex.choose).symm.trans
    (b64_graphCoord_of_span_aux z _ hs).2


theorem b64_analytic_det {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : Type*} [Fintype n] [DecidableEq n] (A : E → Matrix n n ℂ) (W : Set E)
    (hA : ∀ i j, AnalyticOnNhd ℂ (fun t => A t i j) W) :
    AnalyticOnNhd ℂ (fun t => (A t).det) W := by
  classical
  simp only [Matrix.det_apply']
  apply Finset.analyticOnNhd_fun_sum
  intro σ _
  exact analyticOnNhd_const.mul (Finset.analyticOnNhd_fun_prod _ fun i _ => hA (σ i) i)

theorem b64_analytic_inv_entry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : Type*} [Fintype n] [DecidableEq n] (A : E → Matrix n n ℂ) (W : Set E)
    (hA : ∀ i j, AnalyticOnNhd ℂ (fun t => A t i j) W)
    (hunit : ∀ t ∈ W, IsUnit (A t)) (i j : n) :
    AnalyticOnNhd ℂ (fun t => (A t)⁻¹ i j) W := by
  have hd := b64_analytic_det A W hA
  have ha : AnalyticOnNhd ℂ (fun t => (A t).adjugate i j) W := by
    simp only [Matrix.adjugate_apply]
    apply b64_analytic_det
    intro k l
    by_cases h : k = j
    · subst k
      simp only [Matrix.updateRow_self]
      exact analyticOnNhd_const
    · simpa only [Matrix.updateRow_ne h] using hA k l
  intro t ht
  have hn : (A t).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp (hunit t ht)).ne_zero
  convert! ((hd t ht).inv hn).mul (ha t ht) using 1
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  rfl

theorem b64_graphCoord_analyticOnNhd_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (v : E → Fin 3 → ℂ ⊗[ℤ] b60_Lattice) (W : Set E)
    (hv : ∀ j p, AnalyticOnNhd ℂ (fun t => b60c_eigenBasis.repr (v t j) p) W)
    (hu : ∀ t ∈ W, IsUnit (b64_headBlock (v t))) :
    AnalyticOnNhd ℂ (fun t => b64_graphCoord (v t)) W := by
  have hh : ∀ i j, AnalyticOnNhd ℂ (fun t => b64_headBlock (v t) i j) W := by
    intro i j
    exact hv j (0, Fin.castAdd 3 i)
  have hi := b64_analytic_inv_entry (fun t => b64_headBlock (v t)) W hh hu
  apply AnalyticOnNhd.pi
  intro k
  simp only [b64_graphCoord, b60c_matrixCoordinates, Matrix.mul_apply]
  apply Finset.analyticOnNhd_fun_sum
  intro j _
  let q := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm k
  exact (hv j (0, Fin.natAdd 3 q.1)).mul (hi j q.2)


def b64_negLinear : (ℂ ⊗[ℤ] b60_Lattice) →ₗ[ℂ] ℂ ⊗[ℤ] b60_Lattice where
  toFun := b64_negPart
  map_add' x y := by
    simp [b64_negPart, map_add, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp [b64_negPart, map_smul, Finset.smul_sum, smul_smul]

theorem b64_negPart_eq_of_mem (x : ℂ ⊗[ℤ] b60_Lattice) (hx : x ∈ b64_Eminus) :
    b64_negPart x = x := by
  apply (b60c_eigen_reconstruction 0 x ?_).symm
  simpa using Module.End.mem_eigenspace_iff.mp hx

theorem b64_negPart_mem (x : ℂ ⊗[ℤ] b60_Lattice) : b64_negPart x ∈ b64_Eminus := by
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  rw [b64_Eminus, Module.End.mem_eigenspace_iff, b60c_omega_eigenBasis]
  simp

theorem b64_negPart_frame (z : Fin 9 → ℂ) (a : Fin 2) (j : Fin 3) :
    b64_negPart (b60_frame z (a, j)) = if a = 0 then b64_negFrame z j else 0 := by
  fin_cases a
  · apply b64_negPart_eq_of_mem
    apply Module.End.mem_eigenspace_iff.mpr
    simpa using b60_omegaC_frame z (0, j)
  · have hj : b60_omegaC (b60_frame z (1, j)) =
        ((if (1 : Fin 2) = 0 then -1 else 1) * Complex.I * (Real.sqrt 3 : ℂ)) •
          b60_frame z (1, j) := by
      simpa using b60_omegaC_frame z (1, j)
    simp only [b64_negPart]
    simp [b60c_eigen_support 1 0 (by decide) _ hj]

theorem b64_projected_span {ι : Type*} (u : ι → ℂ ⊗[ℤ] b60_Lattice)
    (z : Fin 9 → ℂ) (hu : Submodule.span ℂ (Set.range u) = b60_F z) :
    Submodule.span ℂ (Set.range fun k => b64_negPart (u k)) =
      Submodule.span ℂ (Set.range (b64_negFrame z)) := by
  have he : Submodule.span ℂ (Set.range fun k => b64_negPart (u k)) =
      (b60_F z).map b64_negLinear := by
    rw [← hu, Submodule.map_span, ← Set.range_comp]
    rfl
  rw [he, b60_F, Submodule.map_span, ← Set.range_comp]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, j⟩, rfl⟩
    change b64_negPart (b60_frame z (a, j)) ∈ _
    rw [b64_negPart_frame]
    split_ifs
    · exact Submodule.subset_span ⟨j, rfl⟩
    · exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    apply Submodule.subset_span
    refine ⟨(0, j), ?_⟩
    exact b64_negPart_frame z 0 j

theorem b64_negPart_repr (x : ℂ ⊗[ℤ] b60_Lattice) (p : Fin 2 × Fin 6) :
    b60c_eigenBasis.repr (b64_negPart x) p =
      if p.1 = 0 then b60c_eigenBasis.repr x p else 0 := by
  classical
  simp only [b64_negPart, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
  rcases p with ⟨a, i⟩
  fin_cases a <;> simp [Prod.ext_iff, eq_comm]

theorem b64_local_subframe_aux {E : Type*} [TopologicalSpace E] {ι : Type*} [Fintype ι]
    (u : E → ι → ℂ ⊗[ℤ] b60_Lattice) (F : E → Submodule ℂ (ℂ ⊗[ℤ] b60_Lattice))
    (W : Set E) (hW : IsOpen W)
    (hu : ∀ k p, ContinuousOn (fun t => b60c_eigenBasis.repr (u t k) p) W)
    (hspan : ∀ t ∈ W, Submodule.span ℂ (Set.range (u t)) = F t)
    (hF : ∀ t ∈ W, ∃ z : Fin 9 → ℂ, F t = b60_F z) (t₀ : E) (ht₀ : t₀ ∈ W) :
    ∃ W' : Set E, IsOpen W' ∧ t₀ ∈ W' ∧ W' ⊆ W ∧ ∃ σ : Fin 3 → ι, ∀ t ∈ W',
      IsUnit (b64_headBlock fun j => b64_negPart (u t (σ j))) ∧
      Submodule.span ℂ (Set.range fun j => b64_negPart (u t (σ j))) = F t ⊓ b64_Eminus := by
  classical
  obtain ⟨z₀, hz₀⟩ := hF t₀ ht₀
  have hp := b64_projected_span (u t₀) z₀ ((hspan t₀ ht₀).trans hz₀)
  have hd : Module.finrank ℂ (Submodule.span ℂ
      (Set.range fun k => b64_negPart (u t₀ k))) = 3 := by
    rw [hp, ← b64_negFrame_span_aux]
    exact (b60_weil_dimensions z₀).2
  have hselect : ∃ σ : Fin 3 → ι,
      Submodule.span ℂ (Set.range fun j => b64_negPart (u t₀ (σ j))) =
        Submodule.span ℂ (Set.range (b64_negFrame z₀)) := by
    have hex := Submodule.exists_fun_fin_finrank_span_eq ℂ (Set.range fun k => b64_negPart (u t₀ k))
    rw [hd] at hex
    obtain ⟨f, hf, hfs, _⟩ := hex
    choose σ hσ using hf
    refine ⟨σ, ?_⟩
    have he : (fun j => b64_negPart (u t₀ (σ j))) = f := funext hσ
    rw [he, hfs, hp]
  obtain ⟨σ, hσ⟩ := hselect
  let A : E → Matrix (Fin 3) (Fin 3) ℂ :=
    fun t => b64_headBlock fun j => b64_negPart (u t (σ j))
  have hA : ∀ i j, ContinuousOn (fun t => A t i j) W := by
    intro i j
    simpa only [A, b64_headBlock, Matrix.of_apply, b64_negPart_repr, ite_true] using
      hu (σ j) (0, Fin.castAdd 3 i)
  have hc : ContinuousOn (fun t => (A t).det) W := by
    simp only [Matrix.det_apply']
    fun_prop
  have hunit := (b64_graphCoord_of_span_aux z₀ _ hσ).1
  have hd₀ : (A t₀).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
  have hn := (hc.continuousAt (hW.mem_nhds ht₀)).eventually_ne hd₀
  obtain ⟨W', hsub, hopen, hmem⟩ := mem_nhds_iff.mp (Filter.inter_mem (hW.mem_nhds ht₀) hn)
  refine ⟨W', hopen, hmem, fun t ht => (hsub ht).1, σ, ?_⟩
  intro t ht
  have htW := (hsub ht).1
  have htunit : IsUnit (A t) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (hsub ht).2)
  refine ⟨htunit, ?_⟩
  obtain ⟨z, hz⟩ := hF t htW
  have hp := b64_projected_span (u t) z ((hspan t htW).trans hz)
  have hle : Submodule.span ℂ (Set.range fun j => b64_negPart (u t (σ j))) ≤
      Submodule.span ℂ (Set.range (b64_negFrame z)) := by
    rw [← hp]
    exact Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨σ j, rfl⟩)
  rw [hz, b64_negFrame_span_aux]
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [finrank_span_eq_card (b64_linearIndependent_of_head _ htunit)]
  rw [← b64_negFrame_span_aux]
  exact (b60_weil_dimensions z).2.symm


theorem b64_coordOf_analyticOnNhd_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι : Type*} [Fintype ι]
    (u : E → ι → ℂ ⊗[ℤ] b60_Lattice) (F : E → Submodule ℂ (ℂ ⊗[ℤ] b60_Lattice))
    (W : Set E) (hW : IsOpen W)
    (hu : ∀ k p, AnalyticOnNhd ℂ (fun t => b60c_eigenBasis.repr (u t k) p) W)
    (hspan : ∀ t ∈ W, Submodule.span ℂ (Set.range (u t)) = F t)
    (hF : ∀ t ∈ W, ∃ z : Fin 9 → ℂ, F t = b60_F z) :
    AnalyticOnNhd ℂ (fun t => b64_coordOf (F t)) W := by
  intro t₀ ht₀
  obtain ⟨W', hopen, hmem, hsub, σ, hσ⟩ := b64_local_subframe_aux u F W hW
    (fun k p => (hu k p).continuousOn) hspan hF t₀ ht₀
  let v : E → Fin 3 → ℂ ⊗[ℤ] b60_Lattice := fun t j => b64_negPart (u t (σ j))
  have hv : ∀ j p, AnalyticOnNhd ℂ (fun t => b60c_eigenBasis.repr (v t j) p) W' := by
    intro j p
    simp only [v, b64_negPart_repr]
    split_ifs
    · exact (hu (σ j) p).mono hsub
    · exact analyticOnNhd_const
  have ha := b64_graphCoord_analyticOnNhd_aux v W' hv (fun t ht => (hσ t ht).1)
  have heq : (fun t => b64_coordOf (F t)) =ᶠ[𝓝 t₀] (fun t => b64_graphCoord (v t)) := by
    filter_upwards [hopen.mem_nhds hmem] with t ht
    obtain ⟨z, hz⟩ := hF t (hsub ht)
    have hs : Submodule.span ℂ (Set.range (v t)) =
        Submodule.span ℂ (Set.range (b64_negFrame z)) := by
      rw [(hσ t ht).2, hz, b64_negFrame_span_aux]
    rw [hz, b64_coordOf_eq_aux, (b64_graphCoord_of_span_aux z _ hs).2]
  exact (ha t₀ hmem).congr heq.symm


end HodgeLean.Foundations.Program
