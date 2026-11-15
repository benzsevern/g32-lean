import HodgeLean.Foundations.Program.CyclotomicWeilLinear
import HodgeLean.Papers.G32TransferDefs

noncomputable section
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers

namespace HodgeLean.Foundations

section Hodge

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
  {M : HodgeBlocks.QHodgeStructure 1 V} {m h : ℕ}

theorem cyc_eigenspace_eq_sup (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m))
    (hpres : ∀ a pq, (M.H pq).map ((cyc_scalar e a).baseChange ℂ) ≤ M.H pq)
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (t : cyc_Field m →ₐ[ℚ] ℂ) :
    cyc_eigenspace e t =
      (cyc_eigenspace e t ⊓ M.H (1, 0)) ⊔ (cyc_eigenspace e t ⊓ M.H (0, 1)) := by
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro x hx
  have hxH : x ∈ M.H (1, 0) ⊔ M.H (0, 1) := by rw [hH]; trivial
  obtain ⟨x10, hx10, x01, hx01, rfl⟩ := Submodule.mem_sup.mp hxH
  have hdis : Disjoint (M.H (1, 0)) (M.H (0, 1)) :=
    M.isInternal.submodule_iSupIndep.pairwiseDisjoint (by norm_num)
  have key : ∀ a, (cyc_scalar e a).baseChange ℂ x10 = t a • x10 ∧
      (cyc_scalar e a).baseChange ℂ x01 = t a • x01 := by
    intro a
    have heig := Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hx a)
    have h10 : (cyc_scalar e a).baseChange ℂ x10 - t a • x10 ∈ M.H (1, 0) :=
      sub_mem (hpres a (1, 0) ⟨x10, hx10, rfl⟩) ((M.H (1, 0)).smul_mem _ hx10)
    have h01 : (cyc_scalar e a).baseChange ℂ x01 - t a • x01 ∈ M.H (0, 1) :=
      sub_mem (hpres a (0, 1) ⟨x01, hx01, rfl⟩) ((M.H (0, 1)).smul_mem _ hx01)
    have hz : ((cyc_scalar e a).baseChange ℂ x10 - t a • x10) +
        ((cyc_scalar e a).baseChange ℂ x01 - t a • x01) = 0 := by
      rw [map_add, smul_add] at heig
      rw [← sub_eq_zero] at heig
      rw [← heig]
      abel
    have hz10 : (cyc_scalar e a).baseChange ℂ x10 - t a • x10 = 0 := by
      have hother : (cyc_scalar e a).baseChange ℂ x10 - t a • x10 ∈ M.H (0, 1) := by
        rw [eq_neg_of_add_eq_zero_left hz]
        exact (M.H (0, 1)).neg_mem h01
      exact (Submodule.mem_bot ℂ).mp (hdis.le_bot ⟨h10, hother⟩)
    rw [hz10, zero_add] at hz
    exact ⟨sub_eq_zero.mp hz10, sub_eq_zero.mp hz⟩
  apply Submodule.add_mem
  · refine Submodule.mem_sup_left ⟨?_, hx10⟩
    exact (Submodule.mem_iInf _).mpr fun a => Module.End.mem_eigenspace_iff.mpr (key a).1
  · refine Submodule.mem_sup_right ⟨?_, hx01⟩
    exact (Submodule.mem_iInf _).mpr fun a => Module.End.mem_eigenspace_iff.mpr (key a).2

theorem cyc_complexify_mem_exteriorPowerH {k : ℕ} (hhk : h = k + k)
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m))
    (hpres : ∀ a pq, (M.H pq).map ((cyc_scalar e a).baseChange ℂ) ≤ M.H pq)
    (hsig : ∀ t : cyc_Field m →ₐ[ℚ] ℂ,
      Module.finrank ℂ ↥(cyc_eigenspace e t ⊓ M.H (1, 0)) = k)
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) {w : ⋀[ℚ]^h V} (hw : w ∈ cyc_wedges e) :
    HodgeBlocks.complexify _ w ∈ M.exteriorPowerH (V := V) h ((k : ℤ), (k : ℤ)) := by
  subst hhk
  have hline : ∀ t, cyc_line e t ≤ (M.exteriorPowerH (V := V) (k + k) ((k : ℤ), (k : ℤ))).map
      (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := V) (k + k)).toLinearMap := by
    intro t
    let P := cyc_eigenspace e t ⊓ M.H (1, 0)
    let Q := cyc_eigenspace e t ⊓ M.H (0, 1)
    have hP : Module.finrank ℂ ↥P = k := hsig t
    have hdis : P ⊓ Q = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      have hd : Disjoint (M.H (1, 0)) (M.H (0, 1)) :=
        M.isInternal.submodule_iSupIndep.pairwiseDisjoint (by norm_num)
      exact hd.le_bot ⟨hx.1.2, hx.2.2⟩
    have hsup : cyc_eigenspace e t = P ⊔ Q := cyc_eigenspace_eq_sup e hpres hH t
    have hQ : Module.finrank ℂ ↥Q = Module.finrank ℂ ↥P := by
      have hsum := Submodule.finrank_sup_add_finrank_inf_eq P Q
      rw [hdis, finrank_bot, add_zero, ← hsup, cyc_finrank_eigenspace, hP] at hsum
      omega
    have h1 := HodgeBlocks.topExteriorPower_sup_le_wedgeType P Q hdis hQ
    rw [hP] at h1
    calc cyc_line e t = LinearMap.range (exteriorPower.map (k + k) (P ⊔ Q).subtype) :=
          HodgeBlocks.exteriorPower_map_subtype_range_eq_of_eq _ _ _ hsup
      _ ≤ HodgeBlocks.wedgeType P Q k k := h1
      _ ≤ _ := HodgeBlocks.WeilAction.wedgeType_le_exteriorPowerH_map M k P Q
          (fun x hx => hx.2) (fun x hx => hx.2)
  have hmap : HodgeBlocks.complexifyWedge (k + k) w ∈
      (M.exteriorPowerH (V := V) (k + k) ((k : ℤ), (k : ℤ))).map
        (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := V) (k + k)).toLinearMap :=
    (iSup_le hline) hw
  rw [← HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv_tmul, Submodule.mem_map_equiv,
    LinearEquiv.symm_apply_apply] at hmap
  exact hmap

end Hodge

section Quadratic

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
  {M : HodgeBlocks.QHodgeStructure 1 V} {m h : ℕ}

theorem cyc_topLines_eq_quadratic (hm : m = 3 ∨ m = 6) (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m))
    (u : cyc_Field m) (hu : u ^ 2 = -3) (B : HodgeBlocks.WeilAction M 3)
    (hJ : B.J = cyc_scalar e u) :
    ∃ τ : cyc_Field m →ₐ[ℚ] ℂ, cyc_eigenspace e τ = B.Vs ∧
      cyc_topLines e = LinearMap.range (exteriorPower.map h B.Vs.subtype) ⊔
        LinearMap.range (exteriorPower.map h B.Vsbar.subtype) := by
  have : NeZero m := ⟨by rcases hm with rfl | rfl <;> norm_num⟩
  let ω := HodgeBlocks.WeilAction.omegaC (3 : ℚ)
  have hF : Module.finrank ℚ (cyc_Field m) = 2 := by
    rw [cyc_finrank_field]
    rcases hm with rfl | rfl <;> decide
  have hu' : u ^ 2 = algebraMap ℚ (cyc_Field m) (-3) := by
    rw [hu, map_neg, map_ofNat]
  have hcard := spec_a2a_card_plus u (d := 3) (by norm_num) hu'
  rw [hF] at hcard
  have hone : Nat.card {τ : cyc_Field m →ₐ[ℚ] ℂ // τ u = ω} = 1 := by
    change Nat.card {τ : cyc_Field m →ₐ[ℚ] ℂ // τ u = HodgeBlocks.WeilAction.omegaC 3} = 1
    omega
  obtain ⟨hsub, ⟨⟨τp, hτp⟩⟩⟩ := Nat.card_eq_one_iff_unique.mp hone
  have huniq : ∀ τ : cyc_Field m →ₐ[ℚ] ℂ, τ u = ω → τ = τp := fun τ hτ =>
    congrArg Subtype.val (hsub.elim ⟨τ, hτ⟩ ⟨τp, hτp⟩)
  have hω2 : ω ^ 2 = -((3 : ℚ) : ℂ) := HodgeBlocks.WeilAction.omegaC_sq (by norm_num)
  have hpm : ∀ τ : cyc_Field m →ₐ[ℚ] ℂ, τ u = ω ∨ τ u = -ω := by
    intro τ
    have hsq : (τ u) ^ 2 = ω ^ 2 := by
      rw [← map_pow, hu, map_neg, map_ofNat, hω2]
      norm_num
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  let τm := cmConjEmbedding τp
  have hτm : τm u = -ω := by
    change starRingEnd ℂ (τp u) = -ω
    rw [hτp]
    exact HodgeBlocks.WeilAction.conj_omegaC
  have hconj : ∀ τ : cyc_Field m →ₐ[ℚ] ℂ, cmConjEmbedding (cmConjEmbedding τ) = τ := by
    intro τ
    ext x
    simp [cmConjEmbedding]
  have huniqm : ∀ τ : cyc_Field m →ₐ[ℚ] ℂ, τ u = -ω → τ = τm := by
    intro τ hτ
    have h1 : cmConjEmbedding τ u = ω := by
      change starRingEnd ℂ (τ u) = ω
      rw [hτ, map_neg, HodgeBlocks.WeilAction.conj_omegaC, neg_neg]
    rw [← hconj τ, huniq _ h1]
  have heig : ∀ (ω' : ℂ) (τ' : cyc_Field m →ₐ[ℚ] ℂ), τ' u = ω' →
      (∀ τ : cyc_Field m →ₐ[ℚ] ℂ, τ u = ω' → τ = τ') →
      cyc_eigenspace e τ' = Module.End.eigenspace B.Jc ω' := by
    intro ω' τ' hτ' hu'
    change cyc_eigenspace e τ' = Module.End.eigenspace (B.J.baseChange ℂ) ω'
    rw [hJ]
    change cmEigenspace (cyc_rep e) τ' = Module.End.eigenspace ((cyc_rep e u).baseChange ℂ) ω'
    rw [← spec_a2a_iSup_eq_eigenspace]
    apply le_antisymm
    · exact le_iSup₂_of_le τ' hτ' le_rfl
    · exact iSup₂_le fun τ hτ => (hu' τ hτ) ▸ le_rfl
  have hVs : cyc_eigenspace e τp = B.Vs := heig ω τp hτp huniq
  have hVsbar : cyc_eigenspace e τm = B.Vsbar := heig (-ω) τm hτm huniqm
  refine ⟨τp, hVs, ?_⟩
  rw [← HodgeBlocks.exteriorPower_map_subtype_range_eq_of_eq _ _ _ hVs,
    ← HodgeBlocks.exteriorPower_map_subtype_range_eq_of_eq _ _ _ hVsbar]
  apply le_antisymm
  · refine iSup_le fun τ => ?_
    rcases hpm τ with hτ | hτ
    · rw [huniq τ hτ]
      exact le_sup_left
    · rw [huniqm τ hτ]
      exact le_sup_right
  · exact sup_le (le_iSup (cyc_line e) τp) (le_iSup (cyc_line e) τm)

end Quadratic

section Degree

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

theorem cyc_heq_cast [Module.Finite ℚ (HQ X 1)] (μ : CupProduct X)
    (P Q : Submodule ℂ (ℂ ⊗[ℚ] HQ X 1)) (a b c : ℕ) (hb : b = c) (ha : a = c) :
    HEq ((((LinearMap.range (exteriorPower.map a P.subtype) ⊔
        LinearMap.range (exteriorPower.map a Q.subtype)).restrictScalars ℚ).comap
          (HodgeBlocks.complexifyWedge a)).map (μ.cupWedgeMap a))
      ((((LinearMap.range (exteriorPower.map b P.subtype) ⊔
        LinearMap.range (exteriorPower.map b Q.subtype)).restrictScalars ℚ).comap
          (HodgeBlocks.complexifyWedge b)).map
            ((HQ.castEquiv X hb).toLinearMap ∘ₗ μ.cupWedgeMap b)) := by
  subst hb
  subst ha
  apply heq_of_eq
  congr 1

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
theorem cyc_le_iff_of_heq (j j' : ℕ) (hj : j = j') (S : Submodule ℚ (HQ X (2 * j)))
    (S' : Submodule ℚ (HQ X (2 * j'))) (hS : HEq S S')
    (T : ∀ n : ℕ, Submodule ℚ (HQ X (2 * n))) : S ≤ T j ↔ S' ≤ T j' := by
  subst hj
  obtain rfl := eq_of_heq hS
  rfl

end Degree

theorem cyc_eigenline_decomposition_aux {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {m h : ℕ} (hm : 3 ≤ m) (hh : 0 < h)
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) :
    (∀ t : cyc_Field m →ₐ[ℚ] ℂ,
      Module.finrank ℂ ↥(cyc_eigenspace e t) = h ∧
        Module.finrank ℂ ↥(cyc_line e t) = 1) ∧
      iSupIndep (cyc_line e) := by
  have : NeZero m := ⟨by omega⟩
  exact ⟨fun t => ⟨cyc_finrank_eigenspace e t, cyc_finrank_line e t⟩, cyc_line_iSupIndep hh e⟩

theorem cyc_descent_aux {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {m h : ℕ} (hm : 3 ≤ m) (hh : 0 < h)
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) :
    ((cyc_wedges e).baseChange ℂ).map
      (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := V) h).toLinearMap =
        cyc_topLines e := by
  have : NeZero m := ⟨by omega⟩
  exact cyc_descent_eq e

theorem cyc_rational_rank_aux {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {m h : ℕ} (hm : 3 ≤ m) (hh : 0 < h)
    (e : V ≃ₗ[ℚ] (Fin h → cyc_Field m)) :
    Module.finrank ℚ ↥(cyc_wedges e) = m.totient := by
  have : NeZero m := ⟨by omega⟩
  rw [cyc_finrank_wedges_eq, cyc_finrank_topLines hh, cyc_finrank_field]

theorem cyc_cohomology_rank_aux {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [GrpObj X] {μ : CupProduct X}
    (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology μ) {m k : ℕ}
    (A : letI := hT.finite
      cyc_Action (abelianVarietyCohomologyOf hF hB hD hT).weight1 m k) :
    letI := hT.finite;
    Module.finrank ℚ ↥(cyc_classSpace μ A.cyc_coordinates) = m.totient := by
  let := hT.finite
  change Module.finrank ℚ ↥((cyc_wedges A.cyc_coordinates).map
    (hT.cupWedgeEquiv (2 * k)).toLinearMap) = _
  rw [LinearEquiv.finrank_map_eq]
  exact cyc_rational_rank_aux A.cyc_order (Nat.mul_pos (by norm_num) A.cyc_positive) _

theorem cyc_classes_hodge_aux {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [GrpObj X] {μ : CupProduct X}
    (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology μ) {m k : ℕ}
    (A : letI := hT.finite
      cyc_Action (abelianVarietyCohomologyOf hF hB hD hT).weight1 m k)
    (hC : CupFiltered X μ) :
    letI := hT.finite;
    cyc_classSpace μ A.cyc_coordinates ≤ Hdg^k(X; ℚ) := by
  let := hT.finite
  rintro _ ⟨w, hw, rfl⟩
  have hH := h10_sup_h01_eq_top hF hB hD hT
  have hc := cyc_complexify_mem_exteriorPowerH (two_mul k) A.cyc_coordinates A.cyc_preserves
    A.cyc_signature hH hw
  refine (isHodgeClass_exteriorPower_iff hF hB hD hT hC k w).mp ?_
  rw [HodgeBlocks.IsHodgeClass, HodgeBlocks.WeilAction.weightCast_H]
  exact hc

theorem cyc_quadratic_comparison_aux {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [GrpObj X] {μ : CupProduct X}
    (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology μ) {m k : ℕ}
    (A : letI := hT.finite
      cyc_Action (abelianVarietyCohomologyOf hF hB hD hT).weight1 m k)
    (hm : m = 3 ∨ m = 6) (u : cyc_Field m) (hu : u ^ 2 = -3)
    (B : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3)
    (hW : letI := hT.finite; B.IsWeilType)
    (hJ : letI := hT.finite; B.J = cyc_scalar A.cyc_coordinates u) :
    letI := hT.finite;
    HEq (cyc_classSpace μ A.cyc_coordinates) (weilClassOf hF hB hD hT B hW) ∧
      (cyc_Algebraic μ A.cyc_coordinates ↔ WeilClassesAlgebraic hF hB hD hT B hW) := by
  let := hT.finite
  obtain ⟨τ, hVs, htop⟩ := cyc_topLines_eq_quadratic hm A.cyc_coordinates u hu B hJ
  have hk : Module.finrank ℂ
      ↥(B.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)) = k := by
    rw [← hVs]
    exact A.cyc_signature τ
  have heq : HEq (cyc_classSpace μ A.cyc_coordinates) (weilClassOf hF hB hD hT B hW) := by
    rw [cyc_classSpace, cyc_wedges, htop]
    exact cyc_heq_cast μ B.Vs B.Vsbar (2 * k) _ _ (two_mul _).symm (by rw [hk])
  refine ⟨heq, ?_⟩
  exact cyc_le_iff_of_heq k _ hk.symm _ _ heq (fun n => algebraicCycleClassSpan X n)

theorem cyc_g32_bridge_aux (P : g32t_Sixfold) {m k : ℕ}
    (A : letI := (torusCohomology_cupProductOf P.X).finite
      cyc_Action (abelianVarietyCohomologyOf (finiteBetti_abelian P.X)
        (spec_bettiDeRhamIso_abelian P.X) (hodgeDecomposition_of_abelian P.X)
        (torusCohomology_cupProductOf P.X)).weight1 m k)
    (hm : m = 3 ∨ m = 6) (u : cyc_Field m) (hu : u ^ 2 = -3)
    (hW : letI := (torusCohomology_cupProductOf P.X).finite; P.W.IsWeilType)
    (hJ : letI := (torusCohomology_cupProductOf P.X).finite; P.W.J = cyc_scalar A.cyc_coordinates u) :
    letI := (torusCohomology_cupProductOf P.X).finite;
    cyc_Algebraic (cupProductOf P.X) A.cyc_coordinates ↔ g32t_WeilAlg P := by
  have hc := (cyc_quadratic_comparison_aux (finiteBetti_abelian P.X)
    (spec_bettiDeRhamIso_abelian P.X) (hodgeDecomposition_of_abelian P.X)
    (torusCohomology_cupProductOf P.X) A hm u hu P.W hW hJ).2
  exact hc.trans ⟨fun h _ => h, fun h => h hW⟩

end HodgeLean.Foundations
