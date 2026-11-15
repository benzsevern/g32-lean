import HodgeLean.Foundations.CMWeilClassesDefs
import HodgeLean.Adapters.F1575WeilDescent

/-! # Proofs for the Weil classes spec for a general CM field (stage A5)

The agent's working file. Fill every proof hole. **Do not change the statement of
any `_aux` theorem**: `CMWeilClasses.lean` (frozen) restates each one and must still typecheck.
Helper lemmas may be added freely, in this file or in new files; prefix them `a5_`.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
attribute [local instance 100] LieRing.ofAssociativeRing
open scoped TensorProduct
namespace HodgeLean.Foundations
open NumberField

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

section General

variable {L : Type*} [CommRing L] [Algebra ℚ L]

omit [FiniteDimensional ℚ V] in
/-- The concatenation of bases of the joint eigenspaces `W_{e(v)}`, for an injective family `e`
of embeddings, is linearly independent (A2a S1). -/
theorem a5_linearIndependent_concat (ι : L →ₐ[ℚ] Module.End ℚ V) {P : Type*}
    (e : P → (L →ₐ[ℚ] ℂ)) (he : Function.Injective e) {m : ℕ}
    (b : ∀ v : P, Module.Basis (Fin m) ℂ (cmEigenspace ι (e v))) :
    LinearIndependent ℂ (fun p : P × Fin m => (b p.1 p.2 : ℂ ⊗[ℚ] V)) := by
  classical
  have hind : iSupIndep (fun v : P => cmEigenspace ι (e v)) :=
    (spec_a2a_iSupIndep ι).comp he
  rw [linearIndependent_iff']
  intro s g hg p hp
  let w : P → ℂ ⊗[ℚ] V := fun v =>
    ∑ i : Fin m, (if (v, i) ∈ s then g (v, i) else 0) • (b v i : ℂ ⊗[ℚ] V)
  have hw : ∀ v, w v ∈ cmEigenspace ι (e v) := fun v =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b v i).2
  have hsum : ∑ v ∈ s.image Prod.fst, w v = 0 := by
    rw [← hg]
    simp only [w, ite_smul, zero_smul]
    rw [← Finset.sum_product' (f := fun v i =>
      if (v, i) ∈ s then g (v, i) • (b v i : ℂ ⊗[ℚ] V) else 0)]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext q
    simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_image, Finset.mem_univ, and_true]
    exact ⟨fun h => h.2, fun h => ⟨⟨q, h, rfl⟩, h⟩⟩
  have hw0 := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp hind (s.image Prod.fst) w
    (fun v _ => hw v) hsum p.1 (Finset.mem_image_of_mem _ hp)
  have hli := (b p.1).linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  have := hli (fun i => if (p.1, i) ∈ s then g (p.1, i) else 0) (by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, ZeroMemClass.coe_zero]
    exact hw0) p.2
  simpa [hp] using this

omit [FiniteDimensional ℚ V] in
/-- The top exterior power of a subspace with a basis `B` of size `n` is the line of `∧_j B_j`,
and that wedge is nonzero. -/
theorem a5_top_range {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (W : Submodule K E) {n : ℕ} (B : Module.Basis (Fin n) K W) :
    LinearMap.range (exteriorPower.map n W.subtype) =
        K ∙ exteriorPower.ιMulti K n (fun j => (B j : E)) ∧
      exteriorPower.ιMulti K n (fun j => (B j : E)) ≠ 0 := by
  have hB : exteriorPower.ιMulti K n (fun j => B j) ≠ 0 := by
    intro h
    have := congrArg (exteriorPower.alternatingMapLinearEquiv B.det) h
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, map_zero] at this
    exact one_ne_zero (B.det_self.symm.trans this)
  have hmap : exteriorPower.ιMulti K n (fun j => (B j : E)) =
      exteriorPower.map n W.subtype (exteriorPower.ιMulti K n (fun j => B j)) := by
    rw [exteriorPower.map_apply_ιMulti]; rfl
  have hinj : Function.Injective (exteriorPower.map n W.subtype) :=
    exteriorPower.map_injective_field W.subtype_injective
  have := Module.Finite.of_basis B
  have htop : (K ∙ exteriorPower.ιMulti K n (fun j => B j)) = ⊤ := by
    rw [← finrank_eq_one_iff_of_nonzero _ hB, exteriorPower.finrank_eq,
      Module.finrank_eq_card_basis B, Fintype.card_fin, Nat.choose_self]
  refine ⟨?_, ?_⟩
  · rw [LinearMap.range_eq_map, ← htop, Submodule.map_span, Set.image_singleton, hmap]
  · rw [hmap]
    intro h
    exact hB (hinj (h.trans (map_zero _).symm))

set_option linter.unusedSectionVars false in
theorem spec_a5_range_exteriorPower_cmPlusPart_aux (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) (d : ℚ)
    {m n : ℕ} (b : ∀ v : cmPlusEmb L u d, Module.Basis (Fin m) ℂ (cmEigenspace ι v.1))
    (σ : Fin n ≃ cmPlusEmb L u d × Fin m) :
    LinearMap.range (exteriorPower.map n (cmPlusPart ι u d).subtype) =
        ℂ ∙ exteriorPower.ιMulti ℂ n
          (fun j => ((b (σ j).1 (σ j).2 : cmEigenspace ι (σ j).1.1) : ℂ ⊗[ℚ] V)) ∧
      exteriorPower.ιMulti ℂ n
          (fun j => ((b (σ j).1 (σ j).2 : cmEigenspace ι (σ j).1.1) : ℂ ⊗[ℚ] V)) ≠ 0 := by
  set F : Fin n → ℂ ⊗[ℚ] V := fun j => (b (σ j).1 (σ j).2 : ℂ ⊗[ℚ] V) with hF
  have hli : LinearIndependent ℂ F :=
    (a5_linearIndependent_concat ι Subtype.val Subtype.val_injective b).comp σ σ.injective
  have hspan : Submodule.span ℂ (Set.range F) = cmPlusPart ι u d := by
    refine le_antisymm (Submodule.span_le.mpr ?_) (iSup₂_le fun τ hτ => ?_)
    · rintro _ ⟨j, rfl⟩
      exact (le_iSup₂_of_le (σ j).1.1 (σ j).1.2 le_rfl : cmEigenspace ι (σ j).1.1 ≤
        cmPlusPart ι u d) (b (σ j).1 (σ j).2).2
    · intro x hx
      have hx' : x = ∑ i, (b ⟨τ, hτ⟩).repr ⟨x, hx⟩ i • (b ⟨τ, hτ⟩ i : ℂ ⊗[ℚ] V) := by
        have := congrArg Subtype.val ((b ⟨τ, hτ⟩).sum_repr ⟨x, hx⟩).symm
        simpa only [Submodule.coe_sum, Submodule.coe_smul] using this
      rw [hx']
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      refine ⟨σ.symm (⟨τ, hτ⟩, i), ?_⟩
      have h := σ.apply_symm_apply (⟨τ, hτ⟩, i)
      simp only [hF]
      generalize σ (σ.symm (⟨τ, hτ⟩, i)) = p at h ⊢
      subst h
      rfl
  let B : Module.Basis (Fin n) ℂ (cmPlusPart ι u d) :=
    (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan)
  have hB : (fun j => (B j : ℂ ⊗[ℚ] V)) = F := by
    funext j
    simp [B, Module.Basis.span_apply]
  have := a5_top_range (cmPlusPart ι u d) B
  rw [hB] at this
  exact this

omit [FiniteDimensional ℚ V] in
/-- The base-changed pullback, read through `powerBaseChange`: `z ↦ Σ_i a_i z ⊗ e_i`. -/
theorem a5_powerBaseChange_cmPowerPullback (R : Subalgebra ℚ (Module.End ℚ V)) {r : ℕ}
    (a : Fin r → R) (z : ℂ ⊗[ℚ] V) :
    WeilPower.powerBaseChange r ((cmPowerPullback R a).baseChange ℂ z) =
      ∑ i, ((a i : Module.End ℚ V).baseChange ℂ z) ⊗ₜ[ℂ] (Pi.single i 1 : Fin r → ℂ) := by
  induction z using TensorProduct.inductionOn with
  | tmul c v =>
    simp only [cmPowerPullback, LinearMap.baseChange_tmul, LinearMap.sum_apply,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
      TensorProduct.mk_apply, TensorProduct.tmul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [WeilPower.powerBaseChange, LinearEquiv.trans_apply,
      TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply, WeilPower.multiplicityEquiv_one]
    congr 1
    ext j
    simp only [Pi.single_apply]
    split_ifs <;> simp
  | add z w hz hw => simp only [map_add, hz, hw, TensorProduct.add_tmul, Finset.sum_add_distrib]

omit [FiniteDimensional ℚ V] in
/-- The eigenvalue equation of a vector of `W_τ`. -/
theorem a5_mem_cmEigenspace {ι : L →ₐ[ℚ] Module.End ℚ V} {τ : L →ₐ[ℚ] ℂ} {x : ℂ ⊗[ℚ] V}
    (hx : x ∈ cmEigenspace ι τ) (a : L) : (ι a).baseChange ℂ x = τ a • x := by
  simp only [cmEigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hx
  exact hx a

set_option linter.unusedSectionVars false in
theorem spec_a5_cmPowerPullback_baseChange_aux (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ)
    {r : ℕ} (a : Fin r → L) (x : ℂ ⊗[ℚ] V) (hx : x ∈ cmEigenspace ι τ) :
    (cmPowerPullback ι.range (a5_cmCoeff ι a)).baseChange ℂ x =
      (WeilPower.powerBaseChange (V := V) r).symm (x ⊗ₜ[ℂ] (fun i => τ (a i))) := by
  apply (WeilPower.powerBaseChange (V := V) r).injective
  rw [a5_powerBaseChange_cmPowerPullback, LinearEquiv.apply_symm_apply]
  simp only [a5_cmCoeff, a5_mem_cmEigenspace hx, TensorProduct.smul_tmul, ← TensorProduct.tmul_sum]
  congr 1
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

set_option linter.unusedSectionVars false in
theorem spec_a5_map_cmPowerPullback_ιMulti_aux (ι : L →ₐ[ℚ] Module.End ℚ V) {r n : ℕ}
    (κ : Fin n → (L →ₐ[ℚ] ℂ)) (x : Fin n → ℂ ⊗[ℚ] V) (hx : ∀ j, x j ∈ cmEigenspace ι (κ j))
    (a : Fin r → L) :
    exteriorPower.map n ((cmPowerPullback ι.range (a5_cmCoeff ι a)).baseChange ℂ)
        (exteriorPower.ιMulti ℂ n x) =
      a5_cmDet r x (fun j i => κ j (a i)) := by
  rw [exteriorPower.map_apply_ιMulti, a5_cmDet]
  congr 1
  funext j
  exact spec_a5_cmPowerPullback_baseChange_aux ι (κ j) a (x j) (hx j)

set_option linter.unusedSectionVars false in
theorem spec_a5_cmPowerPullback_conj_aux (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) {d : ℚ}
    (hd : 0 < d) (v : cmPlusEmb L u d) (y : ℂ ⊗[ℚ] V)
    (hy : y ∈ cmEigenspace ι (cmConjEmbedding v.1)) (hy0 : y ≠ 0) :
    (cmPowerPullback ι.range (a5_cmCoeff ι (fun _ : Fin 1 => u))).baseChange ℂ y =
        (WeilPower.powerBaseChange (V := V) 1).symm
          (y ⊗ₜ[ℂ] (fun _ => -HodgeBlocks.WeilAction.omegaC d)) ∧
      (cmPowerPullback ι.range (a5_cmCoeff ι (fun _ : Fin 1 => u))).baseChange ℂ y ≠
        (WeilPower.powerBaseChange (V := V) 1).symm
          (y ⊗ₜ[ℂ] (fun _ => HodgeBlocks.WeilAction.omegaC d)) := by
  have hconj : cmConjEmbedding v.1 u = -HodgeBlocks.WeilAction.omegaC d := by
    change starRingEnd ℂ (v.1 u) = _
    rw [v.2, HodgeBlocks.WeilAction.omegaC, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hω : HodgeBlocks.WeilAction.omegaC d ≠ 0 := by
    rw [HodgeBlocks.WeilAction.omegaC]
    refine mul_ne_zero Complex.I_ne_zero ?_
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  have h1 := spec_a5_cmPowerPullback_baseChange_aux ι (cmConjEmbedding v.1)
    (fun _ : Fin 1 => u) y hy
  simp only [hconj] at h1
  refine ⟨h1, ?_⟩
  rw [h1]
  intro h
  have h2 := congrArg ((TensorProduct.rid ℂ (ℂ ⊗[ℚ] V)).toLinearMap ∘ₗ
    (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).lTensor (ℂ ⊗[ℚ] V))
    ((WeilPower.powerBaseChange (V := V) 1).symm.injective h)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul,
    LinearMap.proj_apply, LinearEquiv.coe_coe, TensorProduct.rid_tmul] at h2
  have h3 : (2 * HodgeBlocks.WeilAction.omegaC d) • y = 0 := by
    rw [two_mul, add_smul]
    nth_rewrite 2 [← h2]
    rw [neg_smul, add_neg_cancel]
  exact hy0 ((smul_eq_zero.mp h3).resolve_left (mul_ne_zero two_ne_zero hω))

omit [FiniteDimensional ℚ V] in
theorem a5_mem_cmEigenspace_iff (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ)
    (x : ℂ ⊗[ℚ] V) : x ∈ cmEigenspace ι τ ↔ ∀ a : L, (ι a).baseChange ℂ x = τ a • x := by
  simp [cmEigenspace]

omit [FiniteDimensional ℚ V] in
theorem a5_map_mem_cmEigenspace (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ)
    (X : Module.End ℂ (ℂ ⊗[ℚ] V)) (hX : ∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X)
    {x : ℂ ⊗[ℚ] V} (hx : x ∈ cmEigenspace ι τ) : X x ∈ cmEigenspace ι τ := by
  rw [a5_mem_cmEigenspace_iff] at hx ⊢
  intro a
  have h := LinearMap.congr_fun (hX a) x
  simp only [Module.End.mul_apply] at h
  rw [← h, hx a, map_smul]

omit [FiniteDimensional ℚ V] in
theorem a5_eq_sum_left (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V)
    (τ : L →ₐ[ℚ] ℂ) {m : ℕ}
    (b : Module.Basis (Fin m) ℂ (cmEigenspace ι τ))
    (c : Module.Basis (Fin m) ℂ (cmEigenspace ι (cmConjEmbedding τ)))
    (hbc : ∀ i j, E.baseChange ℂ (b i) (c j) = if i = j then 1 else 0)
    (z : ℂ ⊗[ℚ] V) (hz : z ∈ cmEigenspace ι τ) :
    z = ∑ j, E.baseChange ℂ z (c j) • (b j : ℂ ⊗[ℚ] V) := by
  have hs := b.sum_repr ⟨z, hz⟩
  have hz' : z = ∑ k, b.repr ⟨z, hz⟩ k • (b k : ℂ ⊗[ℚ] V) := by
    have := congrArg Subtype.val hs
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul] at this
    exact this.symm
  have hE : ∀ j, E.baseChange ℂ z (c j) = b.repr ⟨z, hz⟩ j := by
    intro j
    conv_lhs => rw [hz']
    simp [map_sum, LinearMap.sum_apply, hbc]
  simp_rw [hE]
  exact hz'

omit [FiniteDimensional ℚ V] in
theorem a5_eq_sum_right (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V)
    (τ : L →ₐ[ℚ] ℂ) {m : ℕ}
    (b : Module.Basis (Fin m) ℂ (cmEigenspace ι τ))
    (c : Module.Basis (Fin m) ℂ (cmEigenspace ι (cmConjEmbedding τ)))
    (hbc : ∀ i j, E.baseChange ℂ (b i) (c j) = if i = j then 1 else 0)
    (w : ℂ ⊗[ℚ] V) (hw : w ∈ cmEigenspace ι (cmConjEmbedding τ)) :
    w = ∑ j, E.baseChange ℂ (b j) w • (c j : ℂ ⊗[ℚ] V) := by
  have hs := c.sum_repr ⟨w, hw⟩
  have hw' : w = ∑ k, c.repr ⟨w, hw⟩ k • (c k : ℂ ⊗[ℚ] V) := by
    have := congrArg Subtype.val hs
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul] at this
    exact this.symm
  have hE : ∀ j, E.baseChange ℂ (b j) w = c.repr ⟨w, hw⟩ j := by
    intro j
    conv_lhs => rw [hw']
    simp [map_sum, hbc]
  simp_rw [hE]
  exact hw'

theorem spec_a5_cmTheta_mem_exteriorHodgeClasses_aux
    (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)
    (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V) (u : L)
    (hGk : HodgeLieIsGk H hH E ι.range (ι u)) (τ : L →ₐ[ℚ] ℂ) {m : ℕ}
    (b : Module.Basis (Fin m) ℂ (cmEigenspace ι τ))
    (c : Module.Basis (Fin m) ℂ (cmEigenspace ι (cmConjEmbedding τ)))
    (hbc : ∀ i j, E.baseChange ℂ (b i) (c j) = if i = j then 1 else 0)
    (r : ℕ) (x x' : Fin r → ℂ) :
    a5_cmTheta r (fun i => (b i : ℂ ⊗[ℚ] V)) (fun i => (c i : ℂ ⊗[ℚ] V)) x x' ∈
      WeilPower.exteriorHodgeClasses H hH r 2 := by
  rw [WeilPower.mem_exteriorHodgeClasses_iff]
  intro X hX
  rw [hGk, spec_a2b_mem_complexSpan_gkLie_iff] at hX
  obtain ⟨hc, hs, -, -⟩ := hX
  let φ : (ℂ ⊗[ℚ] V) →ₗ[ℂ] ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ)) :=
    (WeilPower.powerBaseChange (V := V) r).symm.toLinearMap ∘ₗ
      (TensorProduct.mk ℂ (ℂ ⊗[ℚ] V) (Fin r → ℂ)).flip x
  let ψ : (ℂ ⊗[ℚ] V) →ₗ[ℂ] ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ)) :=
    (WeilPower.powerBaseChange (V := V) r).symm.toLinearMap ∘ₗ
      (TensorProduct.mk ℂ (ℂ ⊗[ℚ] V) (Fin r → ℂ)).flip x'
  let β : (ℂ ⊗[ℚ] V) →ₗ[ℂ] (ℂ ⊗[ℚ] V) →ₗ[ℂ] ⋀[ℂ]^2 (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))) :=
    (InvariantsExterior.wedgePair.compl₂ ψ).comp φ
  have hβ : ∀ z w, β z w = exteriorPower.ιMulti ℂ 2
      ![(WeilPower.powerBaseChange (V := V) r).symm (z ⊗ₜ[ℂ] x),
        (WeilPower.powerBaseChange (V := V) r).symm (w ⊗ₜ[ℂ] x')] := fun z w => rfl
  have hP : ∀ (y : ℂ ⊗[ℚ] V) (t : Fin r → ℂ),
      WeilPower.powerAction r X ((WeilPower.powerBaseChange (V := V) r).symm (y ⊗ₜ[ℂ] t)) =
        (WeilPower.powerBaseChange (V := V) r).symm (X y ⊗ₜ[ℂ] t) := by
    intro y t
    simp [WeilPower.powerAction]
  have hD : ∀ z w, InvariantsExterior.exteriorDer 2 (WeilPower.powerAction r X) (β z w) =
      β (X z) w + β z (X w) := by
    intro z w
    rw [hβ, ← InvariantsExterior.wedgePair_apply, InvariantsExterior.exteriorDer_wedgePair,
      hP, hP]
    rfl
  have hθ : a5_cmTheta r (fun i => (b i : ℂ ⊗[ℚ] V)) (fun i => (c i : ℂ ⊗[ℚ] V)) x x' =
      ∑ i, β (b i) (c i) := rfl
  rw [hθ, map_sum]
  simp_rw [hD]
  rw [Finset.sum_add_distrib]
  have h1 : ∀ i, β (X (b i)) (c i) =
      ∑ j, E.baseChange ℂ (X (b i)) (c j) • β (b j) (c i) := by
    intro i
    conv_lhs => rw [a5_eq_sum_left ι E τ b c hbc (X (b i))
      (a5_map_mem_cmEigenspace ι τ X hc (b i).2)]
    simp [map_sum, LinearMap.sum_apply]
  have h2 : ∀ i, β (b i) (X (c i)) =
      ∑ j, E.baseChange ℂ (b j) (X (c i)) • β (b i) (c j) := by
    intro i
    conv_lhs => rw [a5_eq_sum_right ι E τ b c hbc (X (c i))
      (a5_map_mem_cmEigenspace ι _ X hc (c i).2)]
    simp [map_sum]
  simp_rw [h1, h2]
  rw [Finset.sum_comm (f := fun i j => E.baseChange ℂ (b j) (X (c i)) • β (b i) (c j)),
    ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  rw [hs, neg_smul, neg_add_cancel]

set_option linter.unusedSectionVars false in
theorem spec_a5_range_exteriorPower_cmPlusPart_subsingleton_aux [Subsingleton V]
    (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) (d : ℚ) {n : ℕ} (hn : 0 < n) :
    LinearMap.range (exteriorPower.map n (cmPlusPart ι u d).subtype) = ⊥ := by
  have : Subsingleton (cmPlusPart ι u d) := inferInstance
  rw [LinearMap.range_eq_bot]
  refine LinearMap.ext_on_range (exteriorPower.ιMulti_span ℂ n _) fun v => ?_
  have hv : v = Function.update v ⟨0, hn⟩ 0 := Subsingleton.elim _ _
  rw [LinearMap.zero_apply, hv, AlternatingMap.map_update_zero, map_zero]

/-- An exterior power of positive degree of a trivial module is trivial. -/
theorem a5_subsingleton_exteriorPower_of_subsingleton {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Subsingleton M] {n : ℕ} (hn : 0 < n) : Subsingleton (⋀[ℂ]^n M) := by
  have h : Submodule.span ℂ (Set.range (exteriorPower.ιMulti ℂ n (M := M))) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro _ ⟨v, rfl⟩
    have hv : v = fun _ => 0 := Subsingleton.elim _ _
    subst hv
    exact (exteriorPower.ιMulti ℂ n).map_coord_zero ⟨0, hn⟩ rfl
  rw [exteriorPower.ιMulti_span] at h
  refine subsingleton_of_forall_eq 0 fun a => ?_
  have ha : a ∈ (⊥ : Submodule ℂ (⋀[ℂ]^n M)) := h ▸ Submodule.mem_top
  exact (Submodule.mem_bot ℂ).1 ha

theorem spec_a5_subsingleton_exteriorPower_zero_aux {n : ℕ} (hn : 0 < n) :
    Subsingleton (⋀[ℂ]^n (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin 0 → ℚ)))) := by
  have : Subsingleton (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin 0 → ℚ))) :=
    (WeilPower.powerBaseChange (V := V) 0).toEquiv.subsingleton
  exact a5_subsingleton_exteriorPower_of_subsingleton hn

set_option linter.unusedSectionVars false in
theorem spec_a5_cmPlusPart_eq_of_unique_aux (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) (d : ℚ)
    (v : cmPlusEmb L u d) (hv : ∀ w : cmPlusEmb L u d, w = v) :
    cmPlusPart ι u d = cmEigenspace ι v.1 := by
  refine le_antisymm (iSup₂_le fun τ hτ => ?_) (le_iSup₂_of_le v.1 v.2 le_rfl)
  rw [show τ = v.1 from congrArg Subtype.val (hv ⟨τ, hτ⟩)]

theorem spec_a5_span_rat_ne_top_aux {r : ℕ} (hr : 0 < r) (τ₁ τ₂ : L →ₐ[ℚ] ℂ) (h : τ₁ ≠ τ₂) :
    Submodule.span ℂ (Set.range (fun q : Fin r → ℚ =>
      fun (τ : L →ₐ[ℚ] ℂ) (i : Fin r) => τ (algebraMap ℚ L (q i)))) ≠ ⊤ := by
  classical
  let i₀ : Fin r := ⟨0, hr⟩
  let f : ((L →ₐ[ℚ] ℂ) → Fin r → ℂ) →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) i₀ ∘ₗ
        LinearMap.proj (R := ℂ) (φ := fun _ : L →ₐ[ℚ] ℂ => Fin r → ℂ) τ₁) -
      (LinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) i₀ ∘ₗ
        LinearMap.proj (R := ℂ) (φ := fun _ : L →ₐ[ℚ] ℂ => Fin r → ℂ) τ₂)
  have hle : Submodule.span ℂ (Set.range (fun q : Fin r → ℚ =>
      fun (τ : L →ₐ[ℚ] ℂ) (i : Fin r) => τ (algebraMap ℚ L (q i)))) ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    simp [f, AlgHom.commutes]
  intro htop
  have hw : (fun (τ : L →ₐ[ℚ] ℂ) (_ : Fin r) => if τ = τ₁ then (1 : ℂ) else 0) ∈
      LinearMap.ker f := hle (htop ▸ Submodule.mem_top)
  simp [f, Ne.symm h] at hw

end General

/-- Dual functionals to a linearly independent family. -/
theorem a5_exists_dual_of_linearIndependent {M ι : Type*} [AddCommGroup M] [Module ℂ M]
    [DecidableEq ι] {x : ι → M} (hx : LinearIndependent ℂ x) :
    ∃ φ : ι → Module.Dual ℂ M, ∀ a b, φ a (x b) = if b = a then 1 else 0 := by
  choose φ hφ using fun a => LinearMap.exists_extend (Finsupp.lapply a ∘ₗ hx.repr)
  refine ⟨φ, fun a b => ?_⟩
  have h := LinearMap.congr_fun (hφ a) ⟨x b, Submodule.subset_span ⟨b, rfl⟩⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h
  rw [h, hx.repr_eq_single b _ rfl, Finsupp.lapply_apply, Finsupp.single_apply]

/-- The `2 × 2` determinant `F ∧ F'` of two linear forms, as an alternating map. -/
theorem a5_det_compLinearMap_apply {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F F' : M →ₗ[ℂ] ℂ) (v : Fin 2 → M) :
    (Pi.basisFun ℂ (Fin 2)).det.compLinearMap (LinearMap.pi ![F, F']) v =
      F (v 0) * F' (v 1) - F (v 1) * F' (v 0) := by
  rw [AlternatingMap.compLinearMap_apply, Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply]

theorem spec_a5_cmDet_not_mem_span_rat_aux (x : Fin 2 → ℂ ⊗[ℚ] V) (hx : LinearIndependent ℂ x) :
    a5_cmDet 2 x ![Pi.single 0 1, Pi.single 1 1] ∉ Submodule.span ℂ
      (Set.range (fun q : Fin 2 → ℚ => a5_cmDet 2 x (fun _ i => (q i : ℂ)))) := by
  obtain ⟨φ, hφ⟩ := a5_exists_dual_of_linearIndependent hx
  have h00 : φ 0 (x 0) = 1 := by simp [hφ]
  have h01 : φ 0 (x 1) = 0 := by simp [hφ]
  have h10 : φ 1 (x 0) = 0 := by simp [hφ]
  have h11 : φ 1 (x 1) = 1 := by simp [hφ]
  let G : Fin 2 → Fin 2 → (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin 2 → ℚ))) →ₗ[ℂ] ℂ := fun a i =>
    (TensorProduct.lid ℂ ℂ).toLinearMap ∘ₗ TensorProduct.map (φ a) (LinearMap.proj i) ∘ₗ
      (WeilPower.powerBaseChange (V := V) 2).toLinearMap
  have hG : ∀ a i (z : ℂ ⊗[ℚ] V) (y : Fin 2 → ℂ),
      G a i ((WeilPower.powerBaseChange (V := V) 2).symm (z ⊗ₜ[ℂ] y)) = φ a z * y i := by
    intro a i z y
    simp [G, mul_comm]
  let ω := (Pi.basisFun ℂ (Fin 2)).det.compLinearMap (LinearMap.pi ![G 0 0, G 1 1]) -
    (Pi.basisFun ℂ (Fin 2)).det.compLinearMap (LinearMap.pi ![G 0 1, G 1 0])
  let Ω := exteriorPower.alternatingMapLinearEquiv ω
  have hΩ : ∀ y : Fin 2 → Fin 2 → ℂ, Ω (a5_cmDet 2 x y) =
      (y 0 0 * y 1 1 - y 0 1 * y 1 0) := by
    intro y
    simp only [Ω, a5_cmDet, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, ω,
      sub_apply, a5_det_compLinearMap_apply, hG, h00, h01, h10, h11]
    ring
  intro hmem
  have hle : Submodule.span ℂ
      (Set.range (fun q : Fin 2 → ℚ => a5_cmDet 2 x (fun _ i => (q i : ℂ)))) ≤
        LinearMap.ker Ω := by
    rw [Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hΩ]
    ring
  have h := hle hmem
  rw [LinearMap.mem_ker, hΩ] at h
  simp at h

section NumberField

variable {L : Type*} [Field L] [NumberField L]

/-- Dedekind–Artin: the embeddings `L → ℂ` are `ℂ`-linearly independent as functions. -/
theorem a5_linearIndependent_embeddings :
    LinearIndependent ℂ (fun τ : L →ₐ[ℚ] ℂ => (τ : L → ℂ)) := by
  have h := (linearIndependent_monoidHom L ℂ).comp
    (fun τ : L →ₐ[ℚ] ℂ => (τ.toRingHom.toMonoidHom : L →* ℂ))
    (fun τ₁ τ₂ h => AlgHom.ext fun x => DFunLike.congr_fun h x)
  exact h

theorem spec_a5_span_embeddings_eq_top_aux (r : ℕ) :
    Submodule.span ℂ (Set.range (fun a : Fin r → L =>
      fun (τ : L →ₐ[ℚ] ℂ) (i : Fin r) => τ (a i))) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne)
    inferInstance
  have hvan : ∀ a : Fin r → L, f (fun τ i => τ (a i)) = 0 := fun a => by
    have : f (fun τ i => τ (a i)) ∈ (Submodule.span ℂ (Set.range (fun a : Fin r → L =>
        fun (τ : L →ₐ[ℚ] ℂ) (i : Fin r) => τ (a i)))).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨a, rfl⟩)
    rwa [hmap, Submodule.mem_bot] at this
  let c : (L →ₐ[ℚ] ℂ) → Fin r → ℂ := fun τ i => f (Pi.single τ (Pi.single i 1))
  have hf_apply : ∀ w : (L →ₐ[ℚ] ℂ) → Fin r → ℂ, f w = ∑ τ, ∑ i, c τ i * w τ i := by
    intro w
    conv_lhs => rw [show w = ∑ τ, ∑ i, w τ i • Pi.single τ (Pi.single i 1) by
      ext τ i; simp [Finset.sum_apply, Pi.single_apply, ite_apply]]
    simp [c, map_sum, mul_comm]
  have hc : ∀ i τ, c τ i = 0 := by
    intro i
    have := Fintype.linearIndependent_iff.1 a5_linearIndependent_embeddings (fun τ => c τ i)
    apply this
    funext l
    have h1 := hvan (Pi.single i l)
    have hs : ∀ (τ : L →ₐ[ℚ] ℂ) (j : Fin r),
        τ ((Pi.single i l : Fin r → L) j) = if j = i then τ l else 0 := by
      intro τ j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [hf_apply] at h1
    simpa [hs, mul_ite, Finset.sum_ite_eq'] using h1
  apply hf
  ext w
  simp [hf_apply, hc]

/-- The embedding vector `ρ(a) = (τ(a_i))_{τ, i}` of `a ∈ L^r`, as a `ℚ`-linear map.
Source: PW v0.3, proof of Theorem 4.2, paragraph "Weil classes" (the map
`ρ : L^r ⊗ ℂ → U^e`, restricted to `L^r`). -/
def a5_embVec (L : Type*) [Field L] [NumberField L] (r : ℕ) :
    (Fin r → L) →ₗ[ℚ] ((L →ₐ[ℚ] ℂ) → Fin r → ℂ) where
  toFun a := fun τ i => τ (a i)
  map_add' a b := by
    funext τ i
    simp
  map_smul' q a := by
    funext τ i
    exact τ.toLinearMap.map_smul q (a i)

example (r : ℕ) (a : Fin r → L) (τ : L →ₐ[ℚ] ℂ) (i : Fin r) :
    a5_embVec L r a τ i = τ (a i) := rfl

set_option linter.unusedSectionVars false in
theorem spec_a5_cmDet_mem_span_aux (r : ℕ) {n : ℕ} (κ : Fin n → (L →ₐ[ℚ] ℂ))
    (x : Fin n → ℂ ⊗[ℚ] V) (y : (L →ₐ[ℚ] ℂ) → Fin r → ℂ) :
    a5_cmDet r x (fun j => y (κ j)) ∈ Submodule.span ℂ
      (Set.range (fun a : Fin r → L => a5_cmDet r x (fun j i => κ j (a i)))) := by
  classical
  let e := Module.finBasis ℚ (Fin r → L)
  let N := Module.finrank ℚ (Fin r → L)
  let ρ := a5_embVec L r
  let ρC : (Fin N → ℂ) →ₗ[ℂ] ((L →ₐ[ℚ] ℂ) → Fin r → ℂ) :=
    Fintype.linearCombination ℂ (fun k => ρ (e k))
  have hρ : ∀ a : Fin r → L, ρ a = ρC (fun k => ((e.repr a k : ℚ) : ℂ)) := by
    intro a
    conv_lhs => rw [← e.sum_repr a]
    rw [map_sum, Fintype.linearCombination_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Rat.cast_smul_eq_qsmul]
  have hsurj : y ∈ LinearMap.range ρC := by
    have hle : Submodule.span ℂ (Set.range (fun a : Fin r → L =>
        fun (τ : L →ₐ[ℚ] ℂ) (i : Fin r) => τ (a i))) ≤ LinearMap.range ρC := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact ⟨_, (hρ a).symm⟩
    rw [spec_a5_span_embeddings_eq_top_aux] at hle
    exact hle Submodule.mem_top
  obtain ⟨w, rfl⟩ := hsurj
  let g : Fin n → (Fin N → ℂ) →ₗ[ℂ] ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ)) := fun j =>
    (WeilPower.powerBaseChange (V := V) r).symm.toLinearMap ∘ₗ
      (TensorProduct.mk ℂ (ℂ ⊗[ℚ] V) (Fin r → ℂ) (x j)) ∘ₗ
      (LinearMap.proj (κ j)) ∘ₗ ρC
  let f : MultilinearMap ℂ (fun _ : Fin n => Fin N → ℂ) _ :=
    (exteriorPower.ιMulti ℂ n).toMultilinearMap.compLinearMap g
  have hf : ∀ w : Fin N → ℂ, f (fun _ => w) = a5_cmDet r x (fun j => ρC w (κ j)) := fun w => rfl
  rw [← hf]
  refine Submodule.span_mono ?_ (multilinear_diagonal_mem_span_rat f w)
  rintro _ ⟨q, rfl⟩
  refine ⟨∑ k, q k • e k, ?_⟩
  change _ = f (fun _ => fun i => ((q i : ℚ) : ℂ))
  rw [hf]
  have hq : ρC (fun k => ((q k : ℚ) : ℂ)) = ρ (∑ k, q k • e k) := by
    rw [hρ, e.repr_sum_self]
  rw [hq]
  rfl

theorem a5_conj_omegaC (d : ℚ) :
    starRingEnd ℂ (HodgeBlocks.WeilAction.omegaC d) = -HodgeBlocks.WeilAction.omegaC d := by
  simp [HodgeBlocks.WeilAction.omegaC]

theorem a5_cmConjEmbedding_cmConjEmbedding (τ : L →ₐ[ℚ] ℂ) :
    cmConjEmbedding (cmConjEmbedding τ) = τ := by
  ext a
  simp [cmConjEmbedding]

/-- Complex conjugation `τ ↦ τ̄`, from the embeddings with `τ(u) = i√d` onto those with
`τ(-u) = i√d`.
Source: PW v0.3, proof of Theorem 4.2, paragraph "Weil classes" (the conjugate part
`⊗_v det W^v̄`, `v̄ = conj ∘ σ_v`); `cmConjEmbedding` (`Foundations/CMSplittingDefs.lean`). -/
def a5_conjPlusEquiv (u : L) (d : ℚ) : cmPlusEmb L u d ≃ cmPlusEmb L (-u) d where
  toFun v := ⟨cmConjEmbedding v.1, by
    simp only [map_neg, cmConjEmbedding, AlgHom.comp_apply, RingHom.toRatAlgHom_apply]
    rw [v.2, a5_conj_omegaC, neg_neg]⟩
  invFun w := ⟨cmConjEmbedding w.1, by
    have h : w.1 u = -HodgeBlocks.WeilAction.omegaC d := by
      rw [← neg_neg (w.1 u), ← map_neg, w.2]
    simp only [cmConjEmbedding, AlgHom.comp_apply, RingHom.toRatAlgHom_apply]
    rw [h, map_neg, a5_conj_omegaC, neg_neg]⟩
  left_inv v := Subtype.ext (a5_cmConjEmbedding_cmConjEmbedding v.1)
  right_inv w := Subtype.ext (a5_cmConjEmbedding_cmConjEmbedding w.1)

example (u : L) (d : ℚ) (v : cmPlusEmb L u d) :
    (a5_conjPlusEquiv u d v).1 = cmConjEmbedding v.1 := rfl

theorem a5_range_map_subtype_congr {E : Type*} [AddCommGroup E] [Module ℂ E] (n : ℕ)
    {P Q : Submodule ℂ E} (h : P = Q) :
    LinearMap.range (exteriorPower.map n P.subtype) =
      LinearMap.range (exteriorPower.map n Q.subtype) := by
  subst h
  rfl

omit [FiniteDimensional ℚ V] in
theorem a5_exists_conj_basis (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) (d : ℚ) {m : ℕ}
    (b' : ∀ v : cmPlusEmb L u d,
      Module.Basis (Fin m) ℂ (cmEigenspace ι (cmConjEmbedding v.1))) :
    ∃ b'' : ∀ w : cmPlusEmb L (-u) d, Module.Basis (Fin m) ℂ (cmEigenspace ι w.1),
      ∀ w i, ((b'' w i : cmEigenspace ι w.1) : ℂ ⊗[ℚ] V) =
        ((b' ((a5_conjPlusEquiv u d).symm w) i :
          cmEigenspace ι (cmConjEmbedding ((a5_conjPlusEquiv u d).symm w).1)) : ℂ ⊗[ℚ] V) := by
  refine ⟨fun w => (b' ((a5_conjPlusEquiv u d).symm w)).map (LinearEquiv.ofEq _ _
    (congrArg (cmEigenspace ι) (a5_cmConjEmbedding_cmConjEmbedding w.1))), fun w i => ?_⟩
  rw [Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply]

omit [FiniteDimensional ℚ V] in
theorem a5_conj_basis_fun (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) (d : ℚ) {m : ℕ}
    (b' : ∀ v : cmPlusEmb L u d,
      Module.Basis (Fin m) ℂ (cmEigenspace ι (cmConjEmbedding v.1)))
    (b'' : ∀ w : cmPlusEmb L (-u) d, Module.Basis (Fin m) ℂ (cmEigenspace ι w.1))
    (hb : ∀ w i, ((b'' w i : cmEigenspace ι w.1) : ℂ ⊗[ℚ] V) =
      ((b' ((a5_conjPlusEquiv u d).symm w) i :
        cmEigenspace ι (cmConjEmbedding ((a5_conjPlusEquiv u d).symm w).1)) : ℂ ⊗[ℚ] V))
    {n : ℕ} (σ : Fin n ≃ cmPlusEmb L u d × Fin m) :
    (fun j => ((b'' ((σ.trans (Equiv.prodCongr (a5_conjPlusEquiv u d) (Equiv.refl (Fin m)))) j).1
        ((σ.trans (Equiv.prodCongr (a5_conjPlusEquiv u d) (Equiv.refl (Fin m)))) j).2 :
          cmEigenspace ι _) : ℂ ⊗[ℚ] V)) =
      fun j => ((b' (σ j).1 (σ j).2 : cmEigenspace ι (cmConjEmbedding (σ j).1.1)) :
        ℂ ⊗[ℚ] V) := by
  funext j
  have key : ∀ v' : cmPlusEmb L u d, v' = (σ j).1 →
      ((b' v' (σ j).2 : cmEigenspace ι (cmConjEmbedding v'.1)) : ℂ ⊗[ℚ] V) =
        ((b' (σ j).1 (σ j).2 : cmEigenspace ι (cmConjEmbedding (σ j).1.1)) : ℂ ⊗[ℚ] V) := by
    rintro _ rfl
    rfl
  rw [hb]
  exact key _ ((a5_conjPlusEquiv u d).symm_apply_apply _)

theorem spec_a5_weilClasses_baseChange_eq_aux (ι : L →ₐ[ℚ] Module.End ℚ V)
    {M : HodgeBlocks.QHodgeStructure 1 V} {d : ℚ} (A : HodgeBlocks.WeilAction M d) (u : L)
    (hJ : A.J = ι u) (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType) (hd : 0 < d)
    {m : ℕ} (b : ∀ v : cmPlusEmb L u d, Module.Basis (Fin m) ℂ (cmEigenspace ι v.1))
    (b' : ∀ v : cmPlusEmb L u d,
      Module.Basis (Fin m) ℂ (cmEigenspace ι (cmConjEmbedding v.1)))
    (σ : Fin (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) + Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) ≃
      cmPlusEmb L u d × Fin m) :
    ((A.weilClasses hH hW).baseChange ℂ).map
        (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := V)
          (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
            Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)))).toLinearMap =
      (ℂ ∙ exteriorPower.ιMulti ℂ _
          (fun j => ((b (σ j).1 (σ j).2 : cmEigenspace ι (σ j).1.1) : ℂ ⊗[ℚ] V))) ⊔
        (ℂ ∙ exteriorPower.ιMulti ℂ _
          (fun j => ((b' (σ j).1 (σ j).2 : cmEigenspace ι (cmConjEmbedding (σ j).1.1)) :
            ℂ ⊗[ℚ] V))) := by
  have hVs : A.Vs = cmPlusPart ι u d := (spec_a2a_cmPlusPart_eq_Vs ι A u hJ).symm
  have hVsbar : A.Vsbar = cmPlusPart ι (-u) d := by
    rw [HodgeBlocks.WeilAction.Vsbar, HodgeBlocks.WeilAction.Jc, hJ,
      ← spec_a2a_iSup_eq_eigenspace, cmPlusPart]
    refine iSup_congr fun τ => iSup_congr_Prop ?_ fun _ => rfl
    rw [map_neg, neg_eq_iff_eq_neg]
  have h := Adapters.weilClasses_baseChange_eq_topLines A hH hW hd
  dsimp only at h
  obtain ⟨b'', hb''⟩ := a5_exists_conj_basis ι u d b'
  let σ' := σ.trans (Equiv.prodCongr (a5_conjPlusEquiv u d) (Equiv.refl (Fin m)))
  have hfun := a5_conj_basis_fun ι u d b' b'' hb'' σ
  rw [h, a5_range_map_subtype_congr _ hVs, a5_range_map_subtype_congr _ hVsbar,
    (spec_a5_range_exteriorPower_cmPlusPart_aux ι u d b σ).1,
    (spec_a5_range_exteriorPower_cmPlusPart_aux ι (-u) d b'' σ').1, hfun]

end NumberField

end HodgeLean.Foundations
