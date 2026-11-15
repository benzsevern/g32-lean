import HodgeLean.Foundations.CMCentreInvariants
import HodgeLean.Foundations.CMWeilClasses
import HodgeLean.Adapters.PowersVocabulary

/-! # Proofs for the model-assembly spec (stage A6)

The agent's working file. Fill every proof hole. **Do not change the statement of any `_aux`
theorem**: `CMModelAssembly.lean` (frozen) restates each one and must still typecheck.
Helper lemmas may be added freely, in this file or in new files; prefix them `a6_`.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] HodgeLean.Foundations.SchurWeyl.dualAddCommGroup
open scoped TensorProduct
namespace HodgeLean.Foundations
open InvariantsExterior NumberField WeilPower

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

section Unconditional

set_option linter.unusedSectionVars false in
theorem a6_mem_span_unit {M : Type*} [AddCommGroup M] [Module ℚ M] (v : ⋀[ℚ]^0 M) :
    v ∈ Submodule.span ℚ {exteriorPower.ιMulti ℚ 0 (Fin.elim0 : Fin 0 → M)} := by
  have hr : Set.range (exteriorPower.ιMulti ℚ 0 : (Fin 0 → M) → ⋀[ℚ]^0 M) =
      {exteriorPower.ιMulti ℚ 0 Fin.elim0} := by
    ext w
    constructor
    · rintro ⟨f, rfl⟩
      rw [Subsingleton.elim f Fin.elim0]
      rfl
    · rintro rfl
      exact ⟨_, rfl⟩
  rw [← hr, exteriorPower.ιMulti_span]
  trivial

set_option linter.unusedSectionVars false in
theorem a6_exteriorDer_zero {M : Type*} [AddCommGroup M] [Module ℂ M] (f : Module.End ℂ M) :
    exteriorDer 0 f = 0 := by
  ext v
  simp [exteriorDer_ιMulti]

set_option linter.unusedSectionVars false in
theorem spec_a6_degree_zero_aux (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V))
    (hH : DirectSum.IsInternal H) (R : Subalgebra ℚ (Module.End ℚ V)) {r n : ℕ}
    (D : Submodule ℚ (⋀[ℚ]^2 (V ⊗[ℚ] (Fin r → ℚ)))) (W : Submodule ℚ (⋀[ℚ]^n V)) :
    cmPowerSpan R D W 0 = ⊤ ∧ rationalExteriorHodge H hH r 0 = ⊤ := by
  refine ⟨eq_top_iff.mpr fun v _ => ?_, eq_top_iff.mpr fun v _ => ?_⟩
  · simp only [cmPowerSpan, Submodule.mem_iInf]
    intro F hF
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hF.unit_mem) (a6_mem_span_unit v)
  · change exteriorDer 0 (powerAction r (gradingOperator H hH)) (exteriorComplexify 0 v) = 0
    rw [a6_exteriorDer_zero]
    rfl

theorem a6_exteriorHodge_diag_eq_bot (M : HodgeBlocks.QHodgeStructure 1 V) (r : ℕ) {k : ℕ}
    (hk : Odd k) (p : ℤ) : exteriorHodge M.H r k (p, p) = ⊥ := by
  rw [exteriorHodge, Submodule.span_eq_bot]
  rintro v ⟨ps, x, w, hx, hps, rfl⟩
  by_cases h : ∀ i, (ps i).1 + (ps i).2 = 1
  · exfalso
    have h1 := congrArg (fun z : ℤ × ℤ => z.1 + z.2) hps
    simp only [Prod.fst_sum, Prod.snd_sum, ← Finset.sum_add_distrib, h] at h1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] at h1
    obtain ⟨m, hm⟩ := hk
    omega
  · simp only [not_forall] at h
    obtain ⟨i, hi⟩ := h
    have hxi : x i = 0 := by
      have := hx i
      rwa [M.supported _ hi, Submodule.mem_bot] at this
    apply AlternatingMap.map_coord_zero _ i
    simp [hxi]

theorem spec_a6_rationalExteriorHodge_odd_aux (M : HodgeBlocks.QHodgeStructure 1 V) (r : ℕ)
    {k : ℕ} (hk : Odd k) :
    rationalExteriorHodge M.H M.isInternal r k = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  have hv' : exteriorComplexify k v ∈
      LinearMap.ker (exteriorDer k (powerAction r (gradingOperator M.H M.isInternal))) := hv
  have hbot : (⨆ p : ℤ, exteriorHodge M.H r k (p, p)) = ⊥ := by
    simp [a6_exteriorHodge_diag_eq_bot M r hk]
  rw [ker_exterior_hodge_grading M.H M.isInternal, hbot, Submodule.mem_bot] at hv'
  have he : exteriorBaseChange k ((1 : ℂ) ⊗ₜ[ℚ] v) = exteriorComplexify k v := by
    change (exteriorBaseChange k).toLinearMap _ = _
    rw [exteriorBaseChange_eq_lift, LinearMap.liftBaseChange_tmul, one_smul]
  rw [hv', LinearEquiv.map_eq_zero_iff, Module.FaithfullyFlat.one_tmul_eq_zero_iff] at he
  exact he

set_option linter.unusedSectionVars false in
theorem a6_subsingleton_exteriorPower {M : Type*} [AddCommGroup M] [Module ℚ M]
    [Subsingleton M] (k : ℕ) : Subsingleton (⋀[ℚ]^(k + 1) M) := by
  have hsub : Set.range (exteriorPower.ιMulti ℚ (k + 1) : (Fin (k + 1) → M) → _) ⊆ {0} := by
    rintro _ ⟨f, rfl⟩
    exact AlternatingMap.map_coord_zero _ 0 (Subsingleton.elim _ _)
  rw [subsingleton_iff_forall_eq 0]
  intro v
  have hv : v ∈ (⊤ : Submodule ℚ (⋀[ℚ]^(k + 1) M)) := trivial
  rw [← exteriorPower.ιMulti_span] at hv
  have := Submodule.span_mono hsub hv
  rwa [Submodule.span_singleton_eq_bot.mpr rfl, Submodule.mem_bot] at this

set_option linter.unusedSectionVars false in
theorem spec_a6_eq_cmPowerSpan_of_subsingleton_aux (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V))
    (hH : DirectSum.IsInternal H) (R : Subalgebra ℚ (Module.End ℚ V)) {r n : ℕ}
    (hV : Subsingleton (V ⊗[ℚ] (Fin r → ℚ))) (W : Submodule ℚ (⋀[ℚ]^n V)) (k : ℕ) :
    rationalExteriorHodge H hH r k = cmPowerSpan R (rationalExteriorHodge H hH r 2) W k := by
  cases k with
  | zero =>
    obtain ⟨h1, -⟩ := spec_a6_degree_zero_aux H hH R (rationalExteriorHodge H hH r 2) W
    obtain ⟨-, h2⟩ := spec_a6_degree_zero_aux H hH R (rationalExteriorHodge H hH r 2) W
    rw [h1, h2]
  | succ k =>
    have := a6_subsingleton_exteriorPower (M := V ⊗[ℚ] (Fin r → ℚ)) k
    exact Subsingleton.elim _ _

set_option linter.unusedSectionVars false in
theorem a6_range_eq_adjoin {L : Type*} [Field L] [Algebra ℚ L] (hL : Module.finrank ℚ L = 2)
    (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) {d : ℚ} (hd : 0 < d)
    (hu : u ^ 2 = algebraMap ℚ L (-d)) : ι.range = Algebra.adjoin ℚ {ι u} := by
  have hu' : u ∉ (⊥ : Subalgebra ℚ L) := by
    rw [Algebra.mem_bot]
    rintro ⟨q, rfl⟩
    rw [← map_pow] at hu
    have hq := (algebraMap ℚ L).injective hu
    nlinarith [sq_nonneg q]
  have htop : Algebra.adjoin ℚ {u} = ⊤ := by
    have := Subalgebra.isSimpleOrder_of_finrank_prime ℚ L (hL ▸ Nat.prime_two)
    rcases eq_bot_or_eq_top (Algebra.adjoin ℚ {u}) with h | h
    · exact absurd (h ▸ Algebra.self_mem_adjoin_singleton ℚ u) hu'
    · exact h
  rw [← Algebra.map_top, ← htop, AlgHom.map_adjoin, Set.image_singleton]

set_option linter.unusedSectionVars false in
theorem spec_a6_cmPowerSpan_range_eq_divisorPulledWeilSpan_aux {L : Type*} [Field L]
    [Algebra ℚ L] (hL : Module.finrank ℚ L = 2) (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) {d : ℚ}
    (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d)) {r n : ℕ}
    (D : Submodule ℚ (⋀[ℚ]^2 (V ⊗[ℚ] (Fin r → ℚ)))) (W : Submodule ℚ (⋀[ℚ]^n V)) (k : ℕ) :
    cmPowerSpan ι.range D W k = divisorPulledWeilSpan (ι u) D W k := by
  have hJ : (ι u).comp (ι u) = (-d) • LinearMap.id := by
    have h : (ι u).comp (ι u) = ι (u ^ 2) := by rw [pow_two, map_mul]; rfl
    rw [h, hu, AlgHom.commutes, Module.algebraMap_end_eq_smul_id]
  rw [a6_range_eq_adjoin hL ι u hd hu, Adapters.spec_pw0_cmPowerSpan_adjoin_eq _ hJ]

end Unconditional

section CM

variable {L : Type*} [Field L] [NumberField L] [IsCMField L]

theorem spec_a6_exists_powerModel_fin_aux (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d)) (r : ℕ) {e : ℕ}
    (ε : Fin e ≃ cmPlusEmb L u d) :
    ∃ e' : (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))) ≃ₗ[ℂ]
        MultiSpace ℂ (fun j => cmEigenspace ι (ε j).1) (fun _ => Fin r → ℂ)
          (fun _ => Fin r → ℂ),
      (∀ (j : Fin e) (x : cmEigenspace ι (ε j).1) (w : Fin r → ℂ),
        e' ((powerBaseChange (V := V) r).symm ((x : ℂ ⊗[ℚ] V) ⊗ₜ[ℂ] w)) =
          Pi.single j (x ⊗ₜ[ℂ] w, 0)) ∧
      (∀ (j : Fin e) (y : cmEigenspace ι (cmConjEmbedding (ε j).1)) (w : Fin r → ℂ),
        e' ((powerBaseChange (V := V) r).symm ((y : ℂ ⊗[ℚ] V) ⊗ₜ[ℂ] w)) =
          Pi.single j (0, crossPairing (E.baseChange ℂ) (cmEigenspace ι (ε j).1)
            (cmEigenspace ι (cmConjEmbedding (ε j).1)) y ⊗ₜ[ℂ] w)) ∧
      (∀ X : Module.End ℂ (ℂ ⊗[ℚ] V),
        (∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X) →
        (∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y)) →
        ∀ z (j : Fin e), e' (powerAction r X z) j =
          multiplicityLie ℂ (cmEigenspace ι (ε j).1) (Fin r → ℂ) (Fin r → ℂ)
            (cmBlock ι (ε j).1 X) (e' z j)) := by
  classical
  obtain ⟨e, h1, h2, h3⟩ := spec_a2b_powerModel ι E hE hRos u hd hu r
  let φ : cmPlusEmb L u d → Type _ := fun v =>
    InvariantsExterior.Space ℂ (cmEigenspace ι v.1) (Fin r → ℂ) (Fin r → ℂ)
  let P := (LinearEquiv.piCongrLeft ℂ φ ε).symm
  have hP : ∀ g j, P g j = g (ε j) := fun _ _ => rfl
  refine ⟨e.trans P, ?_, ?_, ?_⟩
  · intro j x w
    funext j'
    rw [LinearEquiv.trans_apply, hP, h1]
    by_cases hj : j' = j
    · subst hj
      simp
    · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne (ε.injective.ne hj)]
  · intro j y w
    funext j'
    rw [LinearEquiv.trans_apply, hP, h2]
    by_cases hj : j' = j
    · subst hj
      simp
    · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne (ε.injective.ne hj)]
  · intro X hX hskew z j
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hP, hP, h3 X hX hskew z (ε j)]

set_option linter.unusedSectionVars false in
theorem spec_a6_map_cmTheta_aux (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V)
    (u : L) {d : ℚ} (r : ℕ) {e : ℕ} (ε : Fin e ≃ cmPlusEmb L u d)
    (e' : (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))) ≃ₗ[ℂ]
        MultiSpace ℂ (fun j => cmEigenspace ι (ε j).1) (fun _ => Fin r → ℂ)
          (fun _ => Fin r → ℂ))
    (he₁ : ∀ (j : Fin e) (x : cmEigenspace ι (ε j).1) (w : Fin r → ℂ),
      e' ((powerBaseChange (V := V) r).symm ((x : ℂ ⊗[ℚ] V) ⊗ₜ[ℂ] w)) =
        Pi.single j (x ⊗ₜ[ℂ] w, 0))
    (he₂ : ∀ (j : Fin e) (y : cmEigenspace ι (cmConjEmbedding (ε j).1)) (w : Fin r → ℂ),
      e' ((powerBaseChange (V := V) r).symm ((y : ℂ ⊗[ℚ] V) ⊗ₜ[ℂ] w)) =
        Pi.single j (0, crossPairing (E.baseChange ℂ) (cmEigenspace ι (ε j).1)
          (cmEigenspace ι (cmConjEmbedding (ε j).1)) y ⊗ₜ[ℂ] w))
    (j : Fin e) {m : ℕ} (b : Module.Basis (Fin m) ℂ (cmEigenspace ι (ε j).1))
    (c : Fin m → cmEigenspace ι (cmConjEmbedding (ε j).1))
    (hbc : ∀ i i', E.baseChange ℂ (b i) (c i') = if i = i' then 1 else 0)
    (x x' : Fin r → ℂ) :
    ExteriorAlgebra.map e'.toLinearMap
        ((a5_cmTheta r (fun i => (b i : ℂ ⊗[ℚ] V)) (fun i => (c i : ℂ ⊗[ℚ] V)) x x' :
          ExteriorAlgebra ℂ (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))))) =
      blockTheta (K := ℂ) (W := fun j => cmEigenspace ι (ε j).1) (U := fun _ => Fin r → ℂ)
        (U' := fun _ => Fin r → ℂ) j x x' := by
  have hc : ∀ i, crossPairing (E.baseChange ℂ) (cmEigenspace ι (ε j).1)
      (cmEigenspace ι (cmConjEmbedding (ε j).1)) (c i) = b.dualBasis i := by
    intro i
    refine b.ext fun i' => ?_
    rw [Module.Basis.dualBasis_apply_self]
    exact hbc i' i
  rw [blockTheta, theta_eq_sum b]
  simp only [a5_cmTheta, Submodule.coe_sum, map_sum, wedgePair_apply,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.map_apply_ιMulti]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  funext k
  fin_cases k
  · simp only [Function.comp_apply, LinearEquiv.coe_coe, Fin.zero_eta, Matrix.cons_val_zero,
      he₁]
    rfl
  · simp only [Function.comp_apply, LinearEquiv.coe_coe, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_zero, he₂, hc]
    rfl

/-- Reordering the factors of a product of `ι`'s in the exterior algebra costs a sign that
depends only on the reordering of the indices. -/
theorem a6_prod_map_ι_perm {R M α : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {l l' : List α} (h : l.Perm l') :
    ∃ s : R, s * s = 1 ∧ ∀ f : α → M,
      (l.map fun a => ExteriorAlgebra.ι R (f a)).prod =
        s • (l'.map fun a => ExteriorAlgebra.ι R (f a)).prod := by
  induction h with
  | nil => exact ⟨1, one_mul 1, fun f => by simp⟩
  | cons x _ ih =>
    obtain ⟨s, hs, h⟩ := ih
    exact ⟨s, hs, fun f => by simp only [List.map_cons, List.prod_cons, h f, mul_smul_comm]⟩
  | swap x y l =>
    refine ⟨-1, by norm_num, fun f => ?_⟩
    simp only [List.map_cons, List.prod_cons, ← mul_assoc, neg_one_smul]
    rw [← neg_mul]
    congr 1
    exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨s, hs, h₁⟩ := ih₁
    obtain ⟨t, ht, h₂⟩ := ih₂
    refine ⟨s * t, ?_, fun f => by rw [h₁, h₂, smul_smul]⟩
    calc s * t * (s * t) = (s * s) * (t * t) := by ring
      _ = 1 := by rw [hs, ht, one_mul]

/-- An alternating map on a free module of rank `m`, at a family of `m` vectors, is the
determinant times its value on a basis. -/
theorem a6_alternatingMap_eq_det_smul {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {m : ℕ} (b : Module.Basis (Fin m) R M)
    (g : M [⋀^Fin m]→ₗ[R] N) (v : Fin m → M) : g v = b.det v • g b := by
  have : g = (b.det).smulRight (g b) := by
    refine Module.Basis.ext_alternating b fun i h => ?_
    let σ : Equiv.Perm (Fin m) := Equiv.ofBijective i (Finite.injective_iff_bijective.1 h)
    change g (b ∘ σ) = ((b.det).smulRight (g b)) (b ∘ σ)
    simp [AlternatingMap.map_perm, Module.Basis.det_self]
  conv_lhs => rw [this]
  simp

/-- Changing the basis in a top wedge of linear images scales it by one nonzero scalar,
independent of the linear map. -/
theorem a6_ιMulti_basis_change {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] {m m' : ℕ} (b : Module.Basis (Fin m) K M)
    (b' : Module.Basis (Fin m') K M) :
    ∃ s : K, s ≠ 0 ∧ ∀ φ : M →ₗ[K] N,
      ExteriorAlgebra.ιMulti K m (fun i => φ (b i)) =
        s • ExteriorAlgebra.ιMulti K m' (fun i => φ (b' i)) := by
  have h : m' = m := by
    simpa using (Fintype.card_congr (b.indexEquiv b')).symm
  subst h
  refine ⟨b'.det b, (b'.isUnit_det b).ne_zero, fun φ => ?_⟩
  exact a6_alternatingMap_eq_det_smul b' ((ExteriorAlgebra.ιMulti K _).compLinearMap φ) b


theorem a6_prod_ofFn_smul {K A : Type*} [CommRing K] [Ring A] [Algebra K A] {e : ℕ}
    (s : Fin e → K) (x : Fin e → A) :
    (List.ofFn fun v => s v • x v).prod = (List.ofFn s).prod • (List.ofFn x).prod := by
  induction e with
  | zero => simp
  | succ e ih =>
    simp only [List.ofFn_succ, List.prod_cons, ih, smul_mul_smul_comm]

/-- A wedge of the images of bases of blocks, taken in any order, is one nonzero multiple of the
ordered product over the blocks of the top wedges of other bases, independent of the maps. -/
theorem a6_ιMulti_sigma_blocks {K N : Type*} [Field K] [AddCommGroup N] [Module K N] {e : ℕ}
    {M : Fin e → Type*} [∀ v, AddCommGroup (M v)] [∀ v, Module K (M v)] {m m' : Fin e → ℕ}
    (b : ∀ v, Module.Basis (Fin (m v)) K (M v)) (b' : ∀ v, Module.Basis (Fin (m' v)) K (M v))
    {n : ℕ} (σ : Fin n ≃ (v : Fin e) × Fin (m v)) :
    ∃ s : K, s ≠ 0 ∧ ∀ φ : ∀ v, M v →ₗ[K] N,
      ExteriorAlgebra.ιMulti K n (fun t => φ (σ t).1 (b (σ t).1 (σ t).2)) =
        s • (List.ofFn fun v => ExteriorAlgebra.ιMulti K (m' v) (fun i => φ v (b' v i))).prod := by
  choose s hs h using fun v => a6_ιMulti_basis_change (N := N) (b' v) (b v)
  let L₀ : List ((v : Fin e) × Fin (m v)) := (List.ofFn fun v => List.ofFn fun i => ⟨v, i⟩).flatten
  have hperm : (List.ofFn σ).Perm L₀ := by
    refine (List.perm_ext_iff_of_nodup (List.nodup_ofFn.mpr σ.injective) ?_).mpr fun a => ?_
    · refine List.nodup_flatten.mpr ⟨fun l hl => ?_, List.pairwise_ofFn.mpr fun i j hij => ?_⟩
      · obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hl
        exact List.nodup_ofFn.mpr fun i i' hii => by simpa using hii
      · refine List.disjoint_left.mpr fun a ha ha' => ?_
        obtain ⟨_, rfl⟩ := List.mem_ofFn.mp ha
        obtain ⟨_, h'⟩ := List.mem_ofFn.mp ha'
        exact hij.ne (congrArg Sigma.fst h').symm
    · simp only [List.mem_ofFn, L₀, List.mem_flatten]
      exact ⟨fun _ => ⟨_, ⟨a.1, rfl⟩, List.mem_ofFn.mpr ⟨a.2, rfl⟩⟩,
        fun _ => ⟨σ.symm a, σ.apply_symm_apply a⟩⟩
  obtain ⟨t, ht, hσ⟩ := a6_prod_map_ι_perm (R := K) (M := N) hperm
  have hprod : (List.ofFn s).prod ≠ 0 := by
    intro h0
    rw [List.prod_eq_zero_iff] at h0
    obtain ⟨v, hv⟩ := List.mem_ofFn.mp h0
    exact hs v hv
  refine ⟨t * ((List.ofFn s).prod)⁻¹, mul_ne_zero (left_ne_zero_of_mul_eq_one ht)
    (inv_ne_zero hprod), fun φ => ?_⟩
  simp only [h, a6_prod_ofFn_smul]
  rw [smul_smul, mul_assoc, inv_mul_cancel₀ hprod, mul_one]
  have hl : ExteriorAlgebra.ιMulti K n (fun t => φ (σ t).1 (b (σ t).1 (σ t).2)) =
      ((List.ofFn σ).map fun a => ExteriorAlgebra.ι K (φ a.1 (b a.1 a.2))).prod := by
    rw [ExteriorAlgebra.ιMulti_apply, List.map_ofFn]
    rfl
  have hr : (List.ofFn fun v => ExteriorAlgebra.ιMulti K (m v) (fun i => φ v (b v i))).prod =
      (L₀.map fun a => ExteriorAlgebra.ι K (φ a.1 (b a.1 a.2))).prod := by
    simp only [L₀, List.map_flatten, List.prod_flatten, List.map_ofFn, ExteriorAlgebra.ιMulti_apply]
    simp only [Function.comp_def, List.map_ofFn]
  rw [hl, hr, hσ]

set_option linter.unusedSectionVars false in
theorem spec_a6_map_cmDet_aux (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) {d : ℚ} (r : ℕ) {e : ℕ}
    (ε : Fin e ≃ cmPlusEmb L u d)
    (e' : (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))) ≃ₗ[ℂ]
        MultiSpace ℂ (fun j => cmEigenspace ι (ε j).1) (fun _ => Fin r → ℂ)
          (fun _ => Fin r → ℂ))
    (he₁ : ∀ (j : Fin e) (x : cmEigenspace ι (ε j).1) (w : Fin r → ℂ),
      e' ((powerBaseChange (V := V) r).symm ((x : ℂ ⊗[ℚ] V) ⊗ₜ[ℂ] w)) =
        Pi.single j (x ⊗ₜ[ℂ] w, 0))
    {m : Fin e → ℕ} (b : ∀ j, Module.Basis (Fin (m j)) ℂ (cmEigenspace ι (ε j).1))
    {n : ℕ} (σ : Fin n ≃ (j : Fin e) × Fin (m j)) :
    ∃ s : ℂ, s ≠ 0 ∧ ∀ y : Fin e → Fin r → ℂ,
      ExteriorAlgebra.map e'.toLinearMap
          ((a5_cmDet r (fun t => (b (σ t).1 (σ t).2 : ℂ ⊗[ℚ] V)) (fun t => y (σ t).1) :
            ExteriorAlgebra ℂ (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))))) =
        s • multiDetW (K := ℂ) (W := fun j => cmEigenspace ι (ε j).1)
          (U := fun _ => Fin r → ℂ) (U' := fun _ => Fin r → ℂ) y := by
  obtain ⟨s, hs, H⟩ := a6_ιMulti_sigma_blocks
    (N := MultiSpace ℂ (fun j => cmEigenspace ι (ε j).1) (fun _ => Fin r → ℂ)
      (fun _ => Fin r → ℂ)) b (fun j => Module.finBasis ℂ (cmEigenspace ι (ε j).1)) σ
  refine ⟨s, hs, fun y => ?_⟩
  let φ : ∀ j, cmEigenspace ι (ε j).1 →ₗ[ℂ]
      MultiSpace ℂ (fun j => cmEigenspace ι (ε j).1) (fun _ => Fin r → ℂ)
        (fun _ => Fin r → ℂ) := fun j =>
    (LinearMap.single ℂ (fun j => Space ℂ (cmEigenspace ι (ε j).1) (Fin r → ℂ) (Fin r → ℂ)) j)
      ∘ₗ vectorIn (y j)
  calc _ = ExteriorAlgebra.ιMulti ℂ n (fun t => φ (σ t).1 (b (σ t).1 (σ t).2)) := by
        simp only [a5_cmDet, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.map_apply_ιMulti]
        congr 1
        funext t
        simp only [Function.comp_apply, LinearEquiv.coe_coe, he₁]
        rfl
    _ = _ := H φ
    _ = _ := by
        congr 1
        simp only [multiDetW, detW_eq, exteriorPower.ιMulti_apply_coe,
          ExteriorAlgebra.map_apply_ιMulti]
        rfl

theorem spec_a6_map_cmDet_conj_aux (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V)
    (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (r : ℕ) {e : ℕ} (ε : Fin e ≃ cmPlusEmb L u d)
    (e' : (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))) ≃ₗ[ℂ]
        MultiSpace ℂ (fun j => cmEigenspace ι (ε j).1) (fun _ => Fin r → ℂ)
          (fun _ => Fin r → ℂ))
    (he₂ : ∀ (j : Fin e) (y : cmEigenspace ι (cmConjEmbedding (ε j).1)) (w : Fin r → ℂ),
      e' ((powerBaseChange (V := V) r).symm ((y : ℂ ⊗[ℚ] V) ⊗ₜ[ℂ] w)) =
        Pi.single j (0, crossPairing (E.baseChange ℂ) (cmEigenspace ι (ε j).1)
          (cmEigenspace ι (cmConjEmbedding (ε j).1)) y ⊗ₜ[ℂ] w))
    {m : Fin e → ℕ}
    (c : ∀ j, Module.Basis (Fin (m j)) ℂ (cmEigenspace ι (cmConjEmbedding (ε j).1)))
    {n : ℕ} (σ : Fin n ≃ (j : Fin e) × Fin (m j)) :
    ∃ s : ℂ, s ≠ 0 ∧ ∀ y' : Fin e → Fin r → ℂ,
      ExteriorAlgebra.map e'.toLinearMap
          ((a5_cmDet r (fun t => (c (σ t).1 (σ t).2 : ℂ ⊗[ℚ] V)) (fun t => y' (σ t).1) :
            ExteriorAlgebra ℂ (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))))) =
        s • multiDetWDual (K := ℂ) (W := fun j => cmEigenspace ι (ε j).1)
          (U := fun _ => Fin r → ℂ) (U' := fun _ => Fin r → ℂ) y' := by
  let P : ∀ j, cmEigenspace ι (cmConjEmbedding (ε j).1) ≃ₗ[ℂ]
      Module.Dual ℂ (cmEigenspace ι (ε j).1) := fun j =>
    LinearEquiv.ofBijective _ (spec_a2a_duality_bijective ι E hE hRos (ε j).1)
  obtain ⟨s, hs, H⟩ := a6_ιMulti_sigma_blocks
    (N := MultiSpace ℂ (fun j => cmEigenspace ι (ε j).1) (fun _ => Fin r → ℂ)
      (fun _ => Fin r → ℂ)) (fun j => (c j).map (P j))
    (fun j => (Module.finBasis ℂ (cmEigenspace ι (ε j).1)).dualBasis) σ
  refine ⟨s, hs, fun y' => ?_⟩
  let φ : ∀ j, Module.Dual ℂ (cmEigenspace ι (ε j).1) →ₗ[ℂ]
      MultiSpace ℂ (fun j => cmEigenspace ι (ε j).1) (fun _ => Fin r → ℂ)
        (fun _ => Fin r → ℂ) := fun j =>
    (LinearMap.single ℂ (fun j => Space ℂ (cmEigenspace ι (ε j).1) (Fin r → ℂ) (Fin r → ℂ)) j)
      ∘ₗ dualIn (y' j)
  calc _ = ExteriorAlgebra.ιMulti ℂ n
        (fun t => φ (σ t).1 ((c (σ t).1).map (P (σ t).1) (σ t).2)) := by
        simp only [a5_cmDet, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.map_apply_ιMulti]
        congr 1
        funext t
        simp only [Function.comp_apply, LinearEquiv.coe_coe, he₂, Module.Basis.map_apply]
        rfl
    _ = _ := H φ
    _ = _ := by
        congr 1
        simp only [multiDetWDual, detWDual_eq, exteriorPower.ιMulti_apply_coe,
          ExteriorAlgebra.map_apply_ιMulti]
        rfl

omit [FiniteDimensional ℚ V] in
/-- `⋀^k e'⁻¹` undoes `⋀^k e'`. -/
theorem a6_map_symm_map {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M ≃ₗ[K] N) (k : ℕ) (z : ⋀[K]^k M) :
    exteriorPower.map k f.symm.toLinearMap (exteriorPower.map k f.toLinearMap z) = z := by
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
  simp

omit [FiniteDimensional ℚ V] in
/-- `⋀^k e'` undoes `⋀^k e'⁻¹`. -/
theorem a6_map_map_symm {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M ≃ₗ[K] N) (k : ℕ) (z : ⋀[K]^k N) :
    exteriorPower.map k f.toLinearMap (exteriorPower.map k f.symm.toLinearMap z) = z := by
  simpa using a6_map_symm_map f.symm k z

omit [IsCMField L] in
/-- `⋀^k e'⁻¹` intertwines the block action with the action of `X` (clause `he₃`). -/
theorem a6_exteriorDer_map_symm (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V)
    (u : L) {d : ℚ} (r : ℕ) {e : ℕ} (ε : Fin e ≃ cmPlusEmb L u d)
    (e' : (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))) ≃ₗ[ℂ]
        MultiSpace ℂ (fun j => cmEigenspace ι (ε j).1) (fun _ => Fin r → ℂ)
          (fun _ => Fin r → ℂ))
    (he₃ : ∀ X : Module.End ℂ (ℂ ⊗[ℚ] V),
      (∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X) →
      (∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y)) →
      ∀ z (j : Fin e), e' (powerAction r X z) j =
        multiplicityLie ℂ (cmEigenspace ι (ε j).1) (Fin r → ℂ) (Fin r → ℂ)
          (cmBlock ι (ε j).1 X) (e' z j))
    (X : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hX : ∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X)
    (hs : ∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y)) (k : ℕ)
    (y : ⋀[ℂ]^k (MultiSpace ℂ (fun j => cmEigenspace ι (ε j).1) (fun _ => Fin r → ℂ)
          (fun _ => Fin r → ℂ))) :
    exteriorDer k (powerAction r X) (exteriorPower.map k e'.symm.toLinearMap y) =
      exteriorPower.map k e'.symm.toLinearMap (exteriorDer k (LinearMap.piMap fun j =>
        multiplicityLie ℂ (cmEigenspace ι (ε j).1) (Fin r → ℂ) (Fin r → ℂ)
          (cmBlock ι (ε j).1 X)) y) := by
  apply exteriorDer_map
  apply LinearMap.ext
  intro m
  apply e'.injective
  funext j
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [he₃ X hX hs, LinearEquiv.apply_symm_apply]
  rfl

omit [FiniteDimensional ℚ V] [IsCMField L] in
/-- Membership in `cmBlockTraceZero` is `Σ_v tr Y_v = 0`. -/
theorem a6_mem_cmBlockTraceZero_iff (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) (d : ℚ)
    (Y : ∀ v : cmPlusEmb L u d, Module.End ℂ (cmEigenspace ι v.1)) :
    Y ∈ cmBlockTraceZero ι u d ↔ ∑ v, LinearMap.trace ℂ _ (Y v) = 0 := by
  simp [cmBlockTraceZero]

/-- A2b's S9 reindexed along `ε`: every trace-sum-zero tuple on the `Fin e` blocks is the tuple
of blocks of an element of the complexified `gkLie`. -/
theorem a6_exists_of_traceZero (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V)
    (hE : E.Nondegenerate) (hAlt : E.IsAlt)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d)) {e : ℕ}
    (ε : Fin e ≃ cmPlusEmb L u d)
    (f : (v : Fin e) → Module.End ℂ (cmEigenspace ι (ε v).1))
    (hf : ∑ v, LinearMap.trace ℂ (cmEigenspace ι (ε v).1) (f v) = 0) :
    ∃ X ∈ complexSpan (gkLie E ι.range (ι u)).toSubmodule,
      (fun j => cmBlock ι (ε j).1 X) = f := by
  obtain ⟨Y, hYd⟩ : ∃ Y : ∀ v : cmPlusEmb L u d, Module.End ℂ (cmEigenspace ι v.1),
      ∀ j, Y (ε j) = f j :=
    ⟨Equiv.piCongrLeft (fun v : cmPlusEmb L u d => Module.End ℂ (cmEigenspace ι v.1)) ε f,
      fun j => Equiv.piCongrLeft_apply_apply _ _ _ _⟩
  have hY : Y ∈ cmBlockTraceZero ι u d := by
    rw [a6_mem_cmBlockTraceZero_iff]
    rw [← Fintype.sum_equiv ε (fun j => LinearMap.trace ℂ _ (Y (ε j))) _ (fun _ => rfl)]
    simp only [hYd]
    exact hf
  obtain ⟨X, hX, hXY⟩ := spec_a2b_exists_of_mem_traceZero ι E hE hAlt hRos u hd hu Y hY
  exact ⟨X, hX, funext fun j => (hXY (ε j)).trans (hYd j)⟩

theorem spec_a6_invariants_eq_map_constWeightDegree_aux [Nontrivial V]
    (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hAlt : E.IsAlt)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d)) (r : ℕ) {e : ℕ}
    (ε : Fin e ≃ cmPlusEmb L u d)
    (e' : (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))) ≃ₗ[ℂ]
        MultiSpace ℂ (fun j => cmEigenspace ι (ε j).1) (fun _ => Fin r → ℂ)
          (fun _ => Fin r → ℂ))
    (he₃ : ∀ X : Module.End ℂ (ℂ ⊗[ℚ] V),
      (∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X) →
      (∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y)) →
      ∀ z (j : Fin e), e' (powerAction r X z) j =
        multiplicityLie ℂ (cmEigenspace ι (ε j).1) (Fin r → ℂ) (Fin r → ℂ)
          (cmBlock ι (ε j).1 X) (e' z j))
    (k : ℕ) :
    (⨅ (X : Module.End ℂ (ℂ ⊗[ℚ] V))
        (_ : X ∈ complexSpan (gkLie E ι.range (ι u)).toSubmodule),
        LinearMap.ker (exteriorDer k (powerAction r X))) =
      (constWeightDegree (K := ℂ) (W := fun j => cmEigenspace ι (ε j).1)
        (U := fun _ => Fin r → ℂ) (U' := fun _ => Fin r → ℂ) k).map
        (exteriorPower.map k e'.symm.toLinearMap) := by
  have : ∀ j : Fin e, Nontrivial (cmEigenspace ι (ε j).1) := fun j => by
    apply Module.nontrivial_of_finrank_pos (R := ℂ)
    have h := spec_a2a_finrank ι (ε j).1
    have hV : 0 < Module.finrank ℚ V := Module.finrank_pos
    rcases Nat.eq_zero_or_pos (Module.finrank ℂ (cmEigenspace ι (ε j).1)) with h0 | h0
    · rw [h0, zero_mul] at h; omega
    · exact h0
  rw [← spec_a4_traceZero_invariants k]
  have hiff := fun X => spec_a2b_mem_complexSpan_gkLie_iff ι E u X
  ext z
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hz
    rw [Submodule.mem_map]
    refine ⟨exteriorPower.map k e'.toLinearMap z, ?_, a6_map_symm_map e' k z⟩
    rw [Submodule.mem_iInf]
    rintro ⟨f, hf⟩
    rw [LinearMap.mem_ker]
    have hf2 : ∑ v, LinearMap.trace ℂ (cmEigenspace ι (ε v).1) (f v) = 0 := by
      convert hf using 3
    have hex := a6_exists_of_traceZero ι E hE hAlt hRos u hd hu ε f hf2
    rcases hex with ⟨X, hX, hXf⟩
    have h := hz X hX
    rw [← a6_map_symm_map e' k z] at h
    rw [a6_exteriorDer_map_symm ι E u r ε e' he₃ X
      ((hiff X).mp hX).1 ((hiff X).mp hX).2.1] at h
    have h3 := exteriorPower.map_injective_field (K := ℂ) e'.symm.injective
      (h.trans (map_zero _).symm)
    subst hXf
    exact h3
  · rintro ⟨y, hy, rfl⟩ X hX
    rw [a6_exteriorDer_map_symm ι E u r ε e' he₃ X ((hiff X).mp hX).1 ((hiff X).mp hX).2.1]
    have htr : ∑ j, LinearMap.trace ℂ _ (cmBlock ι (ε j).1 X) = 0 := by
      have h := (a6_mem_cmBlockTraceZero_iff ι u d _).mp
        (spec_a2b_cmBlock_mem_traceZero ι E hE hRos u hd hu X hX)
      rw [Fintype.sum_equiv ε (fun j => LinearMap.trace ℂ _ (cmBlock ι (ε j).1 X))
        (fun v => LinearMap.trace ℂ _ (cmBlock ι v.1 X)) (fun _ => rfl)]
      exact h
    have h := (Submodule.mem_iInf _).mp hy ⟨fun j => cmBlock ι (ε j).1 X, htr⟩
    rw [LinearMap.mem_ker] at h
    rw [h, map_zero]

/-- `ExteriorAlgebra.map` of an isomorphism carries `⋀^k` onto `⋀^k`. -/
theorem a6_map_exteriorPower {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M ≃ₗ[K] N) (k : ℕ) :
    (⋀[K]^k M).map (ExteriorAlgebra.map f.toLinearMap).toLinearMap = ⋀[K]^k N := by
  rw [Submodule.map_pow, LinearMap.range_eq_map, ← Submodule.map_comp]
  rw [ExteriorAlgebra.map_comp_ι, Submodule.map_comp, Submodule.map_top, LinearEquiv.range, ← LinearMap.range_eq_map]

/-- `ExteriorAlgebra.map` of an isomorphism is injective. -/
theorem a6_map_injective {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M ≃ₗ[K] N) :
    Function.Injective (ExteriorAlgebra.map f.toLinearMap) :=
  ExteriorAlgebra.map_injective ⟨f.symm.toLinearMap, by ext; simp⟩

theorem spec_a6_invariants_eq_span_normal_aux [Nontrivial V]
    (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hAlt : E.IsAlt)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d)) (r : ℕ) {e : ℕ}
    (ε : Fin e ≃ cmPlusEmb L u d)
    (e' : (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))) ≃ₗ[ℂ]
        MultiSpace ℂ (fun j => cmEigenspace ι (ε j).1) (fun _ => Fin r → ℂ)
          (fun _ => Fin r → ℂ))
    (he₃ : ∀ X : Module.End ℂ (ℂ ⊗[ℚ] V),
      (∀ a : L, X * (ι a).baseChange ℂ = (ι a).baseChange ℂ * X) →
      (∀ x y, E.baseChange ℂ (X x) y = -E.baseChange ℂ x (X y)) →
      ∀ z (j : Fin e), e' (powerAction r X z) j =
        multiplicityLie ℂ (cmEigenspace ι (ε j).1) (Fin r → ℂ) (Fin r → ℂ)
          (cmBlock ι (ε j).1 X) (e' z j))
    (k : ℕ) :
    Submodule.map (⋀[ℂ]^k (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ)))).subtype
        (⨅ (X : Module.End ℂ (ℂ ⊗[ℚ] V))
          (_ : X ∈ complexSpan (gkLie E ι.range (ι u)).toSubmodule),
          LinearMap.ker (exteriorDer k (powerAction r X))) =
      ⋀[ℂ]^k (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))) ⊓
        (Submodule.span ℂ (centreNormalProducts (K := ℂ)
          (W := fun j => cmEigenspace ι (ε j).1) (U := fun _ => Fin r → ℂ)
          (U' := fun _ => Fin r → ℂ))).map
          (ExteriorAlgebra.map e'.symm.toLinearMap).toLinearMap := by
  rw [spec_a6_invariants_eq_map_constWeightDegree_aux ι E hE hAlt hRos u hd hu r ε e' he₃ k,
    ← Submodule.map_comp, exteriorPower.subtype_comp_map_eq, Submodule.map_comp,
    spec_a4_constWeightDegree_eq_normal k,
    Submodule.map_inf _ (a6_map_injective e'.symm), a6_map_exteriorPower e'.symm k]


omit [FiniteDimensional ℚ V] in
/-- `cmPowerSpan` is itself a closed family. -/
theorem a6_isCMPowerClosed_cmPowerSpan (R : Subalgebra ℚ (Module.End ℚ V)) {m n : ℕ}
    (D : Submodule ℚ (⋀[ℚ]^2 (V ⊗[ℚ] (Fin m → ℚ)))) (W : Submodule ℚ (⋀[ℚ]^n V)) :
    IsCMPowerClosed R D W (cmPowerSpan R D W) where
  unit_mem := Submodule.mem_iInf _ |>.mpr fun _ => Submodule.mem_iInf _ |>.mpr fun hF =>
    hF.unit_mem
  divisor_le := le_iInf₂ fun _ hF => hF.divisor_le
  pullback_mem a w hw := Submodule.mem_iInf _ |>.mpr fun _ => Submodule.mem_iInf _ |>.mpr
    fun hF => hF.pullback_mem a w hw
  wedge_mem i j v w hv hw := Submodule.mem_iInf _ |>.mpr fun F => Submodule.mem_iInf _ |>.mpr
    fun hF => hF.wedge_mem i j v w ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hv F) hF)
      ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hw F) hF)

/-- `exteriorPower.wedge` is the product of the exterior algebra. -/
theorem a6_coe_wedge {K N : Type*} [Field K] [AddCommGroup N] [Module K N] {i j : ℕ}
    (x : ⋀[K]^i N) (y : ⋀[K]^j N) :
    (exteriorPower.wedge K N i j x y : ExteriorAlgebra K N) = x * y := by
  simp [DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul]

/-- The sum, inside the exterior algebra, of a graded family closed under wedge is closed under
the product. -/
theorem a6_iSup_mul_mem {K N : Type*} [Field K] [AddCommGroup N] [Module K N]
    (F : ∀ i, Submodule K (⋀[K]^i N))
    (hF : ∀ i j v w, v ∈ F i → w ∈ F j → exteriorPower.wedge K N i j v w ∈ F (i + j))
    {a b : ExteriorAlgebra K N} (ha : a ∈ ⨆ i, (F i).map (⋀[K]^i N).subtype)
    (hb : b ∈ ⨆ i, (F i).map (⋀[K]^i N).subtype) :
    a * b ∈ ⨆ i, (F i).map (⋀[K]^i N).subtype := by
  induction ha using Submodule.iSup_induction' with
  | mem i a ha =>
    induction hb using Submodule.iSup_induction' with
    | mem j b hb =>
      obtain ⟨v, hv, rfl⟩ := ha
      obtain ⟨w, hw, rfl⟩ := hb
      refine Submodule.mem_iSup_of_mem (i + j) ⟨_, hF i j v w hv hw, ?_⟩
      exact a6_coe_wedge v w
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add b b' _ _ hb hb' => rw [mul_add]; exact Submodule.add_mem _ hb hb'
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add a a' _ _ ha ha' => rw [add_mul]; exact Submodule.add_mem _ ha ha'

/-- The degree-`k` part of the sum of a graded family is its `k`-th member. -/
theorem a6_mem_of_coe_mem_iSup {K N : Type*} [Field K] [AddCommGroup N] [Module K N]
    (F : ∀ i, Submodule K (⋀[K]^i N)) {k : ℕ} (x : ⋀[K]^k N)
    (hx : (x : ExteriorAlgebra K N) ∈ ⨆ i, (F i).map (⋀[K]^i N).subtype) : x ∈ F k := by
  classical
  let π := GradedAlgebra.proj (fun i : ℕ => ⋀[K]^i N) k
  have h : ∀ y ∈ ⨆ i, (F i).map (⋀[K]^i N).subtype, π y ∈ (F k).map (⋀[K]^k N).subtype := by
    intro y hy
    induction hy using Submodule.iSup_induction' with
    | mem i y hy =>
      obtain ⟨v, hv, rfl⟩ := hy
      by_cases hik : i = k
      · subst hik
        refine ⟨v, hv, ?_⟩
        simp only [π, GradedAlgebra.proj_apply, Submodule.subtype_apply]
        exact (DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[K]^i N) v.2).symm
      · simp only [π, GradedAlgebra.proj_apply, Submodule.subtype_apply]
        rw [DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[K]^i N) v.2 hik]
        exact Submodule.zero_mem _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y y' _ _ hy hy' => rw [map_add]; exact Submodule.add_mem _ hy hy'
  obtain ⟨x', hx', hxx⟩ := h _ hx
  have : x' = x := by
    apply Subtype.ext
    rw [← Submodule.subtype_apply, hxx]
    simp only [π, GradedAlgebra.proj_apply]
    exact DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[K]^i N) x.2
  exact this ▸ hx'

/-- A list product of elements of a multiplicatively closed subspace containing `1`. -/
theorem a6_list_prod_mem {K A : Type*} [Field K] [Ring A] [Algebra K A] (T : Submodule K A)
    (h1 : (1 : A) ∈ T) (hmul : ∀ a b, a ∈ T → b ∈ T → a * b ∈ T) (l : List A)
    (hl : ∀ a ∈ l, a ∈ T) : l.prod ∈ T := by
  induction l with
  | nil => simpa using h1
  | cons a l ih =>
    rw [List.prod_cons]
    exact hmul _ _ (hl a List.mem_cons_self) (ih fun b hb => hl b (List.mem_cons_of_mem a hb))

/-- The image of a list product under an algebra map, all of whose factors land in a
multiplicatively closed subspace containing `1`. -/
theorem a6_map_list_prod_mem {K A B : Type*} [Field K] [Ring A] [Algebra K A] [Ring B]
    [Algebra K B] (g : A →ₐ[K] B) (T : Submodule K B) (h1 : (1 : B) ∈ T)
    (hmul : ∀ a b, a ∈ T → b ∈ T → a * b ∈ T) (l : List A) (hl : ∀ a ∈ l, g a ∈ T) :
    g l.prod ∈ T := by
  rw [map_list_prod]
  exact a6_list_prod_mem T h1 hmul _ fun b hb => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact hl a ha


/-- An endomorphism commuting with the grading operator of a weight-one structure with
`H^{1,0} + H^{0,1} = ⊤` preserves every Hodge piece. -/
theorem a6_mem_H_of_commute {M : HodgeBlocks.QHodgeStructure 1 V}
    (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (Y : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hY : gradingOperator M.H M.isInternal * Y = Y * gradingOperator M.H M.isInternal)
    (pq : ℤ × ℤ) (x : ℂ ⊗[ℚ] V) (hx : x ∈ M.H pq) : Y x ∈ M.H pq := by
  have key : ∀ p q p' q' : ℤ, M.H (p, q) ⊔ M.H (p', q') = ⊤ →
      Complex.I * ((p : ℂ) - q) ≠ Complex.I * ((p' : ℂ) - q') →
      ∀ x ∈ M.H (p, q), Y x ∈ M.H (p, q) := by
    intro p q p' q' hab hne x hx
    have hw : Y x ∈ M.H (p, q) ⊔ M.H (p', q') := hab ▸ Submodule.mem_top
    obtain ⟨w1, hw1, w2, hw2, hsum⟩ := Submodule.mem_sup.mp hw
    have hC := LinearMap.congr_fun hY x
    simp only [Module.End.mul_apply] at hC
    rw [gradingOperator_apply_of_mem M.H M.isInternal hx, map_smul, ← hsum, map_add,
      gradingOperator_apply_of_mem M.H M.isInternal hw1,
      gradingOperator_apply_of_mem M.H M.isInternal hw2, smul_add] at hC
    have h2 := add_left_cancel hC
    have hw20 : w2 = 0 := by
      have h' : (Complex.I * ((p' : ℂ) - q') - Complex.I * ((p : ℂ) - q)) • w2 = 0 := by
        rw [sub_smul, h2, sub_self]
      exact (smul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr (Ne.symm hne))
    rw [← hsum, hw20, add_zero]
    exact hw1
  have hne : Complex.I * (((1 : ℤ) : ℂ) - ((0 : ℤ) : ℂ)) ≠
      Complex.I * (((0 : ℤ) : ℂ) - ((1 : ℤ) : ℂ)) := by
    push_cast
    intro h
    apply Complex.I_ne_zero
    linear_combination h / 2
  by_cases h10 : pq = (1, 0)
  · subst h10
    exact key 1 0 0 1 hTop hne x hx
  by_cases h01 : pq = (0, 1)
  · subst h01
    exact key 0 1 1 0 (sup_comm (M.H (1, 0)) _ ▸ hTop) (Ne.symm hne) x hx
  have hle : M.H (1, 0) ⊔ M.H (0, 1) ≤ ⨆ (j) (_ : j ≠ pq), M.H j :=
    sup_le (le_iSup₂_of_le (1, 0) (Ne.symm h10) le_rfl)
      (le_iSup₂_of_le (0, 1) (Ne.symm h01) le_rfl)
  have hx0 : x = 0 := (Submodule.disjoint_def.mp (M.isInternal.submodule_iSupIndep pq)) x hx
    (hle (hTop ▸ Submodule.mem_top))
  rw [hx0, map_zero]
  exact Submodule.zero_mem _

omit [IsCMField L] in
/-- S7's `⊇` half: the complexified span consists of complexified Hodge classes (PW-0's S6). -/
theorem a6_exteriorSpanC_le_exteriorHodgeClasses (ι : L →ₐ[ℚ] Module.End ℚ V)
    {M : HodgeBlocks.QHodgeStructure 1 V} {d : ℚ} (A : HodgeBlocks.WeilAction M d) (u : L)
    (hJ : A.J = ι u) (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (E : LinearMap.BilinForm ℚ V)
    (hGk : HodgeLieIsGk M.H M.isInternal E ι.range A.J) (hW : A.IsWeilType) (r k : ℕ) :
    exteriorSpanC (cmPowerSpan ι.range (rationalExteriorHodge M.H M.isInternal r 2)
        (A.weilClasses hTop hW) k) ≤ exteriorHodgeClasses M.H M.isInternal r k := by
  have hR : ∀ x ∈ ι.range, ∀ pq, ∀ v ∈ M.H pq,
      (x : Module.End ℚ V).baseChange ℂ v ∈ M.H pq := by
    intro x hx pq v hv
    obtain ⟨a, rfl⟩ := hx
    apply a6_mem_H_of_commute hTop _ ?_ pq v hv
    have hC : gradingOperator M.H M.isInternal ∈
        complexSpan (gkLie E ι.range (ι u)).toSubmodule := by
      rw [← hJ, ← hGk]
      exact gradingOperator_mem_span_hodgeLieAlgebra M.H M.isInternal
    exact (((spec_a2b_mem_complexSpan_gkLie_iff ι E u _).mp hC).1 a)
  exact exteriorSpanC_mono (Adapters.spec_pw0_cmPowerSpan_le_rationalExteriorHodge M.H
    M.isInternal ι.range hR (A.weilClasses hTop hW) (Adapters.spec_pw0_weilClasses_grading A hTop hW)
    r k)

/-- `ExteriorAlgebra.map e'⁻¹` undoes `ExteriorAlgebra.map e'`. -/
theorem a6_map_symm_map_EA {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M ≃ₗ[K] N) (z : ExteriorAlgebra K M) :
    ExteriorAlgebra.map f.symm.toLinearMap (ExteriorAlgebra.map f.toLinearMap z) = z := by
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  simp

omit [IsCMField L] in
/-- The block dimension `m = dim V / [L : ℚ]`, the same for every embedding (A2a's S3). -/
theorem a6_finrank_cmEigenspace (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ) :
    Module.finrank ℂ (cmEigenspace ι τ) = Module.finrank ℚ V / Module.finrank ℚ L :=
  (Nat.div_eq_of_eq_mul_left Module.finrank_pos (spec_a2a_finrank ι τ).symm).symm

omit [FiniteDimensional ℚ V] [IsCMField L] in
/-- `dim V₊ = e · m`: the concatenated bases of the `W_v` form a basis of `V₊`. -/
theorem a6_finrank_cmPlusPart (ι : L →ₐ[ℚ] Module.End ℚ V) (u : L) (d : ℚ) {m : ℕ}
    (b : ∀ v : cmPlusEmb L u d, Module.Basis (Fin m) ℂ (cmEigenspace ι v.1)) :
    Module.finrank ℂ (cmPlusPart ι u d) = Fintype.card (cmPlusEmb L u d) * m := by
  have hli := a5_linearIndependent_concat ι Subtype.val Subtype.val_injective b
  have hspan : Submodule.span ℂ (Set.range fun p : cmPlusEmb L u d × Fin m =>
      (b p.1 p.2 : ℂ ⊗[ℚ] V)) = cmPlusPart ι u d := by
    refine le_antisymm (Submodule.span_le.mpr ?_) (iSup₂_le fun τ hτ => ?_)
    · rintro _ ⟨p, rfl⟩
      exact (le_iSup₂_of_le p.1.1 p.1.2 le_rfl : cmEigenspace ι p.1.1 ≤
        cmPlusPart ι u d) (b p.1 p.2).2
    · intro x hx
      have hx' : x = ∑ i, (b ⟨τ, hτ⟩).repr ⟨x, hx⟩ i • (b ⟨τ, hτ⟩ i : ℂ ⊗[ℚ] V) := by
        have := congrArg Subtype.val ((b ⟨τ, hτ⟩).sum_repr ⟨x, hx⟩).symm
        simpa only [Submodule.coe_sum, Submodule.coe_smul] using this
      rw [hx']
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨(⟨τ, hτ⟩, i), rfl⟩)
  rw [← hspan, finrank_span_eq_card hli, Fintype.card_prod, Fintype.card_fin]

/-- S7, the contractions: `e'⁻¹` of `Θ_j(x, x')` is a complexified degree-2 Hodge class, so it
lies in the complexified span. -/
theorem a6_theta_mem (ι : L →ₐ[ℚ] Module.End ℚ V)
    {M : HodgeBlocks.QHodgeStructure 1 V} {d : ℚ} (A : HodgeBlocks.WeilAction M d) (u : L)
    (hJ : A.J = ι u) (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (E : LinearMap.BilinForm ℚ V)
    (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (hGk : HodgeLieIsGk M.H M.isInternal E ι.range A.J) (hW : A.IsWeilType) (r : ℕ) {e : ℕ}
    (ε : Fin e ≃ cmPlusEmb L u d)
    (e' : (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))) ≃ₗ[ℂ]
        MultiSpace ℂ (fun j => cmEigenspace ι (ε j).1) (fun _ => Fin r → ℂ)
          (fun _ => Fin r → ℂ))
    (he₁ : ∀ (j : Fin e) (x : cmEigenspace ι (ε j).1) (w : Fin r → ℂ),
      e' ((powerBaseChange (V := V) r).symm ((x : ℂ ⊗[ℚ] V) ⊗ₜ[ℂ] w)) =
        Pi.single j (x ⊗ₜ[ℂ] w, 0))
    (he₂ : ∀ (j : Fin e) (y : cmEigenspace ι (cmConjEmbedding (ε j).1)) (w : Fin r → ℂ),
      e' ((powerBaseChange (V := V) r).symm ((y : ℂ ⊗[ℚ] V) ⊗ₜ[ℂ] w)) =
        Pi.single j (0, crossPairing (E.baseChange ℂ) (cmEigenspace ι (ε j).1)
          (cmEigenspace ι (cmConjEmbedding (ε j).1)) y ⊗ₜ[ℂ] w))
    (j : Fin e) (x x' : Fin r → ℂ) :
    ExteriorAlgebra.map e'.symm.toLinearMap
        (blockTheta (K := ℂ) (W := fun j => cmEigenspace ι (ε j).1) (U := fun _ => Fin r → ℂ)
          (U' := fun _ => Fin r → ℂ) j x x') ∈
      ⨆ i, (exteriorSpanC (cmPowerSpan ι.range (rationalExteriorHodge M.H M.isInternal r 2)
        (A.weilClasses hTop hW) i)).map (⋀[ℂ]^i (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ)))).subtype := by
  let cp := LinearEquiv.ofBijective (crossPairing (E.baseChange ℂ) (cmEigenspace ι (ε j).1)
    (cmEigenspace ι (cmConjEmbedding (ε j).1))) (spec_a2a_duality_bijective ι E hE hRos (ε j).1)
  let b := Module.finBasis ℂ (cmEigenspace ι (ε j).1)
  let c := b.dualBasis.map cp.symm
  have hbc : ∀ i i', E.baseChange ℂ (b i) (c i') = if i = i' then 1 else 0 := by
    intro i i'
    have h : crossPairing (E.baseChange ℂ) (cmEigenspace ι (ε j).1)
        (cmEigenspace ι (cmConjEmbedding (ε j).1)) (c i') (b i) = E.baseChange ℂ (b i) (c i') :=
      rfl
    rw [← h]
    have h' : crossPairing (E.baseChange ℂ) (cmEigenspace ι (ε j).1)
        (cmEigenspace ι (cmConjEmbedding (ε j).1)) (c i') = b.dualBasis i' := by
      change cp (cp.symm (b.dualBasis i')) = _
      exact cp.apply_symm_apply _
    rw [h', Module.Basis.dualBasis_apply_self]
  have h2 := spec_a6_map_cmTheta_aux ι E u r ε e' he₁ he₂ j b (fun i => c i) hbc x x'
  rw [← h2, a6_map_symm_map_EA]
  have hmem := spec_a5_cmTheta_mem_exteriorHodgeClasses M.H M.isInternal ι E u (hJ ▸ hGk)
    (ε j).1 b c hbc r x x'
  exact Submodule.mem_iSup_of_mem 2 ⟨_, exteriorSpanC_mono
    (a6_isCMPowerClosed_cmPowerSpan _ _ _).divisor_le hmem, rfl⟩

/-- S7, the determinant classes: `e'⁻¹` of `multiDetW y` is a nonzero multiple of an `a5_cmDet`
on the concatenated bases, which lies in the span of the pullbacks of the complexified Weil
plane. -/
theorem a6_det_mem (ι : L →ₐ[ℚ] Module.End ℚ V)
    {M : HodgeBlocks.QHodgeStructure 1 V} {d : ℚ} (A : HodgeBlocks.WeilAction M d) (u : L)
    (hJ : A.J = ι u) (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType) (hd : 0 < d)
    (r : ℕ) {e : ℕ} (ε : Fin e ≃ cmPlusEmb L u d)
    (e' : (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))) ≃ₗ[ℂ]
        MultiSpace ℂ (fun j => cmEigenspace ι (ε j).1) (fun _ => Fin r → ℂ)
          (fun _ => Fin r → ℂ))
    (he₁ : ∀ (j : Fin e) (x : cmEigenspace ι (ε j).1) (w : Fin r → ℂ),
      e' ((powerBaseChange (V := V) r).symm ((x : ℂ ⊗[ℚ] V) ⊗ₜ[ℂ] w)) =
        Pi.single j (x ⊗ₜ[ℂ] w, 0))
    {m : ℕ} (bb : ∀ v : cmPlusEmb L u d, Module.Basis (Fin m) ℂ (cmEigenspace ι v.1))
    (bb' : ∀ v : cmPlusEmb L u d,
      Module.Basis (Fin m) ℂ (cmEigenspace ι (cmConjEmbedding v.1)))
    (σ' : Fin (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) + Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) ≃
      (_ : Fin e) × Fin m)
    (y : Fin e → Fin r → ℂ) :
    ExteriorAlgebra.map e'.symm.toLinearMap
        (multiDetW (K := ℂ) (W := fun j => cmEigenspace ι (ε j).1) (U := fun _ => Fin r → ℂ)
          (U' := fun _ => Fin r → ℂ) y) ∈
      ⨆ i, (exteriorSpanC (cmPowerSpan ι.range (rationalExteriorHodge M.H M.isInternal r 2)
        (A.weilClasses hTop hW) i)).map (⋀[ℂ]^i (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ)))).subtype := by
  set n := Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) + Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))
  let σ : Fin n ≃ cmPlusEmb L u d × Fin m :=
    σ'.trans ((Equiv.sigmaEquivProd (Fin e) (Fin m)).trans (Equiv.prodCongr ε (Equiv.refl _)))
  let xs : Fin n → ℂ ⊗[ℚ] V := fun t => (bb (ε (σ' t).1) (σ' t).2 : ℂ ⊗[ℚ] V)
  have hxs : ∀ t, xs t ∈ cmEigenspace ι (ε (σ' t).1).1 := fun t => (bb _ _).2
  have hS7 := spec_a5_weilClasses_baseChange_eq ι A u hJ hTop hW hd bb bb' σ
  have hι : exteriorPower.ιMulti ℂ n xs ∈ exteriorSpanC (A.weilClasses hTop hW) := by
    change _ ∈ ((A.weilClasses hTop hW).baseChange ℂ).map
      (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := V) n).toLinearMap
    rw [hS7]
    exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
  have hP := a6_isCMPowerClosed_cmPowerSpan ι.range
    (rationalExteriorHodge M.H M.isInternal r 2) (A.weilClasses hTop hW)
  have hpb : ∀ a : Fin r → L, a5_cmDet r xs (fun t i => (ε (σ' t).1).1 (a i)) ∈
      exteriorSpanC (cmPowerSpan ι.range (rationalExteriorHodge M.H M.isInternal r 2)
        (A.weilClasses hTop hW) n) := by
    intro a
    rw [← spec_a5_map_cmPowerPullback_ιMulti ι (fun t => (ε (σ' t).1).1) xs hxs a]
    exact exteriorSpanC_map _ _ _ (fun w hw => hP.pullback_mem _ w hw) hι
  have hspan := spec_a5_cmDet_mem_span r (fun t => (ε (σ' t).1).1) xs
    (Function.extend (fun j => (ε j).1) y 0)
  have heq : (fun t => Function.extend (fun j => (ε j).1) y 0 ((ε (σ' t).1).1)) =
      fun t => y (σ' t).1 :=
    funext fun t => (Subtype.val_injective.comp ε.injective).extend_apply y 0 _
  simp only [heq] at hspan
  have hdet : a5_cmDet r xs (fun t => y (σ' t).1) ∈
      exteriorSpanC (cmPowerSpan ι.range (rationalExteriorHodge M.H M.isInternal r 2)
        (A.weilClasses hTop hW) n) :=
    Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact hpb a) hspan
  obtain ⟨s, hs, hsy⟩ := spec_a6_map_cmDet_aux ι u r ε e' he₁ (fun j => bb (ε j)) σ'
  have h := congrArg (ExteriorAlgebra.map e'.symm.toLinearMap) (hsy y)
  rw [a6_map_symm_map_EA, map_smul] at h
  have hmd : ExteriorAlgebra.map e'.symm.toLinearMap
      (multiDetW (K := ℂ) (W := fun j => cmEigenspace ι (ε j).1) (U := fun _ => Fin r → ℂ)
        (U' := fun _ => Fin r → ℂ) y) =
      s⁻¹ • ((a5_cmDet r xs (fun t => y (σ' t).1) :
        ExteriorAlgebra ℂ (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))))) := by
    rw [h, smul_smul, inv_mul_cancel₀ hs, one_smul]
  rw [hmd]
  exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem n ⟨_, hdet, rfl⟩)

/-- S7, the conjugate determinant classes: as `a6_det_mem`, with the bases of the `W_j̄`, the
second line of the complexified Weil plane and A6's S4. -/
theorem a6_detDual_mem (ι : L →ₐ[ℚ] Module.End ℚ V)
    {M : HodgeBlocks.QHodgeStructure 1 V} {d : ℚ} (A : HodgeBlocks.WeilAction M d) (u : L)
    (hJ : A.J = ι u) (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType) (hd : 0 < d)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (r : ℕ) {e : ℕ} (ε : Fin e ≃ cmPlusEmb L u d)
    (e' : (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))) ≃ₗ[ℂ]
        MultiSpace ℂ (fun j => cmEigenspace ι (ε j).1) (fun _ => Fin r → ℂ)
          (fun _ => Fin r → ℂ))
    (he₂ : ∀ (j : Fin e) (y : cmEigenspace ι (cmConjEmbedding (ε j).1)) (w : Fin r → ℂ),
      e' ((powerBaseChange (V := V) r).symm ((y : ℂ ⊗[ℚ] V) ⊗ₜ[ℂ] w)) =
        Pi.single j (0, crossPairing (E.baseChange ℂ) (cmEigenspace ι (ε j).1)
          (cmEigenspace ι (cmConjEmbedding (ε j).1)) y ⊗ₜ[ℂ] w))
    {m : ℕ} (bb : ∀ v : cmPlusEmb L u d, Module.Basis (Fin m) ℂ (cmEigenspace ι v.1))
    (bb' : ∀ v : cmPlusEmb L u d,
      Module.Basis (Fin m) ℂ (cmEigenspace ι (cmConjEmbedding v.1)))
    (σ' : Fin (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) + Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) ≃
      (_ : Fin e) × Fin m)
    (y : Fin e → Fin r → ℂ) :
    ExteriorAlgebra.map e'.symm.toLinearMap
        (multiDetWDual (K := ℂ) (W := fun j => cmEigenspace ι (ε j).1) (U := fun _ => Fin r → ℂ)
          (U' := fun _ => Fin r → ℂ) y) ∈
      ⨆ i, (exteriorSpanC (cmPowerSpan ι.range (rationalExteriorHodge M.H M.isInternal r 2)
        (A.weilClasses hTop hW) i)).map (⋀[ℂ]^i (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ)))).subtype := by
  set n := Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) + Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))
  let σ : Fin n ≃ cmPlusEmb L u d × Fin m :=
    σ'.trans ((Equiv.sigmaEquivProd (Fin e) (Fin m)).trans (Equiv.prodCongr ε (Equiv.refl _)))
  let xs : Fin n → ℂ ⊗[ℚ] V := fun t => (bb' (ε (σ' t).1) (σ' t).2 : ℂ ⊗[ℚ] V)
  have hxs : ∀ t, xs t ∈ cmEigenspace ι (cmConjEmbedding (ε (σ' t).1).1) :=
    fun t => (bb' _ _).2
  have hS7 := spec_a5_weilClasses_baseChange_eq ι A u hJ hTop hW hd bb bb' σ
  have hι : exteriorPower.ιMulti ℂ n xs ∈ exteriorSpanC (A.weilClasses hTop hW) := by
    change _ ∈ ((A.weilClasses hTop hW).baseChange ℂ).map
      (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := V) n).toLinearMap
    rw [hS7]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hP := a6_isCMPowerClosed_cmPowerSpan ι.range
    (rationalExteriorHodge M.H M.isInternal r 2) (A.weilClasses hTop hW)
  have hpb : ∀ a : Fin r → L, a5_cmDet r xs (fun t i => cmConjEmbedding (ε (σ' t).1).1 (a i)) ∈
      exteriorSpanC (cmPowerSpan ι.range (rationalExteriorHodge M.H M.isInternal r 2)
        (A.weilClasses hTop hW) n) := by
    intro a
    rw [← spec_a5_map_cmPowerPullback_ιMulti ι (fun t => cmConjEmbedding (ε (σ' t).1).1) xs hxs a]
    exact exteriorSpanC_map _ _ _ (fun w hw => hP.pullback_mem _ w hw) hι
  have hinj : Function.Injective fun j => cmConjEmbedding (ε j).1 :=
    (Function.LeftInverse.injective (g := cmConjEmbedding (L := L))
      a5_cmConjEmbedding_cmConjEmbedding).comp (Subtype.val_injective.comp ε.injective)
  have hspan := spec_a5_cmDet_mem_span r (fun t => cmConjEmbedding (ε (σ' t).1).1) xs
    (Function.extend (fun j => cmConjEmbedding (ε j).1) y 0)
  have heq : (fun t => Function.extend (fun j => cmConjEmbedding (ε j).1) y 0
      (cmConjEmbedding (ε (σ' t).1).1)) = fun t => y (σ' t).1 :=
    funext fun t => hinj.extend_apply y 0 _
  simp only [heq] at hspan
  have hdet : a5_cmDet r xs (fun t => y (σ' t).1) ∈
      exteriorSpanC (cmPowerSpan ι.range (rationalExteriorHodge M.H M.isInternal r 2)
        (A.weilClasses hTop hW) n) :=
    Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact hpb a) hspan
  obtain ⟨s, hs, hsy⟩ := spec_a6_map_cmDet_conj_aux ι E hE hRos u r ε e' he₂ (fun j => bb' (ε j)) σ'
  have h := congrArg (ExteriorAlgebra.map e'.symm.toLinearMap) (hsy y)
  rw [a6_map_symm_map_EA, map_smul] at h
  have hmd : ExteriorAlgebra.map e'.symm.toLinearMap
      (multiDetWDual (K := ℂ) (W := fun j => cmEigenspace ι (ε j).1) (U := fun _ => Fin r → ℂ)
        (U' := fun _ => Fin r → ℂ) y) =
      s⁻¹ • ((a5_cmDet r xs (fun t => y (σ' t).1) :
        ExteriorAlgebra ℂ (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))))) := by
    rw [h, smul_smul, inv_mul_cancel₀ hs, one_smul]
  rw [hmd]
  exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem n ⟨_, hdet, rfl⟩)

theorem spec_a6_exteriorHodgeClasses_eq_cmPowerSpan_aux (ι : L →ₐ[ℚ] Module.End ℚ V)
    {M : HodgeBlocks.QHodgeStructure 1 V} {d : ℚ} (A : HodgeBlocks.WeilAction M d) (u : L)
    (hJ : A.J = ι u) (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (E : LinearMap.BilinForm ℚ V)
    (hE : E.Nondegenerate) (hAlt : E.IsAlt)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d))
    (hGk : HodgeLieIsGk M.H M.isInternal E ι.range A.J) (r k : ℕ) :
    exteriorHodgeClasses M.H M.isInternal r k =
      ((cmPowerSpan ι.range (rationalExteriorHodge M.H M.isInternal r 2)
        (A.weilClasses hTop
          (Adapters.isWeilType_of_hodgeLieIsGk hd A hTop E ι.range hGk)) k).baseChange ℂ).map
        (exteriorBaseChange k).toLinearMap := by
  set hW := Adapters.isWeilType_of_hodgeLieIsGk hd A hTop E ι.range hGk
  change _ = exteriorSpanC (cmPowerSpan ι.range (rationalExteriorHodge M.H M.isInternal r 2)
    (A.weilClasses hTop hW) k)
  refine le_antisymm ?_ (a6_exteriorSpanC_le_exteriorHodgeClasses ι A u hJ hTop E hGk hW r k)
  rcases subsingleton_or_nontrivial V with hV | hV
  · have hS12 := spec_a6_eq_cmPowerSpan_of_subsingleton_aux M.H M.isInternal ι.range
      (r := r) inferInstance (A.weilClasses hTop hW) k
    intro x hx
    change x ∈ ((rationalExteriorHodge M.H M.isInternal r k).baseChange ℂ).map _ at hx
    rw [hS12] at hx
    exact hx
  classical
  let ε := (Fintype.equivFin (cmPlusEmb L u d)).symm
  obtain ⟨e', he₁, he₂, he₃⟩ := spec_a6_exists_powerModel_fin_aux ι E hE hRos u hd hu r ε
  let bb : ∀ v : cmPlusEmb L u d, Module.Basis (Fin (Module.finrank ℚ V / Module.finrank ℚ L))
      ℂ (cmEigenspace ι v.1) := fun v =>
    (Module.finBasis ℂ (cmEigenspace ι v.1)).reindex (finCongr (a6_finrank_cmEigenspace ι v.1))
  let bb' : ∀ v : cmPlusEmb L u d, Module.Basis (Fin (Module.finrank ℚ V / Module.finrank ℚ L))
      ℂ (cmEigenspace ι (cmConjEmbedding v.1)) := fun v =>
    (Module.finBasis ℂ (cmEigenspace ι (cmConjEmbedding v.1))).reindex
      (finCongr (a6_finrank_cmEigenspace ι (cmConjEmbedding v.1)))
  have hcard : Fintype.card ((_ : Fin (Fintype.card (cmPlusEmb L u d))) ×
      Fin (Module.finrank ℚ V / Module.finrank ℚ L)) =
      Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) + Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) := by
    have h1 : 2 * Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) = Module.finrank ℂ ↥A.Vs := hW
    have h2 : Module.finrank ℂ ↥A.Vs = Fintype.card (cmPlusEmb L u d) *
        (Module.finrank ℚ V / Module.finrank ℚ L) := by
      rw [← spec_a2a_cmPlusPart_eq_Vs ι A u hJ, a6_finrank_cmPlusPart ι u d bb]
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    omega
  let σ' := (Fintype.equivFinOfCardEq hcard).symm
  have hP := a6_isCMPowerClosed_cmPowerSpan ι.range
    (rationalExteriorHodge M.H M.isInternal r 2) (A.weilClasses hTop hW)
  set T := ⨆ i, (exteriorSpanC (cmPowerSpan ι.range (rationalExteriorHodge M.H M.isInternal r 2)
    (A.weilClasses hTop hW) i)).map (⋀[ℂ]^i (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ)))).subtype with hT
  have hTmul : ∀ a b, a ∈ T → b ∈ T → a * b ∈ T := fun a b ha hb =>
    a6_iSup_mul_mem _ (fun i j v w hv hw => exteriorSpanC_wedge _ _ _
      (fun v hv w hw => hP.wedge_mem i j v w hv hw) hv hw) ha hb
  have hT1 : (1 : ExteriorAlgebra ℂ (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ)))) ∈ T := by
    have hu := exteriorComplexify_mem hP.unit_mem
    rw [exteriorComplexify_ιMulti] at hu
    refine Submodule.mem_iSup_of_mem 0 ⟨_, hu, ?_⟩
    simp
  have hNP : ∀ y ∈ centreNormalProducts (K := ℂ) (W := fun j => cmEigenspace ι (ε j).1)
      (U := fun _ => Fin r → ℂ) (U' := fun _ => Fin r → ℂ),
      ExteriorAlgebra.map e'.symm.toLinearMap y ∈ T := by
    rintro y (⟨l, c, x, rfl⟩ | ⟨l, c, x', rfl⟩)
    · rw [map_mul]
      refine hTmul _ _ (a6_map_list_prod_mem _ T hT1 hTmul _ ?_)
        (a6_map_list_prod_mem _ T hT1 hTmul _ ?_)
      · intro a ha
        obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
        exact a6_theta_mem ι A u hJ hTop E hE hRos hGk hW r ε e' he₁ he₂ p.1 p.2.1 p.2.2
      · intro a ha
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
        exact a6_det_mem ι A u hJ hTop hW hd r ε e' he₁ bb bb' σ' (x j)
    · rw [map_mul]
      refine hTmul _ _ (a6_map_list_prod_mem _ T hT1 hTmul _ ?_)
        (a6_map_list_prod_mem _ T hT1 hTmul _ ?_)
      · intro a ha
        obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
        exact a6_theta_mem ι A u hJ hTop E hE hRos hGk hW r ε e' he₁ he₂ p.1 p.2.1 p.2.2
      · intro a ha
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
        exact a6_detDual_mem ι A u hJ hTop hW hd E hE hRos r ε e' he₂ bb bb' σ' (x' j)
  have hspanT : (Submodule.span ℂ (centreNormalProducts (K := ℂ)
      (W := fun j => cmEigenspace ι (ε j).1) (U := fun _ => Fin r → ℂ)
      (U' := fun _ => Fin r → ℂ))).map (ExteriorAlgebra.map e'.symm.toLinearMap).toLinearMap ≤
      T := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact hNP y hy
  intro x hx
  have hker : x ∈ ⨅ (X : Module.End ℂ (ℂ ⊗[ℚ] V))
      (_ : X ∈ complexSpan (gkLie E ι.range (ι u)).toSubmodule),
      LinearMap.ker (exteriorDer k (powerAction r X)) := by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro X hX
    exact (mem_exteriorHodgeClasses_iff M.H M.isInternal r k x).mp hx X (by rw [hGk, hJ]; exact hX)
  have hx6 := Submodule.mem_map_of_mem
    (f := (⋀[ℂ]^k (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ)))).subtype) hker
  rw [spec_a6_invariants_eq_span_normal_aux ι E hE hAlt hRos u hd hu r ε e' he₃ k] at hx6
  exact a6_mem_of_coe_mem_iSup _ x (hspanT hx6.2)

theorem spec_a6_rationalExteriorHodge_eq_cmPowerSpan_aux (ι : L →ₐ[ℚ] Module.End ℚ V)
    {M : HodgeBlocks.QHodgeStructure 1 V} {d : ℚ} (A : HodgeBlocks.WeilAction M d) (u : L)
    (hJ : A.J = ι u) (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (E : LinearMap.BilinForm ℚ V)
    (hE : E.Nondegenerate) (hAlt : E.IsAlt)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d))
    (hGk : HodgeLieIsGk M.H M.isInternal E ι.range A.J) (r k : ℕ) :
    rationalExteriorHodge M.H M.isInternal r k =
      cmPowerSpan ι.range (rationalExteriorHodge M.H M.isInternal r 2)
        (A.weilClasses hTop
          (Adapters.isWeilType_of_hodgeLieIsGk hd A hTop E ι.range hGk)) k := by
  have h := spec_a6_exteriorHodgeClasses_eq_cmPowerSpan_aux ι A u hJ hTop E hE hAlt hRos hd hu
    hGk r k
  apply le_antisymm
  · apply (Submodule.baseChange_le_iff (A := ℂ)).mp
    apply (Submodule.map_le_map_iff_of_injective (exteriorBaseChange k).injective _ _).mp
    change exteriorHodgeClasses M.H M.isInternal r k ≤ _
    rw [h]
  · apply (Submodule.baseChange_le_iff (A := ℂ)).mp
    apply (Submodule.map_le_map_iff_of_injective (exteriorBaseChange k).injective _ _).mp
    change _ ≤ exteriorHodgeClasses M.H M.isInternal r k
    rw [h]

end CM

end HodgeLean.Foundations
