import HodgeLean.Foundations.CMSplittingDefs
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import HodgeLean.Foundations.WeilPower

/-! # Proofs for the CM splitting spec (stage A2a)

The agent's working file. Fill every proof hole. **Do not change the statement of
any `_aux` theorem**: `CMSplitting.lean` (frozen) restates each one and must still typecheck.
Helper lemmas may be added freely, in this file or in new files; prefix them `a2a_`.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations
open NumberField

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

section General

variable {L : Type*} [CommRing L] [Algebra ℚ L]

/-- The complexified actions of two elements of a commutative `L` commute. -/
theorem a2a_baseChange_commute (ι : L →ₐ[ℚ] Module.End ℚ V) (a b : L) :
    Commute ((ι a).baseChange ℂ) ((ι b).baseChange ℂ) := by
  rw [Commute, SemiconjBy, ← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, ← map_mul,
    ← map_mul, mul_comm]

/-- Spec S1. -/
theorem spec_a2a_iSupIndep_aux (ι : L →ₐ[ℚ] Module.End ℚ V) :
    iSupIndep (cmEigenspace ι) := by
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (f := fun a : L => (ι a).baseChange ℂ)
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (a2a_baseChange_commute ι j i) φ)
  refine (hind.comp (f := fun τ : L →ₐ[ℚ] ℂ => (τ : L → ℂ)) DFunLike.coe_injective).mono ?_
  intro τ
  exact iInf_mono fun a => Module.End.eigenspace_le_maxGenEigenspace

/-- Spec S4. -/
theorem spec_a2a_complexConj_mem_iff_aux (ι : L →ₐ[ℚ] Module.End ℚ V) (τ : L →ₐ[ℚ] ℂ)
    (x : ℂ ⊗[ℚ] V) :
    complexConj V x ∈ cmEigenspace ι (cmConjEmbedding τ) ↔ x ∈ cmEigenspace ι τ := by
  have key : ∀ (σ : L →ₐ[ℚ] ℂ) (y : ℂ ⊗[ℚ] V), y ∈ cmEigenspace ι σ →
      complexConj V y ∈ cmEigenspace ι (cmConjEmbedding σ) := by
    intro σ y hy
    simp only [cmEigenspace, Submodule.mem_iInf] at hy ⊢
    exact fun a => complexConj_mem_eigenspace (hy a)
  refine ⟨fun hx => ?_, key τ x⟩
  have hττ : cmConjEmbedding (cmConjEmbedding τ) = τ := by
    ext a
    simp [cmConjEmbedding]
  simpa [hττ] using key _ _ hx

/-- Spec S8. -/
theorem spec_a2a_orthogonal_of_rosati_aux (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (c : L →ₐ[ℚ] L)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (c a) y))
    (τ τ' : L →ₐ[ℚ] ℂ) (h : τ ≠ τ'.comp c)
    (x : ℂ ⊗[ℚ] V) (hx : x ∈ cmEigenspace ι τ) (y : ℂ ⊗[ℚ] V) (hy : y ∈ cmEigenspace ι τ') :
    E.baseChange ℂ x y = 0 := by
  have hext : ∀ (a : L) (x y : ℂ ⊗[ℚ] V),
      E.baseChange ℂ ((ι a).baseChange ℂ x) y = E.baseChange ℂ x ((ι (c a)).baseChange ℂ y) := by
    intro a x y
    induction x using TensorProduct.inductionOn with
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | tmul z v =>
      induction y using TensorProduct.inductionOn with
      | add y y' hy hy' => simp only [map_add, hy, hy']
      | tmul w v' =>
        simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hRos]
  obtain ⟨a, ha⟩ : ∃ a, τ a ≠ τ' (c a) := by
    by_contra hcon
    push Not at hcon
    exact h (AlgHom.ext hcon)
  simp only [cmEigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hx hy
  have h1 := hext a x y
  rw [hx a, hy (c a), map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at h1
  have h2 : (τ a - τ' (c a)) * E.baseChange ℂ x y = 0 := by rw [sub_mul, h1, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr ha)

/-- Spec S11. -/
theorem spec_a2a_finrank_fails_nonfaithful_aux :
    ¬ ∀ τ : ℚ × ℚ →ₐ[ℚ] ℂ,
      Module.finrank ℂ (cmEigenspace a2a_fstAction τ) * Module.finrank ℚ (ℚ × ℚ) =
        Module.finrank ℚ ℚ := by
  intro hall
  have h := hall ((Algebra.ofId ℚ ℂ).comp (AlgHom.snd ℚ ℚ ℚ))
  have hbot : cmEigenspace a2a_fstAction ((Algebra.ofId ℚ ℂ).comp (AlgHom.snd ℚ ℚ ℚ)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    simp only [cmEigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hx
    have h1 := hx (1, 0)
    have hone : a2a_fstAction ((1, 0) : ℚ × ℚ) = 1 := by
      ext
      simp [a2a_fstAction, Algebra.algebraMap_eq_smul_one]
    rw [hone, LinearMap.baseChange_one] at h1
    simpa using h1
  rw [hbot, finrank_bot] at h
  simp at h

end General

section NumberField

variable {L : Type*} [Field L] [NumberField L]

/-- If `θ` generates `L`, the `τ(θ)`-eigenspace of `ι(θ)_ℂ` lies in `W_τ`. -/
theorem a2a_eigenspace_gen_le (ι : L →ₐ[ℚ] Module.End ℚ V) {θ : L}
    (hθ : Algebra.adjoin ℚ {θ} = ⊤) (τ : L →ₐ[ℚ] ℂ) :
    Module.End.eigenspace ((ι θ).baseChange ℂ) (τ θ) ≤ cmEigenspace ι τ := by
  intro x hx
  simp only [cmEigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  intro a
  have ha : a ∈ Algebra.adjoin ℚ {θ} := hθ ▸ Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact Module.End.mem_eigenspace_iff.mp hx
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
      LinearMap.baseChange_smul, LinearMap.baseChange_one, algebraMap_smul]
    rfl
  | add y z _ _ hy hz =>
    rw [map_add, LinearMap.baseChange_add, LinearMap.add_apply, hy, hz, map_add, add_smul]
  | mul y z _ _ hy hz =>
    rw [map_mul, LinearMap.baseChange_mul, Module.End.mul_apply, hz, LinearMap.map_smul, hy,
      smul_smul, map_mul, mul_comm]

/-- Spec S2. -/
theorem spec_a2a_iSup_eq_top_aux [FiniteDimensional ℚ V] (ι : L →ₐ[ℚ] Module.End ℚ V) :
    ⨆ τ : L →ₐ[ℚ] ℂ, cmEigenspace ι τ = ⊤ := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable ℚ L
  set T := (ι pb.gen).baseChange ℂ with hTdef
  set p := (minpoly ℚ pb.gen).map (algebraMap ℚ ℂ) with hpdef
  have hT : Polynomial.aeval T p = 0 := by
    have h0 : Polynomial.aeval (ι pb.gen) (minpoly ℚ pb.gen) = 0 := by
      rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    have h1 : T = Module.End.baseChangeHom ℚ ℂ V (ι pb.gen) := rfl
    rw [hpdef, Polynomial.aeval_map_algebraMap, h1, Polynomial.aeval_algHom_apply, h0, map_zero]
  have hsep : p.Separable := Polynomial.Separable.map (Algebra.IsSeparable.isSeparable ℚ pb.gen)
  have hss : Module.End.IsSemisimple T :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree hT
  refine eq_top_iff.mpr ?_
  rw [← hss.iSup_eigenspace_eq_top]
  refine iSup_le fun μ => ?_
  by_cases hμ : Polynomial.aeval μ (minpoly ℚ pb.gen) = 0
  · refine le_iSup_of_le (pb.lift μ hμ) ?_
    have h := a2a_eigenspace_gen_le ι pb.adjoin_gen_eq_top (pb.lift μ hμ)
    rwa [pb.lift_gen] at h
  · intro x hx
    by_contra hx0
    have hev : Module.End.HasEigenvector T μ x := ⟨hx, fun h => hx0 (h ▸ Submodule.zero_mem _)⟩
    have := Module.End.aeval_apply_of_hasEigenvector (p := p) hev
    rw [hT, LinearMap.zero_apply, hpdef, Polynomial.eval_map_algebraMap] at this
    exact hx0 (by
      rcases smul_eq_zero.mp this.symm with h | h
      · exact absurd h hμ
      · rw [h]; exact Submodule.zero_mem _)

/-- For `V = L` with the multiplication action, every `W_τ` is a line. -/
theorem a2a_finrank_cmEigenspace_lmul (τ : L →ₐ[ℚ] ℂ) :
    Module.finrank ℂ (cmEigenspace (Algebra.lmul ℚ L) τ) = 1 := by
  classical
  let W := cmEigenspace (Algebra.lmul ℚ L)
  have hpos : ∀ σ : L →ₐ[ℚ] ℂ, 1 ≤ Module.finrank ℂ (W σ) := by
    intro σ
    refine Nat.one_le_iff_ne_zero.mpr fun h0 => ?_
    have hbot : W σ = ⊥ := Submodule.finrank_eq_zero.mp h0
    let pb := Field.powerBasisOfFiniteOfSeparable ℚ L
    set f := ((Algebra.lmul ℚ L) pb.gen).baseChange ℂ
    let S := f - σ pb.gen • (LinearMap.id : Module.End ℂ (ℂ ⊗[ℚ] L))
    have hinj : Function.Injective S := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro x hx
      have hx' : x ∈ Module.End.eigenspace f (σ pb.gen) := by
        rw [Module.End.mem_eigenspace_iff]
        have := LinearMap.mem_ker.mp hx
        rwa [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at this
      rw [← hbot]
      exact a2a_eigenspace_gen_le _ pb.adjoin_gen_eq_top σ hx'
    obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hinj) (1 ⊗ₜ 1)
    let ψ : ℂ ⊗[ℚ] L →ₗ[ℂ] ℂ :=
      (Algebra.TensorProduct.lift (Algebra.ofId ℂ ℂ) σ (fun _ _ => Commute.all _ _)).toLinearMap
    have hψ : ∀ (a : L) (y : ℂ ⊗[ℚ] L),
        ψ (((Algebra.lmul ℚ L) a).baseChange ℂ y) = σ a * ψ y := by
      intro a y
      induction y with
      | tmul z b => simp [ψ, map_mul]; ring
      | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add, mul_add]
    have h1 : ψ (S y) = 0 := by
      simp only [S, f, LinearMap.sub_apply, map_sub, hψ, LinearMap.smul_apply, LinearMap.id_apply,
        map_smul, smul_eq_mul, sub_self]
    rw [hy] at h1
    simp [ψ] at h1
  let pb := Field.powerBasisOfFiniteOfSeparable ℚ L
  set f := ((Algebra.lmul ℚ L) pb.gen).baseChange ℂ
  have hW : W = fun σ => Module.End.eigenspace f (σ pb.gen) := funext fun σ =>
    le_antisymm (iInf_le _ pb.gen) (a2a_eigenspace_gen_le _ pb.adjoin_gen_eq_top σ)
  have hind : iSupIndep W := by
    rw [hW]
    exact (Module.End.eigenspaces_iSupIndep f).comp fun σ σ' h => pb.algHom_ext h
  have hint : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind (spec_a2a_iSup_eq_top_aux _)
  have hsum : ∑ σ, Module.finrank ℂ (W σ) = ∑ _σ : L →ₐ[ℚ] ℂ, 1 := by
    rw [Finset.sum_const, Finset.card_univ, AlgHom.card, smul_eq_mul, mul_one,
      ← Module.finrank_baseChange (R := ℂ),
      ← (LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hint).finrank_eq,
      Module.finrank_directSum]
  exact ((Finset.sum_eq_sum_iff_of_le fun σ _ => hpos σ).mp hsum.symm τ
    (Finset.mem_univ _)).symm

/-- The dimension of `W_τ` is invariant under an equivariant `ℚ`-linear equivalence. -/
theorem a2a_finrank_cmEigenspace_congr {V' : Type*} [AddCommGroup V'] [Module ℚ V']
    (ι : L →ₐ[ℚ] Module.End ℚ V) (ι' : L →ₐ[ℚ] Module.End ℚ V') (e : V ≃ₗ[ℚ] V')
    (he : ∀ a x, e (ι a x) = ι' a (e x)) (τ : L →ₐ[ℚ] ℂ) :
    Module.finrank ℂ (cmEigenspace ι τ) = Module.finrank ℂ (cmEigenspace ι' τ) := by
  let E : ℂ ⊗[ℚ] V ≃ₗ[ℂ] ℂ ⊗[ℚ] V' := e.baseChange ℚ ℂ V V'
  have hE : ∀ a x, E ((ι a).baseChange ℂ x) = (ι' a).baseChange ℂ (E x) := by
    intro a x
    induction x with
    | tmul z v => simp [E, he]
    | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  have hmap : (cmEigenspace ι τ).map (E : ℂ ⊗[ℚ] V →ₗ[ℂ] ℂ ⊗[ℚ] V') = cmEigenspace ι' τ := by
    ext y
    rw [Submodule.mem_map_equiv]
    simp only [cmEigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    refine forall_congr' fun a => ?_
    rw [← E.injective.eq_iff, hE, LinearEquiv.apply_symm_apply, map_smul,
      LinearEquiv.apply_symm_apply]
  rw [← hmap, LinearEquiv.finrank_map_eq]

/-- For `V = L^m` with the diagonal action, `dim W_τ = m · dim W_τ(L)`. -/
theorem a2a_finrank_cmEigenspace_pi (m : ℕ) (τ : L →ₐ[ℚ] ℂ) :
    Module.finrank ℂ (cmEigenspace ((Algebra.lmul ℚ (Fin m → L)).comp
      (IsScalarTower.toAlgHom ℚ L (Fin m → L))) τ) =
      m * Module.finrank ℂ (cmEigenspace (Algebra.lmul ℚ L) τ) := by
  classical
  set ι' := (Algebra.lmul ℚ (Fin m → L)).comp (IsScalarTower.toAlgHom ℚ L (Fin m → L))
  let P : ℂ ⊗[ℚ] (Fin m → L) ≃ₗ[ℂ] (Fin m → ℂ ⊗[ℚ] L) :=
    TensorProduct.piRight ℚ ℂ ℂ (fun _ : Fin m => L)
  have hP : ∀ a x i,
      P ((ι' a).baseChange ℂ x) i = ((Algebra.lmul ℚ L) a).baseChange ℂ (P x i) := by
    intro a x i
    induction x with
    | tmul z v => simp [P, ι']
    | add x x' hx hx' => simp only [map_add, Pi.add_apply, hx, hx']
  have hmem : ∀ x, x ∈ cmEigenspace ι' τ ↔
      ∀ i, P x i ∈ cmEigenspace (Algebra.lmul ℚ L) τ := by
    intro x
    simp only [cmEigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    constructor
    · intro h i a
      rw [← hP, h a, map_smul, Pi.smul_apply]
    · intro h a
      apply P.injective
      funext i
      rw [hP, h i a, map_smul, Pi.smul_apply]
  let F : cmEigenspace ι' τ ≃ₗ[ℂ] (Fin m → cmEigenspace (Algebra.lmul ℚ L) τ) :=
    { toFun := fun x i => ⟨P x i, (hmem x).mp x.2 i⟩
      invFun := fun y => ⟨P.symm (fun i => y i), (hmem _).mpr fun i => by simp⟩
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp
      left_inv := fun x => by ext1; simp
      right_inv := fun y => by ext i; simp }
  rw [F.finrank_eq, Module.finrank_pi_fintype]
  simp

/-- Spec S3. -/
theorem spec_a2a_finrank_aux [FiniteDimensional ℚ V] (ι : L →ₐ[ℚ] Module.End ℚ V)
    (τ : L →ₐ[ℚ] ℂ) :
    Module.finrank ℂ (cmEigenspace ι τ) * Module.finrank ℚ L = Module.finrank ℚ V := by
  classical
  let _ : Module L V := Module.compHom V ι.toRingHom
  have hsmul : ∀ (a : L) (x : V), a • x = ι a x := fun _ _ => rfl
  have : IsScalarTower ℚ L V := ⟨fun q a x => by
    rw [hsmul, hsmul, map_smul]; rfl⟩
  have : Module.Finite L V := Module.Finite.of_restrictScalars_finite ℚ L V
  let b := Module.finBasis L V
  let e : V ≃ₗ[ℚ] (Fin (Module.finrank L V) → L) := b.equivFun.restrictScalars ℚ
  have he : ∀ a x, e (ι a x) =
      ((Algebra.lmul ℚ (Fin (Module.finrank L V) → L)).comp
        (IsScalarTower.toAlgHom ℚ L (Fin (Module.finrank L V) → L))) a (e x) := by
    intro a x
    rw [← hsmul]
    change b.equivFun (a • x) = _
    rw [map_smul]
    ext i
    simp [e]
  rw [a2a_finrank_cmEigenspace_congr ι _ e he, a2a_finrank_cmEigenspace_pi,
    a2a_finrank_cmEigenspace_lmul, mul_one, mul_comm, Module.finrank_mul_finrank]

/-- Spec S5. -/
theorem spec_a2a_card_plus_aux (u : L) {d : ℚ} (hd : 0 < d) (hu : u ^ 2 = algebraMap ℚ L (-d)) :
    Nat.card {τ : L →ₐ[ℚ] ℂ // τ u = HodgeBlocks.WeilAction.omegaC d} * 2 =
      Module.finrank ℚ L := by
  classical
  set ω := HodgeBlocks.WeilAction.omegaC d with hωdef
  have hω2 : ω ^ 2 = -(d : ℂ) := HodgeBlocks.WeilAction.omegaC_sq hd
  have hω0 : ω ≠ 0 := HodgeBlocks.WeilAction.omegaC_ne_zero hd
  have hconj : starRingEnd ℂ ω = -ω := HodgeBlocks.WeilAction.conj_omegaC
  have hne : ω ≠ -ω := fun h => hω0 (by linear_combination h / 2)
  have hroot : ∀ τ : L →ₐ[ℚ] ℂ, τ u = ω ∨ τ u = -ω := by
    intro τ
    have h1 : τ u ^ 2 = ω ^ 2 := by
      rw [← map_pow, hu, hω2, AlgHom.commutes]; simp
    exact sq_eq_sq_iff_eq_or_eq_neg.mp h1
  let e1 : {τ : L →ₐ[ℚ] ℂ // ¬ τ u = ω} ≃ {τ : L →ₐ[ℚ] ℂ // τ u = -ω} :=
    Equiv.subtypeEquivRight fun τ =>
      ⟨fun h => (hroot τ).resolve_left h, fun h h' => hne (h'.symm.trans h)⟩
  let e2 : {τ : L →ₐ[ℚ] ℂ // τ u = ω} ≃ {τ : L →ₐ[ℚ] ℂ // τ u = -ω} :=
    { toFun := fun τ => ⟨cmConjEmbedding τ.1, by
        change starRingEnd ℂ (τ.1 u) = -ω; rw [τ.2, hconj]⟩
      invFun := fun τ => ⟨cmConjEmbedding τ.1, by
        change starRingEnd ℂ (τ.1 u) = ω; rw [τ.2, map_neg, hconj, neg_neg]⟩
      left_inv := fun τ => Subtype.ext (AlgHom.ext fun a => by
        change starRingEnd ℂ (starRingEnd ℂ (τ.1 a)) = τ.1 a; simp)
      right_inv := fun τ => Subtype.ext (AlgHom.ext fun a => by
        change starRingEnd ℂ (starRingEnd ℂ (τ.1 a)) = τ.1 a; simp) }
  have hc := AlgHom.card ℚ L ℂ
  have hcompl := Fintype.card_subtype_compl (fun τ : L →ₐ[ℚ] ℂ => τ u = ω)
  have hle := Fintype.card_subtype_le (fun τ : L →ₐ[ℚ] ℂ => τ u = ω)
  rw [Fintype.card_congr e1, ← Fintype.card_congr e2] at hcompl
  rw [Nat.card_eq_fintype_card]
  omega

/-- Spec S6. -/
theorem spec_a2a_iSup_eq_eigenspace_aux [FiniteDimensional ℚ V] (ι : L →ₐ[ℚ] Module.End ℚ V)
    (u : L) (ω : ℂ) :
    ⨆ (τ : L →ₐ[ℚ] ℂ) (_ : τ u = ω), cmEigenspace ι τ =
      Module.End.eigenspace ((ι u).baseChange ℂ) ω := by
  classical
  set f := (ι u).baseChange ℂ
  have hle : ∀ τ : L →ₐ[ℚ] ℂ, cmEigenspace ι τ ≤ Module.End.eigenspace f (τ u) :=
    fun τ => iInf_le _ u
  apply le_antisymm
  · exact iSup₂_le fun τ hτ => hτ ▸ hle τ
  · set P := ⨆ (τ : L →ₐ[ℚ] ℂ) (_ : τ u = ω), cmEigenspace ι τ
    set N := ⨆ (τ : L →ₐ[ℚ] ℂ) (_ : ¬ τ u = ω), cmEigenspace ι τ
    have htop : P ⊔ N = ⊤ := by
      rw [← iSup_split]; exact spec_a2a_iSup_eq_top_aux ι
    have hN : N ≤ ⨆ (μ : ℂ) (_ : μ ≠ ω), Module.End.eigenspace f μ :=
      iSup₂_le fun τ hτ => le_iSup₂_of_le (f := fun μ (_ : μ ≠ ω) => Module.End.eigenspace f μ)
        (τ u) hτ (hle τ)
    have hdisj : Disjoint (Module.End.eigenspace f ω) N :=
      ((Module.End.eigenspaces_iSupIndep f) ω).mono_right hN
    have hP : P ≤ Module.End.eigenspace f ω := iSup₂_le fun τ hτ => hτ ▸ hle τ
    refine le_of_eq ?_
    calc Module.End.eigenspace f ω = (P ⊔ N) ⊓ Module.End.eigenspace f ω := by
          rw [htop, top_inf_eq]
      _ = P ⊔ N ⊓ Module.End.eigenspace f ω := sup_inf_assoc_of_le N hP
      _ = P := by rw [hdisj.symm.eq_bot, sup_bot_eq]

/-- Spec S7. -/
theorem spec_a2a_cmPlusPart_eq_Vs_aux [FiniteDimensional ℚ V] (ι : L →ₐ[ℚ] Module.End ℚ V)
    {M : HodgeBlocks.QHodgeStructure 1 V} {d : ℚ} (A : HodgeBlocks.WeilAction M d) (u : L)
    (hJ : A.J = ι u) :
    cmPlusPart ι u d = A.Vs := by
  rw [cmPlusPart, HodgeBlocks.WeilAction.Vs, spec_a2a_iSup_eq_eigenspace_aux ι u,
    HodgeBlocks.WeilAction.Jc, hJ]

variable [IsCMField L]

/-- Spec S9. -/
theorem spec_a2a_orthogonal_aux (ι : L →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (τ τ' : L →ₐ[ℚ] ℂ) (h : τ' ≠ cmConjEmbedding τ)
    (x : ℂ ⊗[ℚ] V) (hx : x ∈ cmEigenspace ι τ) (y : ℂ ⊗[ℚ] V) (hy : y ∈ cmEigenspace ι τ') :
    E.baseChange ℂ x y = 0 := by
  refine spec_a2a_orthogonal_of_rosati_aux ι E
    ((IsCMField.complexConj L : L →+* L).toRatAlgHom) (fun a x y => hRos a x y) τ τ' ?_
    x hx y hy
  rintro rfl
  apply h
  ext a
  have h1 := IsCMField.complexEmbedding_complexConj L (τ' : L →+* ℂ) a
  simp only [cmConjEmbedding, AlgHom.coe_comp, Function.comp_apply]
  change τ' a = starRingEnd ℂ (τ' (IsCMField.complexConj L a))
  rw [show τ' (IsCMField.complexConj L a) = (τ' : L →+* ℂ) (IsCMField.complexConj L a) from rfl,
    h1, Complex.conj_conj]
  rfl

omit [IsCMField L] in
/-- A linear functional `E_ℂ(·, y)` vanishing on every `W_σ` vanishes, by S2. -/
theorem a2a_baseChange_eq_zero_of_forall [FiniteDimensional ℚ V] (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (y : ℂ ⊗[ℚ] V)
    (hy : ∀ σ : L →ₐ[ℚ] ℂ, ∀ x ∈ cmEigenspace ι σ, E.baseChange ℂ x y = 0)
    (x : ℂ ⊗[ℚ] V) : E.baseChange ℂ x y = 0 := by
  have hx : x ∈ ⨆ σ : L →ₐ[ℚ] ℂ, cmEigenspace ι σ := by
    rw [spec_a2a_iSup_eq_top_aux ι]; trivial
  refine Submodule.iSup_induction _ (motive := fun x => E.baseChange ℂ x y = 0) hx hy ?_ ?_
  · simp
  · intro x z hx hz
    simp only [map_add, LinearMap.add_apply, hx, hz, add_zero]

/-- Spec S10. -/
theorem spec_a2a_duality_bijective_aux [FiniteDimensional ℚ V] (ι : L →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hRos : ∀ (a : L) (x y : V), E (ι a x) y = E x (ι (IsCMField.complexConj L a) y))
    (τ : L →ₐ[ℚ] ℂ) :
    Function.Bijective (WeilPower.crossPairing (E.baseChange ℂ) (cmEigenspace ι τ)
      (cmEigenspace ι (cmConjEmbedding τ))) := by
  have hEc := WeilPower.nondegenerate_baseChange E hE
  have hinj : Function.Injective (WeilPower.crossPairing (E.baseChange ℂ) (cmEigenspace ι τ)
      (cmEigenspace ι (cmConjEmbedding τ))) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    rw [Submodule.mem_bot]
    apply Subtype.ext
    apply hEc.2
    refine a2a_baseChange_eq_zero_of_forall ι E _ (fun σ x hx => ?_)
    by_cases hσ : σ = τ
    · subst hσ
      exact LinearMap.congr_fun (LinearMap.mem_ker.mp hy) ⟨x, hx⟩
    · refine spec_a2a_orthogonal_aux ι E hRos σ _ ?_ x hx y y.2
      intro h
      apply hσ
      ext a
      have h2 := congrArg (fun f : L →ₐ[ℚ] ℂ => starRingEnd ℂ (f a)) h
      simpa [cmConjEmbedding] using h2.symm
  have hn : 0 < Module.finrank ℚ L := Module.finrank_pos
  have hfr : Module.finrank ℂ (cmEigenspace ι (cmConjEmbedding τ)) =
      Module.finrank ℂ (Module.Dual ℂ (cmEigenspace ι τ)) := by
    rw [Subspace.dual_finrank_eq]
    apply Nat.eq_of_mul_eq_mul_right hn
    rw [spec_a2a_finrank_aux, spec_a2a_finrank_aux]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp hinj⟩

/-- Spec S12. -/
theorem spec_a2a_orthogonal_fails_without_rosati_aux :
    (a2a_traceSymplectic L).Nondegenerate ∧ (a2a_traceSymplectic L).IsAlt ∧
      (∀ (a : L) (x y : L × L),
        a2a_traceSymplectic L (a2a_diagAction L a x) y =
          a2a_traceSymplectic L x (a2a_diagAction L a y)) ∧
      ∃ τ τ' : L →ₐ[ℚ] ℂ, τ' ≠ cmConjEmbedding τ ∧
        ∃ x ∈ cmEigenspace (a2a_diagAction L) τ, ∃ y ∈ cmEigenspace (a2a_diagAction L) τ',
          (a2a_traceSymplectic L).baseChange ℂ x y ≠ 0 := by
  have hT := (traceForm_nondegenerate ℚ L).1
  have hTr : ∀ a : L, (∀ z : L, Algebra.trace ℚ L (a * z) = 0) → a = 0 := fun a ha =>
    hT a (fun z => by rw [Algebra.traceForm_apply]; exact ha z)
  have happ : ∀ x y : L × L, a2a_traceSymplectic L x y =
      Algebra.trace ℚ L (x.1 * y.2) - Algebra.trace ℚ L (x.2 * y.1) := fun _ _ => rfl
  have hND : (a2a_traceSymplectic L).Nondegenerate := by
    constructor
    · intro x hx
      have h1 : x.1 = 0 := hTr _ fun z => by simpa [happ] using hx (0, z)
      have h2 : x.2 = 0 := hTr _ fun z => by simpa [happ] using hx (z, 0)
      exact Prod.ext h1 h2
    · intro y hy
      have h1 : y.1 = 0 := hTr _ fun z => by simpa [happ, mul_comm] using hy (0, z)
      have h2 : y.2 = 0 := hTr _ fun z => by simpa [happ, mul_comm] using hy (z, 0)
      exact Prod.ext h1 h2
  have hcompat : ∀ (a : L) (x y : L × L),
      a2a_traceSymplectic L (a2a_diagAction L a x) y =
        a2a_traceSymplectic L x (a2a_diagAction L a y) := by
    intro a x y
    have hd : ∀ z : L × L, a2a_diagAction L a z = (a * z.1, a * z.2) := fun z => by
      simp [a2a_diagAction]; rfl
    rw [happ, happ, hd, hd]
    simp only [mul_assoc, mul_left_comm a]
  refine ⟨hND, fun x => by rw [happ, mul_comm, sub_self], hcompat, ?_⟩
  -- an embedding `τ`, with `τ ≠ τ̄` since `L` is totally complex
  let τ : L →ₐ[ℚ] ℂ := (Classical.choice (inferInstance : Nonempty (L →+* ℂ))).toRatAlgHom
  have hτ : τ ≠ cmConjEmbedding τ := by
    intro h
    apply IsTotallyComplex.complexEmbedding_not_isReal (τ : L →+* ℂ)
    rw [ComplexEmbedding.isReal_iff]
    ext a
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact (congrArg (fun f : L →ₐ[ℚ] ℂ => f a) h).symm
  -- `W_τ ≠ 0`, by S3
  have hn : 0 < Module.finrank ℚ L := Module.finrank_pos
  have hW : Module.finrank ℂ (cmEigenspace (a2a_diagAction L) τ) ≠ 0 := by
    intro h0
    have := spec_a2a_finrank_aux (a2a_diagAction L) τ
    rw [h0, zero_mul, Module.finrank_prod] at this
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (p := cmEigenspace (a2a_diagAction L) τ) (fun h => hW (by rw [h, finrank_bot]))
  -- some `y ∈ W_σ` pairs nontrivially with `x`
  have hEc := WeilPower.nondegenerate_baseChange _ hND
  obtain ⟨σ, y, hy, hxy⟩ : ∃ σ : L →ₐ[ℚ] ℂ, ∃ y ∈ cmEigenspace (a2a_diagAction L) σ,
      (a2a_traceSymplectic L).baseChange ℂ x y ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hx0
    apply hEc.1
    intro z
    have hz : z ∈ ⨆ σ : L →ₐ[ℚ] ℂ, cmEigenspace (a2a_diagAction L) σ := by
      rw [spec_a2a_iSup_eq_top_aux]; trivial
    refine Submodule.iSup_induction _
      (motive := fun z => (a2a_traceSymplectic L).baseChange ℂ x z = 0) hz hall ?_ ?_
    · simp
    · intro z w hz hw
      simp only [map_add, hz, hw, add_zero]
  -- by S8 for `c = id`, `σ = τ`
  have hστ : τ = σ := by
    by_contra hne
    exact hxy (spec_a2a_orthogonal_of_rosati_aux (a2a_diagAction L) (a2a_traceSymplectic L)
      (AlgHom.id ℚ L) hcompat τ σ hne x hx y hy)
  subst hστ
  exact ⟨τ, τ, hτ, x, hx, y, hy, hxy⟩

end NumberField

end HodgeLean.Foundations
