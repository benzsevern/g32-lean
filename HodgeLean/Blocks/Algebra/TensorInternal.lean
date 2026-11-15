import Mathlib
import HodgeLean.Blocks.Algebra.PiTensorInjective

/-! # Internal direct sums and tensor products

General lemmas for tensoring internal families and regrouping internal families.
-/

open scoped DirectSum TensorProduct

noncomputable section

/-- Tensor products of the summands in two internal direct sums form an internal direct sum. -/
theorem DirectSum.IsInternal.tensor {R M N ι κ : Type*} [Field R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [DecidableEq ι] [DecidableEq κ]
    {A : ι → Submodule R M} {B : κ → Submodule R N}
    (hA : DirectSum.IsInternal A) (hB : DirectSum.IsInternal B) :
    DirectSum.IsInternal (fun p : ι × κ =>
      LinearMap.range (TensorProduct.mapIncl (A p.1) (B p.2))) := by
  let C : ι × κ → Submodule R (M ⊗[R] N) := fun p =>
    LinearMap.range (TensorProduct.mapIncl (A p.1) (B p.2))
  have hinj (p : ι × κ) :
      Function.Injective (TensorProduct.mapIncl (A p.1) (B p.2)) :=
    TensorProduct.map_injective_of_flat_flat _ _
      (A p.1).subtype_injective (B p.2).subtype_injective
  let eA : (⨁ i : ι, A i) ≃ₗ[R] M :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hA
  let eB : (⨁ i : κ, B i) ≃ₗ[R] N :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap B) hB
  let eC (p : ι × κ) : (A p.1) ⊗[R] (B p.2) ≃ₗ[R] C p :=
    LinearEquiv.ofInjective (TensorProduct.mapIncl (A p.1) (B p.2)) (hinj p)
  let Φ : ((⨁ i : ι, A i) ⊗[R] (⨁ j : κ, B j)) ≃ₗ[R]
      (⨁ p : ι × κ, C p) :=
    (TensorProduct.directSum R R (fun i : ι => A i) (fun j : κ => B j)).trans
      (DirectSum.congrLinearEquiv (fun p : ι × κ => eC p))
  let E : (⨁ p : ι × κ, C p) ≃ₗ[R] M ⊗[R] N :=
    Φ.symm.trans (TensorProduct.congr eA eB)
  have hmaps : DirectSum.coeLinearMap C = E.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro p
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := (eC p).surjective x
    have hcongr (z : (A p.1) ⊗[R] (B p.2)) :
        (DirectSum.congrLinearEquiv (fun q : ι × κ => eC q)).symm
          (DirectSum.lof R (ι × κ) (fun q => ↥(C q)) p (eC p z)) =
            DirectSum.lof R (ι × κ)
              (fun q => (A q.1) ⊗[R] (B q.2)) p z := by
      rw [LinearEquiv.symm_apply_eq]
      rw [DirectSum.coe_congrLinearEquiv]
      simp
    induction x using TensorProduct.induction_on with
    | zero =>
        rw [(eC p).map_zero, map_zero, map_zero]
    | tmul a b =>
        rcases p with ⟨i, j⟩
        simp only [LinearMap.coe_comp, Function.comp_apply, DirectSum.coeLinearMap_lof,
          LinearEquiv.coe_coe, LinearEquiv.trans_apply]
        simp only [E, LinearEquiv.trans_apply]
        rw [show Φ.symm (DirectSum.lof R (ι × κ) (fun q => ↥(C q)) (i, j)
            (eC (i, j) (a ⊗ₜ[R] b))) =
            (TensorProduct.directSum R R (fun i : ι => A i) (fun j : κ => B j)).symm
              (DirectSum.lof R (ι × κ)
                (fun q => (A q.1) ⊗[R] (B q.2)) (i, j) (a ⊗ₜ[R] b)) by
          simp only [Φ, LinearEquiv.trans_symm, LinearEquiv.trans_apply]
          exact congrArg _ (hcongr (a ⊗ₜ[R] b))]
        rw [LinearEquiv.ofInjective_apply]
        rw [TensorProduct.directSum_symm_lof_tmul]
        rw [TensorProduct.congr_tmul]
        change (a : M) ⊗ₜ[R] (b : N) =
          DirectSum.coeLinearMap A
              (DirectSum.lof R ι (fun k => ↥(A k)) i a) ⊗ₜ[R]
            DirectSum.coeLinearMap B
              (DirectSum.lof R κ (fun k => ↥(B k)) j b)
        simp
    | add x y hx hy =>
        rw [(eC p).map_add, map_add, map_add, hx, hy]
  change Function.Bijective (DirectSum.coeLinearMap C)
  rw [hmaps]
  exact E.bijective

#print axioms DirectSum.IsInternal.tensor

/-- Regrouping the summands of an internal direct sum along arbitrary fibres preserves
internality. -/
theorem DirectSum.IsInternal.regroupFibers {R M ι κ L : Type*} [Field R]
    [AddCommGroup M] [Module R M] [DecidableEq ι] [DecidableEq κ] [DecidableEq L]
    {C : ι × κ → Submodule R M} (f : ι × κ → L)
    (hC : DirectSum.IsInternal C) :
    DirectSum.IsInternal (fun l => ⨆ p ∈ f ⁻¹' {l}, C p) := by
  apply (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
  constructor
  · intro l
    have hd := hC.submodule_iSupIndep.disjoint_biSup_biSup
      (disjoint_compl_right : Disjoint (f ⁻¹' {l}) (f ⁻¹' {l})ᶜ)
    refine hd.mono le_rfl ?_
    refine iSup_le fun l' => iSup_le fun hl' => ?_
    refine iSup_le fun p => iSup_le fun hp => ?_
    refine le_iSup_of_le p (le_iSup_of_le ?_ le_rfl)
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff] at hp ⊢
    intro hpl
    exact hl' (hp.symm.trans hpl)
  · apply top_unique
    rw [← hC.submodule_iSup_eq_top]
    refine iSup_le fun p => ?_
    exact le_iSup_of_le (f p) <|
      le_iSup_of_le p <| le_iSup_of_le (by simp) le_rfl

#print axioms DirectSum.IsInternal.regroupFibers

/-- The kernel of an endomorphism preserving every summand inherits the internal direct-sum
decomposition, with summands given by the traces of the original summands on the kernel. -/
theorem DirectSum.IsInternal.ker_isInternal {R M ι : Type*} [Field R]
    [AddCommGroup M] [Module R M] [DecidableEq ι] {A : ι → Submodule R M}
    (hA : DirectSum.IsInternal A) (f : M →ₗ[R] M)
    (hf : ∀ i, ∀ x ∈ A i, f x ∈ A i) :
    DirectSum.IsInternal
      (fun i => (A i ⊓ LinearMap.ker f).submoduleOf (LinearMap.ker f)) := by
  classical
  let B : ι → Submodule R (LinearMap.ker f) := fun i =>
    (A i ⊓ LinearMap.ker f).submoduleOf (LinearMap.ker f)
  let e : (⨁ i, A i) ≃ₗ[R] M :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hA
  let fi (i : ι) : A i →ₗ[R] A i :=
    f.restrict (hf i)
  let g : (⨁ i, A i) →ₗ[R] (⨁ i, A i) :=
    DirectSum.lmap fi
  have commute : DirectSum.coeLinearMap A ∘ₗ g = f ∘ₗ DirectSum.coeLinearMap A := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    simp [g, fi]
  constructor
  · intro z w hzw
    let bi (i : ι) : B i →ₗ[R] A i :=
      { toFun := fun x => ⟨(x : LinearMap.ker f), x.2.1⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let lift (u : ⨁ i, B i) : ⨁ i, A i :=
      DirectSum.lmap bi u
    have lift_coe (u : ⨁ i, B i) :
        DirectSum.coeLinearMap A (lift u) =
          (DirectSum.coeLinearMap B u : LinearMap.ker f) := by
      change (DirectSum.coeLinearMap A ∘ₗ DirectSum.lmap bi) u =
        ((LinearMap.ker f).subtype ∘ₗ DirectSum.coeLinearMap B) u
      congr 1
      apply DirectSum.linearMap_ext
      intro i
      apply LinearMap.ext
      intro v
      simp [bi, B]
    have hlift : lift z = lift w := by
      apply hA.injective
      change DirectSum.coeLinearMap A (lift z) = DirectSum.coeLinearMap A (lift w)
      rw [lift_coe, lift_coe]
      exact congrArg Subtype.val hzw
    apply DFinsupp.ext
    intro i
    have hi := congrArg (fun q => q i) hlift
    apply Subtype.ext
    simpa [lift, bi, B] using congrArg Subtype.val hi
  · intro x
    let y : ⨁ i, A i := e.symm (x : M)
    have hgy : g y = 0 := by
      apply hA.injective
      change DirectSum.coeLinearMap A (g y) = DirectSum.coeLinearMap A 0
      rw [LinearMap.map_zero, ← LinearMap.comp_apply, commute, LinearMap.comp_apply]
      change f (e (e.symm (x : M))) = 0
      rw [e.apply_symm_apply]
      exact x.2
    have hyker (i : ι) : f (y i : M) = 0 := by
      have hi := congrArg (fun q => q i) hgy
      simpa [g, fi] using congrArg Subtype.val hi
    let z : ⨁ i, B i := DFinsupp.mk y.support fun i =>
      ⟨⟨(y i : M), hyker i⟩, (y i).2, hyker i⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    change ((DirectSum.coeLinearMap B z : LinearMap.ker f) : M) = x
    let bi (i : ι) : B i →ₗ[R] A i :=
      { toFun := fun v => ⟨(v : LinearMap.ker f), v.2.1⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let za : ⨁ i, A i := DirectSum.lmap bi z
    have hza : za = y := by
      apply DFinsupp.ext
      intro i
      by_cases hi : i ∈ y.support
      · simp [za, z, bi, B, hi]
      · have hy0 : y i = 0 := by simpa [DFinsupp.mem_support_iff] using hi
        simp [za, z, bi, B, hi, hy0]
    have hcoe : ((DirectSum.coeLinearMap B z : LinearMap.ker f) : M) =
        DirectSum.coeLinearMap A za := by
      change ((LinearMap.ker f).subtype ∘ₗ DirectSum.coeLinearMap B) z =
        (DirectSum.coeLinearMap A ∘ₗ DirectSum.lmap bi) z
      congr 1
      apply DirectSum.linearMap_ext
      intro i
      apply LinearMap.ext
      intro v
      simp [bi, B]
    calc
      ((DirectSum.coeLinearMap B z : LinearMap.ker f) : M) =
          DirectSum.coeLinearMap A za := hcoe
      _ = DirectSum.coeLinearMap A y := congrArg _ hza
      _ = x := by
        change e (e.symm (x : M)) = x
        exact e.apply_symm_apply _

#print axioms DirectSum.IsInternal.ker_isInternal

/-- The kernel of an endomorphism preserving every summand is the supremum of its
intersections with those summands in the ambient module. -/
theorem DirectSum.IsInternal.ker_eq_iSup_inf {R M ι : Type*} [Field R]
    [AddCommGroup M] [Module R M] [DecidableEq ι] {A : ι → Submodule R M}
    (hA : DirectSum.IsInternal A) (f : M →ₗ[R] M)
    (hf : ∀ i, ∀ x ∈ A i, f x ∈ A i) :
    LinearMap.ker f = ⨆ i, LinearMap.ker f ⊓ A i := by
  let K := LinearMap.ker f
  have hint := hA.ker_isInternal f hf
  have htop : ⨆ i, (A i ⊓ K).submoduleOf K = (⊤ : Submodule R K) :=
    hint.submodule_iSup_eq_top
  have hmap := congrArg (Submodule.map K.subtype) htop
  simp only [Submodule.map_iSup] at hmap
  have hpiece (i : ι) :
      Submodule.map K.subtype ((A i ⊓ K).submoduleOf K) = K ⊓ A i := by
    rw [show (A i ⊓ K).submoduleOf K =
      Submodule.comap K.subtype (A i ⊓ K) by rfl]
    rw [Submodule.map_comap_subtype]
    simp [inf_comm]
  have hwhole : Submodule.map K.subtype (⊤ : Submodule R K) = K := by
    rw [← LinearMap.range_eq_map]
    exact Submodule.range_subtype K
  rw [hwhole] at hmap
  simpa only [hpiece] using hmap.symm

#print axioms DirectSum.IsInternal.ker_eq_iSup_inf

/-- Tensor products of the summands in a finite family of internal direct sums form an
internal direct sum. -/
theorem DirectSum.IsInternal.piTensor {R ι : Type*} [Field R] [Fintype ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    {κ : ι → Type*} [∀ i, DecidableEq (κ i)]
    {A : ∀ i, κ i → Submodule R (M i)} (hA : ∀ i, DirectSum.IsInternal (A i)) :
    DirectSum.IsInternal (fun p : ∀ i, κ i =>
      LinearMap.range (PiTensorProduct.map fun i => (A i (p i)).subtype)) := by
  let C : (∀ i, κ i) → Submodule R (PiTensorProduct R M) := fun p =>
    LinearMap.range (PiTensorProduct.map fun i => (A i (p i)).subtype)
  have hinj (p : ∀ i, κ i) :
      Function.Injective (PiTensorProduct.map fun i => (A i (p i)).subtype) :=
    PiTensorProduct.map_injective_of_field
      (fun i => A i (p i)) M (fun i => (A i (p i)).subtype)
      (fun i => (A i (p i)).subtype_injective)
  let eA (i : ι) : (⨁ j : κ i, A i j) ≃ₗ[R] M i :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap (A i)) (hA i)
  let eC (p : ∀ i, κ i) : (⨂[R] i, A i (p i)) ≃ₗ[R] C p :=
    LinearEquiv.ofInjective (PiTensorProduct.map fun i => (A i (p i)).subtype) (hinj p)
  let Φ : (⨂[R] i, ⨁ j : κ i, A i j) ≃ₗ[R] (⨁ p : ∀ i, κ i, C p) :=
    PiTensorProduct.ofDirectSumEquiv.trans
      (DirectSum.congrLinearEquiv (fun p => eC p))
  let E : (⨁ p : ∀ i, κ i, C p) ≃ₗ[R] PiTensorProduct R M :=
    Φ.symm.trans (PiTensorProduct.congr eA)
  have hmaps : DirectSum.coeLinearMap C = E.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro p
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := (eC p).surjective x
    have hcongr (z : ⨂[R] i, A i (p i)) :
        (DirectSum.congrLinearEquiv (fun q => eC q)).symm
          (DirectSum.lof R (∀ i, κ i) (fun q => ↥(C q)) p (eC p z)) =
            DirectSum.lof R (∀ i, κ i)
              (fun q => ⨂[R] i, A i (q i)) p z := by
      rw [LinearEquiv.symm_apply_eq]
      rw [DirectSum.coe_congrLinearEquiv]
      simp
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r x =>
        simp only [map_smul, LinearMap.coe_comp, Function.comp_apply,
          DirectSum.coeLinearMap_lof, LinearEquiv.coe_coe, LinearEquiv.trans_apply]
        simp only [E, LinearEquiv.trans_apply]
        apply congrArg (r • ·)
        rw [show Φ.symm (DirectSum.lof R (∀ i, κ i) (fun q => ↥(C q)) p
            (eC p (PiTensorProduct.tprod R x))) =
            PiTensorProduct.ofDirectSumEquiv.symm
              (DirectSum.lof R (∀ i, κ i)
                (fun q => ⨂[R] i, A i (q i)) p
                (PiTensorProduct.tprod R x)) by
          simp only [Φ, LinearEquiv.trans_symm, LinearEquiv.trans_apply]
          exact congrArg _ (hcongr (PiTensorProduct.tprod R x))]
        rw [LinearEquiv.ofInjective_apply,
          PiTensorProduct.ofDirectSumEquiv_symm_lof_tprod]
        rw [PiTensorProduct.map_tprod]
        simp only [PiTensorProduct.congr_tprod]
        congr 1
        funext i
        change (x i : M i) = DirectSum.coeLinearMap (A i)
          (DirectSum.lof R (κ i) (fun j => ↥(A i j)) (p i) (x i))
        simp
    | add x y hx hy =>
        rw [(eC p).map_add, map_add, map_add, hx, hy]
  change Function.Bijective (DirectSum.coeLinearMap C)
  rw [hmaps]
  exact E.bijective

#print axioms DirectSum.IsInternal.piTensor

/-- Regrouping an arbitrary internal family along arbitrary fibres preserves internality. -/
theorem DirectSum.IsInternal.regroupFibers' {R M ι L : Type*} [Field R]
    [AddCommGroup M] [Module R M] [DecidableEq ι] [DecidableEq L]
    {C : ι → Submodule R M} (f : ι → L) (hC : DirectSum.IsInternal C) :
    DirectSum.IsInternal (fun l => ⨆ p ∈ f ⁻¹' {l}, C p) := by
  apply (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
  constructor
  · intro l
    have hd := hC.submodule_iSupIndep.disjoint_biSup_biSup
      (disjoint_compl_right : Disjoint (f ⁻¹' {l}) (f ⁻¹' {l})ᶜ)
    refine hd.mono le_rfl ?_
    refine iSup_le fun l' => iSup_le fun hl' => ?_
    refine iSup_le fun p => iSup_le fun hp => ?_
    refine le_iSup_of_le p (le_iSup_of_le ?_ le_rfl)
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff] at hp ⊢
    intro hpl
    exact hl' (hp.symm.trans hpl)
  · apply top_unique
    rw [← hC.submodule_iSup_eq_top]
    refine iSup_le fun p => ?_
    exact le_iSup_of_le (f p) <|
      le_iSup_of_le p <| le_iSup_of_le (by simp) le_rfl

#print axioms DirectSum.IsInternal.regroupFibers'

/-- Quotienting an internal direct sum by a submodule split across its summands
preserves internality of the images. -/
theorem DirectSum.IsInternal.quotientMap_isInternal {R M ι : Type*} [Field R]
    [AddCommGroup M] [Module R M] [DecidableEq ι] {A : ι → Submodule R M}
    (hA : DirectSum.IsInternal A) (K : Submodule R M) (hK : K = ⨆ i, K ⊓ A i) :
    DirectSum.IsInternal (fun i => (A i).map K.mkQ) := by
  classical
  apply (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
  constructor
  · rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro x hxA hxS
    let S : Submodule R M := ⨆ j, ⨆ _ : j ≠ i, A j
    let Ki : Submodule R M := K ⊓ A i
    have hmapS : (⨆ j, ⨆ _ : j ≠ i, (A j).map K.mkQ) = S.map K.mkQ := by
      simp only [S, Submodule.map_iSup]
    obtain ⟨a, ha, rfl⟩ := hxA
    rw [hmapS] at hxS
    obtain ⟨b, hb, hab⟩ := hxS
    have habK : a - b ∈ K := by
      rw [← Submodule.ker_mkQ K]
      rw [LinearMap.mem_ker]
      simpa using congrArg (fun z => z - K.mkQ b) hab.symm
    have haSup : a ∈ S ⊔ K := by
      rw [show a = b + (a - b) by abel]
      exact Submodule.add_mem_sup hb habK
    have hK_le : K ≤ S ⊔ Ki := by
      rw [hK]
      refine iSup_le fun l => ?_
      by_cases hli : l = i
      · subst l
        exact le_sup_right
      · refine le_trans inf_le_right ?_
        exact le_trans
          (le_iSup_of_le l (le_iSup (fun _ : l ≠ i => A l) hli)) le_sup_left
    have hsup_le : S ⊔ K ≤ S ⊔ Ki := sup_le le_sup_left hK_le
    have hSi : S ⊓ A i = ⊥ := by
      have hd : Disjoint (A i) S := by
        have hind := hA.submodule_iSupIndep
        rw [iSupIndep_def] at hind
        exact hind i
      rw [inf_comm]
      exact disjoint_iff.mp hd
    have hclaim : A i ⊓ (S ⊔ K) ≤ K := by
      refine le_trans (inf_le_inf_left (A i) hsup_le) ?_
      rw [inf_comm, sup_comm]
      rw [sup_inf_assoc_of_le S inf_le_right]
      rw [hSi]
      simp only [sup_bot_eq]
      exact inf_le_left
    have haK : a ∈ K := hclaim ⟨ha, haSup⟩
    exact (Submodule.Quotient.mk_eq_zero K).2 haK
  · rw [← Submodule.map_iSup, hA.submodule_iSup_eq_top]
    rw [← LinearMap.range_eq_map]
    exact Submodule.range_mkQ K

#print axioms DirectSum.IsInternal.quotientMap_isInternal
