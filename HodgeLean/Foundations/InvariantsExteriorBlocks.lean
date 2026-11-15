import HodgeLean.Foundations.InvariantsExterior

/-! # Exterior images of tensor blocks

F-1575 (1) is proved in `sl(W)` Lie form by `invariants_eq_generatedDegree`.
The `SL(W)` group form is not proved. The proof uses the tensor first fundamental
theorem and polarization, rather than TR54 §3, with exactly the same generating set.

`TensorGenerated` makes exterior-span membership independent of slot order.
Local pair sums factor by induction, and determinant powers factor by their recursive
definition. The resulting block images close the colored-word assembly.
-/

open PiTensorProduct Finset Module
open scoped TensorProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] HodgeLean.Foundations.SchurWeyl.dualAddCommGroup
namespace HodgeLean.Foundations.InvariantsExterior
open SchurWeyl

variable {K W U U' : Type*} [Field K] [CharZero K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup U] [Module K U] [AddCommGroup U'] [Module K U']

/-- Extensionality on two pure tensor families, without partially applied curry maps. -/
theorem tensorMap_ext_tprod {I J A B C : Type*}
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [AddCommGroup C] [Module K C]
    {f g : (⨂[K] _ : I, A) ⊗[K] (⨂[K] _ : J, B) →ₗ[K] C}
    (h : ∀ v w, f (tprod K v ⊗ₜ[K] tprod K w) = g (tprod K v ⊗ₜ[K] tprod K w)) :
    f = g := by
  apply TensorProduct.ext'
  intro s t
  induction s using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    induction t using PiTensorProduct.induction_on with
    | smul_tprod d w =>
      simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul, h]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]

/-- The corresponding extensionality statement for three local tensor factors. -/
theorem tensorMap_ext_three_tprod {I J L A B C D : Type*}
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [AddCommGroup C] [Module K C] [AddCommGroup D] [Module K D]
    {f g : ((⨂[K] _ : I, A) ⊗[K] (⨂[K] _ : J, B)) ⊗[K] (⨂[K] _ : L, C) →ₗ[K] D}
    (h : ∀ v w z, f ((tprod K v ⊗ₜ[K] tprod K w) ⊗ₜ[K] tprod K z) =
      g ((tprod K v ⊗ₜ[K] tprod K w) ⊗ₜ[K] tprod K z)) : f = g := by
  apply TensorProduct.ext_threefold
  intro s t u
  induction s using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    induction t using PiTensorProduct.induction_on with
    | smul_tprod d w =>
      induction u using PiTensorProduct.induction_on with
      | smul_tprod e z =>
        simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul, h]
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | add x y hx hy => simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add, hx, hy]
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]

/-- A tensor whose exterior image is generated, in every ordering of its slots. -/
private def TensorGenerated {I : Type*} (t : ⨂[K] _ : I, Space K W U U') : Prop :=
  ∀ (k : ℕ) (e : I ≃ Fin k),
    wedgeQuotient k (PiTensorProduct.reindex K (fun _ => Space K W U U') e t) ∈ generatedDegree k

/-- Checking one ordering suffices: all other orderings differ by a sign. -/
theorem tensorGenerated_of_order {I : Type*} {k : ℕ} (e : I ≃ Fin k)
    (t : ⨂[K] _ : I, Space K W U U')
    (ht : wedgeQuotient k (PiTensorProduct.reindex K (fun _ => Space K W U U') e t) ∈ generatedDegree k) :
    TensorGenerated t := by
  intro l d
  have hkl : k = l := Fintype.card_fin k ▸ Fintype.card_fin l ▸
    Fintype.card_congr (e.symm.trans d)
  subst l
  have he : (PiTensorProduct.reindex K (fun _ => Space K W U U') d).toLinearMap =
      (permRep K (Space K W U U') (Fin k) (e.symm.trans d)).comp
        (PiTensorProduct.reindex K (fun _ => Space K W U U') e).toLinearMap := by
    ext v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, reindex_tprod, permRep_tprod]
    congr 1
    funext i
    change v (d.symm i) = v (e.symm (e (d.symm i)))
    rw [e.symm_apply_apply]
  rw [show PiTensorProduct.reindex K (fun _ => Space K W U U') d t = _ from LinearMap.congr_fun he t]
  exact wedgeQuotient_permRep_mem _ _ ht

/-- Relabelling an arbitrary finite set of slots preserves generated images. -/
theorem TensorGenerated.reindex {I J : Type*} (e : I ≃ J)
    {t : ⨂[K] _ : I, Space K W U U'} (ht : TensorGenerated t) :
    TensorGenerated (PiTensorProduct.reindex K (fun _ => Space K W U U') e t) := by
  intro k d
  rw [reindex_reindex (R := K) (s := fun _ : I => Space K W U U') e d]
  exact ht k (e.trans d)

/-- The tensor product of two generated blocks is generated in every slot ordering. -/
theorem TensorGenerated.tmul {I J : Type*} [Fintype I] [Fintype J]
    {s : ⨂[K] _ : I, Space K W U U'} {t : ⨂[K] _ : J, Space K W U U'}
    (hs : TensorGenerated s) (ht : TensorGenerated t) :
    TensorGenerated (tmulEquiv K (Space K W U U') (s ⊗ₜ[K] t)) := by
  let e := Fintype.equivFin I
  let d := Fintype.equivFin J
  let q := (Equiv.sumCongr e d).trans finSumFinEquiv
  apply tensorGenerated_of_order q
  have he : (PiTensorProduct.reindex K (fun _ => Space K W U U') q).toLinearMap.comp
      (tmulEquiv K (Space K W U U')).toLinearMap =
      (tensorAppend (K := K) (M := Space K W U U') (Fintype.card I) (Fintype.card J)).toLinearMap.comp
        (TensorProduct.map (PiTensorProduct.reindex K (fun _ => Space K W U U') e).toLinearMap
          (PiTensorProduct.reindex K (fun _ => Space K W U U') d).toLinearMap) := by
    apply tensorMap_ext_tprod
    intro v w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, tmulEquiv_apply,
      TensorProduct.map_tmul, reindex_tprod, tensorAppend_tprod]
    congr 1
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [q, Fin.append, Function.comp_def]
  rw [show PiTensorProduct.reindex K (fun _ => Space K W U U') q
      (tmulEquiv K (Space K W U U') (s ⊗ₜ[K] t)) = _ from LinearMap.congr_fun he (s ⊗ₜ[K] t)]
  exact wedgeQuotient_tensorAppend_mem _ _ (hs _ e) (ht _ d)

/-- Slotwise maps commute with concatenation, including independent multiplicities. -/
theorem map_tmulEquiv {I J A B : Type*}
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    (f : I ⊕ J → A →ₗ[K] B) (s : ⨂[K] _ : I, A) (t : ⨂[K] _ : J, A) :
    PiTensorProduct.map f (tmulEquiv K A (s ⊗ₜ[K] t)) =
      tmulEquiv K B (PiTensorProduct.map (fun i => f (.inl i)) s ⊗ₜ[K]
        PiTensorProduct.map (fun j => f (.inr j)) t) := by
  suffices h : (PiTensorProduct.map f).comp (tmulEquiv K A).toLinearMap =
      (tmulEquiv K B).toLinearMap.comp (TensorProduct.map
        (PiTensorProduct.map (fun i => f (.inl i)))
        (PiTensorProduct.map (fun j => f (.inr j)))) from LinearMap.congr_fun h _
  apply tensorMap_ext_tprod
  intro v w
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, tmulEquiv_apply,
    map_tprod, TensorProduct.map_tmul]
  congr 1
  funext i
  cases i <;> rfl

/-- The empty tensor has the empty generator product as its exterior image. -/
theorem tensorGenerated_empty {I : Type*} [IsEmpty I] (v : I → Space K W U U') :
    TensorGenerated (tprod K v) := by
  let e : I ≃ Fin 0 := Equiv.equivOfIsEmpty I (Fin 0)
  apply tensorGenerated_of_order e
  simp only [reindex_tprod, wedgeQuotient_tprod]
  have h : (fun i => v (e.symm i)) = Fin.elim0 := funext fun i => Fin.elim0 i
  rw [h]
  exact Submodule.subset_span GeneratorProduct.unit

/-- All vector determinant powers with independent multiplicities are generated. -/
theorem tensorGenerated_detPowDual (m : ℕ) (a : Blocks (finrank K W) m → U) :
    TensorGenerated (PiTensorProduct.map (fun i => vectorIn (U' := U') (a i))
      (detPowDual K W m)) := by
  induction m with
  | zero =>
    simp only [detPowDual, map_tprod]
    exact tensorGenerated_empty _
  | succ m ih =>
    change Fin (finrank K W) ⊕ Blocks (finrank K W) m → _ at a
    change TensorGenerated (PiTensorProduct.map _
      (tmulEquiv K W (detTensorDual K W ⊗ₜ[K] detPowDual K W m)))
    rw [map_tmulEquiv (K := K)]
    apply TensorGenerated.tmul
    · apply tensorGenerated_of_order (Equiv.refl _)
      simpa only [reindex_refl, LinearEquiv.refl_apply] using
        wedgeQuotient_detTensorDual_mem (U' := U') (fun i => a (.inl i))
    · exact ih (fun i => a (.inr i))

/-- All covector determinant powers with independent multiplicities are generated. -/
theorem tensorGenerated_detPow (m : ℕ) (a : Blocks (finrank K W) m → U') :
    TensorGenerated (PiTensorProduct.map (fun i => dualIn (U := U) (a i))
      (detPow K W m)) := by
  induction m with
  | zero =>
    simp only [detPow, map_tprod]
    exact tensorGenerated_empty _
  | succ m ih =>
    change Fin (finrank K W) ⊕ Blocks (finrank K W) m → _ at a
    change TensorGenerated (PiTensorProduct.map _
      (tmulEquiv K (Module.Dual K W) (detTensor K W ⊗ₜ[K] detPow K W m)))
    rw [map_tmulEquiv (K := K)]
    apply TensorGenerated.tmul
    · apply tensorGenerated_of_order (Equiv.refl _)
      simpa only [reindex_refl, LinearEquiv.refl_apply] using
        wedgeQuotient_detTensor_mem (U := U) (fun i => a (.inl i))
    · exact ih (fun i => a (.inr i))

/-- Separate the first local factor from the remaining pair slots. -/
private def pairSlotsSucc (n : ℕ) : Fin 2 ⊕ (Fin n × Fin 2) ≃ Fin (n + 1) × Fin 2 where
  toFun := Sum.elim (fun j => (0, j)) (fun p => (p.1.succ, p.2))
  invFun p := Fin.cases (.inl p.2) (fun i => .inr (i, p.2)) p.1
  left_inv p := by cases p <;> rfl
  right_inv p := by rcases p with ⟨i,j⟩; refine Fin.cases ?_ (fun i => ?_) i <;> rfl

/-- A finite collection of local pair tensors, expanded independently, is generated
when each local sum is generated. This is the multiple-pair regrouping calculation. -/
theorem tensorGenerated_pairSums {B : Type*} [Fintype B] (n : ℕ)
    (v : Fin n → B → Fin 2 → Space K W U U')
    (hv : ∀ i, TensorGenerated (∑ b, tprod K (v i b))) :
    TensorGenerated (∑ f : Fin n → B, tprod K (fun p : Fin n × Fin 2 => v p.1 (f p.1) p.2)) := by
  induction n with
  | zero =>
    simp only [Fintype.sum_unique]
    exact tensorGenerated_empty _
  | succ n ih =>
    have h := ((hv 0).tmul (ih (fun i => v i.succ) (fun i => hv i.succ))).reindex
      (pairSlotsSucc n)
    have he : (∑ f : Fin (n + 1) → B,
        tprod K (fun p : Fin (n + 1) × Fin 2 => v p.1 (f p.1) p.2)) =
        PiTensorProduct.reindex K (fun _ => Space K W U U') (pairSlotsSucc n)
          (tmulEquiv K (Space K W U U')
            ((∑ b, tprod K (v 0 b)) ⊗ₜ[K]
              (∑ f : Fin n → B, tprod K (fun p : Fin n × Fin 2 => v p.1.succ (f p.1) p.2)))) := by
      rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => B)).sum_comp]
      simp only [Fintype.sum_prod_type, TensorProduct.sum_tmul, TensorProduct.tmul_sum,
        map_sum, tmulEquiv_apply, reindex_tprod]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro f _
      congr 1
      funext p
      rcases p with ⟨i,j⟩
      refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    rw [he]
    exact h

/-- A local contraction pair has exactly the generator θ as its exterior image. -/
theorem tensorGenerated_pair (a : U) (a' : U') :
    TensorGenerated (∑ j : Fin (finrank K W), tprod K
      ![vectorIn (U' := U') a (Module.finBasis K W j),
        dualIn (U := U) a' ((Module.finBasis K W).dualBasis j)]) := by
  apply tensorGenerated_of_order (Equiv.refl _)
  simp only [reindex_refl, LinearEquiv.refl_apply, map_sum, wedgeQuotient_tprod]
  have h := theta_eq_sum (K := K) (W := W) (Module.finBasis K W) a a'
  simp only [wedgePair_apply] at h
  rw [← h]
  exact Submodule.subset_span (GeneratorProduct.theta a a')

/-- Attach independent multiplicity vectors and place vector slots before dual slots. -/
private def attachMixed {I J : Type*} (a : I → U) (b : J → U') :
    MixedTensor K W I J →ₗ[K] (⨂[K] _ : I ⊕ J, Space K W U U') :=
  (tmulEquiv K (Space K W U U')).toLinearMap.comp
    (TensorProduct.map (PiTensorProduct.map (fun i => vectorIn (a i)))
      (PiTensorProduct.map (fun j => dualIn (b j))))

@[simp] theorem attachMixed_tprod {I J : Type*} (a : I → U) (b : J → U')
    (v : I → W) (w : J → Module.Dual K W) :
    attachMixed a b (tprod K v ⊗ₜ[K] tprod K w) =
      tprod K (Sum.elim (fun i => vectorIn (a i) (v i)) (fun j => dualIn (b j) (w j))) := by
  simp [attachMixed, tmulEquiv_apply]

/-- Multiplicities move with their slots when mixed tensors are relabelled. -/
theorem attachMixed_reindex {I J I' J' : Type*}
    [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
    [DecidableEq I] [DecidableEq J] [DecidableEq I'] [DecidableEq J']
    (e : I ≃ I') (d : J ≃ J') (a : I' → U) (b : J' → U') (t : MixedTensor K W I J) :
    attachMixed a b (mixedReindex e d t) =
      PiTensorProduct.reindex K (fun _ => Space K W U U') (Equiv.sumCongr e d)
        (attachMixed (a ∘ e) (b ∘ d) t) := by
  suffices h : (attachMixed a b).comp (mixedReindex e d).toLinearMap =
      (PiTensorProduct.reindex K (fun _ => Space K W U U') (Equiv.sumCongr e d)).toLinearMap.comp
        (attachMixed (a ∘ e) (b ∘ d)) from LinearMap.congr_fun h t
  apply tensorMap_ext_tprod
  intro v w
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, mixedReindex,
    TensorProduct.congr_tmul, reindex_tprod, attachMixed_tprod]
  congr 1
  funext i
  cases i <;> simp [Function.comp_def]

/-- A dual-slot permutation can be moved to the output, with multiplicities pulled back. -/
theorem attachMixed_permDual {I J : Type*} (τ : Equiv.Perm J)
    (a : I → U) (b : J → U') (t : MixedTensor K W I J) :
    attachMixed a b ((permRep K (Module.Dual K W) J τ).lTensor _ t) =
      PiTensorProduct.reindex K (fun _ => Space K W U U') (Equiv.sumCongr (Equiv.refl I) τ)
        (attachMixed a (b ∘ τ) t) := by
  suffices h : (attachMixed a b).comp ((permRep K (Module.Dual K W) J τ).lTensor _) =
      (PiTensorProduct.reindex K (fun _ => Space K W U U') (Equiv.sumCongr (Equiv.refl I) τ)).toLinearMap.comp
        (attachMixed a (b ∘ τ)) from LinearMap.congr_fun h t
  apply tensorMap_ext_tprod
  intro v w
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.lTensor_tmul,
    permRep_tprod, attachMixed_tprod, reindex_tprod]
  congr 1
  funext i
  cases i <;> simp [Function.comp_def]

/-- The vector-slot version of the permutation compatibility. -/
theorem attachMixed_permVec {I J : Type*} (τ : Equiv.Perm I)
    (a : I → U) (b : J → U') (t : MixedTensor K W I J) :
    attachMixed a b ((permRep K W I τ).rTensor _ t) =
      PiTensorProduct.reindex K (fun _ => Space K W U U') (Equiv.sumCongr τ (Equiv.refl J))
        (attachMixed (a ∘ τ) b t) := by
  suffices h : (attachMixed a b).comp ((permRep K W I τ).rTensor _) =
      (PiTensorProduct.reindex K (fun _ => Space K W U U') (Equiv.sumCongr τ (Equiv.refl J))).toLinearMap.comp
        (attachMixed (a ∘ τ) b) from LinearMap.congr_fun h t
  apply tensorMap_ext_tprod
  intro v w
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul,
    permRep_tprod, attachMixed_tprod, reindex_tprod]
  congr 1
  funext i
  cases i <;> simp [Function.comp_def]

/-- Sort interleaved pairs into vector slots followed by dual slots. -/
private def pairSlots (I : Type*) : I × Fin 2 ≃ I ⊕ I where
  toFun p := if p.2 = 0 then .inl p.1 else .inr p.1
  invFun := Sum.elim (fun i => (i, 0)) (fun i => (i, 1))
  left_inv p := by rcases p with ⟨i,j⟩; fin_cases j <;> simp
  right_inv p := by cases p <;> simp

/-- Independent sums of local pairs on any finite index type. -/
theorem tensorGenerated_pairSums_fintype {I B : Type*} [Fintype I] [DecidableEq I] [Fintype B]
    (v : I → B → Fin 2 → Space K W U U')
    (hv : ∀ i, TensorGenerated (∑ b, tprod K (v i b))) :
    TensorGenerated (∑ f : I → B, tprod K (fun p : I × Fin 2 => v p.1 (f p.1) p.2)) := by
  let e := (Fintype.equivFin I).symm
  have h := (tensorGenerated_pairSums (Fintype.card I) (fun i => v (e i))
    (fun i => hv (e i))).reindex (Equiv.prodCongr e (Equiv.refl (Fin 2)))
  have he : (∑ f : I → B, tprod K (fun p : I × Fin 2 => v p.1 (f p.1) p.2)) =
      PiTensorProduct.reindex K (fun _ => Space K W U U') (Equiv.prodCongr e (Equiv.refl (Fin 2)))
        (∑ f : Fin (Fintype.card I) → B,
          tprod K (fun p : Fin (Fintype.card I) × Fin 2 => v (e p.1) (f p.1) p.2)) := by
    rw [← (Equiv.arrowCongr e (Equiv.refl B)).sum_comp]
    simp only [map_sum, reindex_tprod]
    apply Finset.sum_congr rfl
    intro f _
    congr 1
    funext p
    simp [Function.comp_def]
  rw [he]
  exact h

/-- The exterior image of any number of identity contraction pairs is generated. -/
theorem tensorGenerated_contraction {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → U) (b : I → U') :
    TensorGenerated (attachMixed a b (contraction K W I 1)) := by
  rw [contraction_eq_sum (Module.finBasis K W)]
  simp only [map_sum, attachMixed_tprod, Equiv.Perm.one_def, Equiv.refl_symm,
    Equiv.refl_apply]
  have h := (tensorGenerated_pairSums_fintype
    (fun i j => ![vectorIn (U' := U') (a i) (Module.finBasis K W j),
      dualIn (U := U) (b i) ((Module.finBasis K W).dualBasis j)])
    (fun i => tensorGenerated_pair (a i) (b i))).reindex (pairSlots I)
  convert h using 1
  simp only [map_sum, reindex_tprod]
  apply Finset.sum_congr rfl
  intro f _
  congr 1
  funext i
  cases i <;> simp [pairSlots, Basis.coe_dualBasis]

/-- Associativity of concatenation, expressed as a slot relabelling. -/
theorem tmulEquiv_assoc_slots {I J L A : Type*} [AddCommGroup A] [Module K A]
    (s : ⨂[K] _ : I, A) (t : ⨂[K] _ : J, A) (u : ⨂[K] _ : L, A) :
    PiTensorProduct.reindex K (fun _ => A) (Equiv.sumAssoc I J L)
      (tmulEquiv K A (tmulEquiv K A (s ⊗ₜ[K] t) ⊗ₜ[K] u)) =
      tmulEquiv K A (s ⊗ₜ[K] tmulEquiv K A (t ⊗ₜ[K] u)) := by
  have h : (PiTensorProduct.reindex K (fun _ => A) (Equiv.sumAssoc I J L)).toLinearMap.comp
      ((tmulEquiv K A).toLinearMap.comp ((tmulEquiv K A).toLinearMap.rTensor _)) =
      (tmulEquiv K A).toLinearMap.comp
        (((tmulEquiv K A).toLinearMap.lTensor _).comp
          (TensorProduct.assoc K _ _ _).toLinearMap) := by
    apply tensorMap_ext_three_tprod
    intro v w z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul,
      LinearMap.lTensor_tmul, TensorProduct.assoc_tmul, tmulEquiv_apply, reindex_tprod]
    congr 1
    funext i
    rcases i with i | (j | l) <;> rfl
  exact LinearMap.congr_fun h ((s ⊗ₜ[K] t) ⊗ₜ[K] u)

/-- Append a dual block after the paired slots. -/
theorem attachMixed_extendDual {I J L : Type*} (a : I → U) (b : J ⊕ L → U')
    (t : MixedTensor K W I J) (D : ⨂[K] _ : L, Module.Dual K W) :
    attachMixed a b (extendDual D t) =
      PiTensorProduct.reindex K (fun _ => Space K W U U') (Equiv.sumAssoc I J L)
        (tmulEquiv K (Space K W U U')
          (attachMixed a (fun j => b (.inl j)) t ⊗ₜ[K]
            PiTensorProduct.map (fun l => dualIn (b (.inr l))) D)) := by
  induction t using TensorProduct.inductionOn with
  | tmul s t =>
    simp only [extendDual_tmul, attachMixed, LinearMap.comp_apply, TensorProduct.map_tmul,
      LinearEquiv.coe_coe, map_tmulEquiv, tmulEquiv_assoc_slots]
  | add s t hs ht => simp only [map_add, TensorProduct.add_tmul, hs, ht]

/-- Slot sorting after appending a vector block. -/
private def vectorBlockSlots (I J L : Type*) : (I ⊕ J) ⊕ L ≃ (I ⊕ L) ⊕ J :=
  (Equiv.sumAssoc I J L).trans
    ((Equiv.sumCongr (Equiv.refl I) (Equiv.sumComm J L)).trans (Equiv.sumAssoc I L J).symm)

/-- The vector-block regrouping moves the appended block past the dual slots. -/
theorem attachMixed_extendVec {I J L : Type*} (a : I ⊕ L → U) (b : J → U')
    (t : MixedTensor K W I J) (D : ⨂[K] _ : L, W) :
    attachMixed a b (extendVec D t) =
      PiTensorProduct.reindex K (fun _ => Space K W U U') (vectorBlockSlots I J L)
        (tmulEquiv K (Space K W U U')
          (attachMixed (fun i => a (.inl i)) b t ⊗ₜ[K]
            PiTensorProduct.map (fun l => vectorIn (a (.inr l))) D)) := by
  suffices h : (attachMixed a b).comp (extendVec D) =
      (PiTensorProduct.reindex K (fun _ => Space K W U U') (vectorBlockSlots I J L)).toLinearMap.comp
        ((tmulEquiv K (Space K W U U')).toLinearMap.comp
          (((TensorProduct.mk K _ _).flip
            (PiTensorProduct.map (fun l => vectorIn (a (.inr l))) D)).comp
              (attachMixed (fun i => a (.inl i)) b))) from LinearMap.congr_fun h t
  apply tensorMap_ext_tprod
  intro v w
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.flip_apply, TensorProduct.mk_apply]
  induction D using PiTensorProduct.induction_on with
  | smul_tprod c z =>
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, extendVec_tmul,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul, map_smul, tmulEquiv_apply,
      attachMixed_tprod, map_tprod, LinearMap.flip_apply, TensorProduct.mk_apply, reindex_tprod]
    congr 2
    funext i
    rcases i with (i | l) | j <;> rfl
  | add x y hx hy =>
    simp_all only [extendVec, attachMixed, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.rTensor_tmul,
      LinearMap.flip_apply, TensorProduct.mk_apply, TensorProduct.tmul_add, TensorProduct.add_tmul,
      TensorProduct.map_tmul, map_add, LinearEquiv.coe_coe]

/-- Contractions followed by any number of dual determinant blocks are generated. -/
theorem tensorGenerated_extendDual {I : Type*} [Fintype I] [DecidableEq I]
    (m : ℕ) (a : I → U) (b : I ⊕ Blocks (finrank K W) m → U') :
    TensorGenerated (attachMixed a b
      (extendDual (detPow K W m) (contraction K W I 1))) := by
  rw [attachMixed_extendDual]
  exact ((tensorGenerated_contraction a (fun i => b (.inl i))).tmul
    (tensorGenerated_detPow m (fun i => b (.inr i)))).reindex _

/-- Contractions followed by any number of vector determinant blocks are generated. -/
theorem tensorGenerated_extendVec {I : Type*} [Fintype I] [DecidableEq I]
    (m : ℕ) (a : I ⊕ Blocks (finrank K W) m → U) (b : I → U') :
    TensorGenerated (attachMixed a b
      (extendVec (detPowDual K W m) (contraction K W I 1))) := by
  rw [attachMixed_extendVec]
  exact ((tensorGenerated_contraction (fun i => a (.inl i)) b).tmul
    (tensorGenerated_detPowDual m (fun i => a (.inr i)))).reindex _

/-- Generated tensor images form a submodule before taking the exterior quotient. -/
private def tensorGeneratedSubmodule (I : Type*) : Submodule K (⨂[K] _ : I, Space K W U U') where
  carrier := {t | TensorGenerated t}
  zero_mem' := by intro k e; simp only [map_zero]; exact Submodule.zero_mem _
  add_mem' := by
    intro s t hs ht k e
    simp only [map_add]
    exact Submodule.add_mem _ (hs k e) (ht k e)
  smul_mem' := by
    intro c t ht k e
    simp only [map_smul]
    exact Submodule.smul_mem _ c (ht k e)

/-- T8(a)'s transported dual-block spanning family has generated exterior images. -/
theorem tensorGenerated_invariant_dualBlocks {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (m : ℕ) (d : (I ⊕ Blocks (finrank K W) m) ≃ J)
    (a : I → U) (b : J → U') (t : MixedTensor K W I J)
    (ht : t ∈ LieModule.maxTrivSubmodule K (slEnd K W) (MixedTensor K W I J)) :
    TensorGenerated (attachMixed a b t) := by
  change t ∈ (LieModule.maxTrivSubmodule K (slEnd K W) (MixedTensor K W I J) : Submodule K _) at ht
  rw [invariants_eq_span_detPow_reindex m d] at ht
  apply (show Submodule.span K _ ≤
      (tensorGeneratedSubmodule (K := K) (W := W) (U := U) (U' := U') (I ⊕ J)).comap
        (attachMixed a b) from ?_) ht
  rw [Submodule.span_le]
  rintro _ ⟨τ, rfl⟩
  change TensorGenerated _
  rw [attachMixed_reindex, attachMixed_permDual]
  exact ((tensorGenerated_extendDual m _ _).reindex _).reindex _

/-- T8(a)'s transported vector-block spanning family has generated exterior images. -/
theorem tensorGenerated_invariant_vecBlocks {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (m : ℕ) (e : (J ⊕ Blocks (finrank K W) m) ≃ I)
    (a : I → U) (b : J → U') (t : MixedTensor K W I J)
    (ht : t ∈ LieModule.maxTrivSubmodule K (slEnd K W) (MixedTensor K W I J)) :
    TensorGenerated (attachMixed a b t) := by
  change t ∈ (LieModule.maxTrivSubmodule K (slEnd K W) (MixedTensor K W I J) : Submodule K _) at ht
  rw [invariants_eq_span_detPowDual_reindex m e] at ht
  apply (show Submodule.span K _ ≤
      (tensorGeneratedSubmodule (K := K) (W := W) (U := U) (U' := U') (I ⊕ J)).comap
        (attachMixed a b) from ?_) ht
  rw [Submodule.span_le]
  rintro _ ⟨τ, rfl⟩
  change TensorGenerated _
  rw [attachMixed_reindex, attachMixed_permVec]
  exact ((tensorGenerated_extendVec m _ _).reindex _).reindex _

/-- The general block-image calculation, including all cardinalities and zero-dimensional W. -/
theorem tensorGenerated_invariant {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (a : I → U) (b : J → U') (t : MixedTensor K W I J)
    (ht : t ∈ LieModule.maxTrivSubmodule K (slEnd K W) (MixedTensor K W I J)) :
    TensorGenerated (attachMixed a b t) := by
  by_cases hd : (finrank K W : ℤ) ∣ (Fintype.card J : ℤ) - Fintype.card I
  · obtain ⟨m, hm⟩ := hd
    cases m with
    | ofNat m =>
      change (Fintype.card J : ℤ) - Fintype.card I = (finrank K W : ℤ) * (m : ℤ) at hm
      have hc : Fintype.card J = Fintype.card I + m * finrank K W := by
        have hc' : (Fintype.card J : ℤ) = Fintype.card I + (m * finrank K W : ℕ) := by
          push_cast
          nlinarith [hm]
        exact_mod_cast hc'
      exact tensorGenerated_invariant_dualBlocks m (blockSlotEquiv m hc) a b t ht
    | negSucc m =>
      have hc : Fintype.card I = Fintype.card J + (m + 1) * finrank K W := by
        have hc' : (Fintype.card I : ℤ) = Fintype.card J + ((m + 1) * finrank K W : ℕ) := by
          push_cast
          simp only [Int.negSucc_eq] at hm
          nlinarith [hm]
        exact_mod_cast hc'
      exact tensorGenerated_invariant_vecBlocks (m + 1) (blockSlotEquiv (m + 1) hc) a b t ht
  · have hz := maxTriv_slEnd_eq_bot (K := K) (W := W) (ι := I) (κ := J) hd
    rw [hz] at ht
    have : t = 0 := ht
    subst t
    rw [map_zero]
    exact (tensorGeneratedSubmodule _).zero_mem

variable [FiniteDimensional K U] [FiniteDimensional K U']

/-- On pure multiplicities, the colored-word embedding is precisely attachment and sorting. -/
theorem coloredMultiplicityIn_pure {k : ℕ} (s : Finset (Fin k))
    (a : {i // i ∈ s} → U) (b : {i // i ∉ s} → U')
    (t : MixedTensor K W {i // i ∈ s} {i // i ∉ s}) :
    coloredMultiplicityIn s (t ⊗ₜ[K] (tprod K a ⊗ₜ[K] tprod K b)) =
      PiTensorProduct.reindex K (fun _ => Space K W U U') (Equiv.sumCompl (· ∈ s)) (attachMixed a b t) := by
  suffices h : (coloredMultiplicityIn s).comp
      ((TensorProduct.mk K _ _).flip (tprod K a ⊗ₜ[K] tprod K b)) =
      (PiTensorProduct.reindex K (fun _ => Space K W U U') (Equiv.sumCompl (· ∈ s))).toLinearMap.comp
        (attachMixed a b) from LinearMap.congr_fun h t
  apply tensorMap_ext_tprod
  intro v w
  simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply, coloredMultiplicityIn,
    mixedMultiplicityEquiv, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    TensorProduct.tensorTensorTensorComm_tmul, TensorProduct.congr_tmul,
    tensorMultiplicityEquiv_tprod, coloredWordIn, orderedWordIn,
    TensorProduct.map_tmul, map_tprod, tmulEquiv_apply, attachMixed_tprod]
  rfl

/-- Independent multiplicities on every T8(a) invariant have generated exterior images. -/
theorem colored_invariant_image_mem {k : ℕ} (s : Finset (Fin k))
    (t : MixedTensor K W {i // i ∈ s} {i // i ∉ s})
    (ht : t ∈ LieModule.maxTrivSubmodule K (slEnd K W)
      (MixedTensor K W {i // i ∈ s} {i // i ∉ s}))
    (c : (⨂[K] _ : {i // i ∈ s}, U) ⊗[K] (⨂[K] _ : {i // i ∉ s}, U')) :
    wedgeQuotient k (coloredMultiplicityIn s (t ⊗ₜ[K] c)) ∈ generatedDegree k := by
  induction c using TensorProduct.inductionOn with
  | tmul a b =>
    induction a using PiTensorProduct.induction_on with
    | smul_tprod r a =>
      induction b using PiTensorProduct.induction_on with
      | smul_tprod q b =>
        simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul]
        apply Submodule.smul_mem
        apply Submodule.smul_mem
        rw [coloredMultiplicityIn_pure]
        exact tensorGenerated_invariant a b t ht k (Equiv.sumCompl (· ∈ s))
      | add x y hx hy =>
        simp only [TensorProduct.tmul_add, map_add]
        exact Submodule.add_mem _ hx hy
    | add x y hx hy =>
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add]
      exact Submodule.add_mem _ hx hy
  | add x y hx hy =>
    simp only [TensorProduct.tmul_add, map_add]
    exact Submodule.add_mem _ hx hy

/-- All exterior invariants are generated by θ and vector and dual determinant classes,
for arbitrary separate finite multiplicity spaces. The SL(W) group form is not asserted.
This is part (1) of F-1575 (the invariant-theory lemma), in `sl(W)` Lie form over a field
of characteristic 0; it does not check F-1575 itself.
Source: F-1575 (1), via the tensor first fundamental theorem and polarization. -/
theorem invariants_eq_generatedDegree (k : ℕ) :
    (LieModule.maxTrivSubmodule K (slEnd K W) (⋀[K]^k (Space K W U U')) : Submodule K _) =
      generatedDegree (K := K) (W := W) (U := U) (U' := U') k := by
  apply le_antisymm
  · exact invariants_le_generatedDegree_of_colored_images k
      (fun s t ht c => colored_invariant_image_mem s t ht c)
  · exact generatedDegree_le_invariants k

end HodgeLean.Foundations.InvariantsExterior
