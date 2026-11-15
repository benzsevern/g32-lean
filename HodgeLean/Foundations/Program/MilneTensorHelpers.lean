import HodgeLean.Foundations.Program.MilneTensorDefs

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem m1b_fixed_zero (S : Set (Module.End ℂ V)) : m1b_fixed S 0 = ⊤ := by
  apply top_unique
  intro t _
  simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  intro u _
  have h : SchurWeyl.tensorPow (Fin 0) u = LinearMap.id := by
    ext v
    simp only [LinearMap.compMultilinearMap_apply, SchurWeyl.tensorPow_tprod,
      LinearMap.id_apply]
    congr 1
    funext i
    exact Fin.elim0 i
  rw [h, LinearMap.id_apply]

theorem m1b_fixed_odd (S : Set (Module.End ℂ V)) (hS : -1 ∈ S)
    (n : ℕ) (hn : Odd n) : m1b_fixed S n = ⊥ := by
  apply le_antisymm _ bot_le
  intro t ht
  have ht' : SchurWeyl.tensorPow (Fin n) (-1 : Module.End ℂ V) t = t := by
    simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at ht
    exact ht (-1) hS
  have hscalar : (-1 : Module.End ℂ V) = (-1 : ℂ) • 1 := by simp
  rw [hscalar, SchurWeyl.tensorPow_smul_one, Fintype.card_fin,
    hn.neg_one_pow] at ht'
  have hneg : -t = t := by simpa using ht'
  have htwo : (2 : ℂ) • t = 0 := by
    rw [two_smul]
    calc t + t = -t + t := congrArg (fun x => x + t) hneg.symm
         _ = 0 := neg_add_cancel t
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem m1b_copies_neg_one (r : ℕ) :
    m1b_copies (V := V) r (-1) = -1 := by
  ext x i
  rfl

theorem m1b_isometries_neg_one (B : LinearMap.BilinForm ℂ V) :
    -1 ∈ m1b_isometries B := by
  refine ⟨isUnit_one.neg, ?_⟩
  intro x y
  simp

theorem m1b_coloredWordOut_tensorPow {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset ι)
    (u : Module.End ℂ V) (v : Module.End ℂ W) (t : ⨂[ℂ] _ : ι, V × W) :
    InvariantsExterior.coloredWordOut s (SchurWeyl.tensorPow ι (u.prodMap v) t) =
      TensorProduct.map (SchurWeyl.tensorPow {i // i ∈ s} u)
        (SchurWeyl.tensorPow {i // i ∉ s} v)
        (InvariantsExterior.coloredWordOut s t) := by
  suffices h : (InvariantsExterior.coloredWordOut s).comp
      (SchurWeyl.tensorPow ι (u.prodMap v)) =
      (TensorProduct.map (SchurWeyl.tensorPow {i // i ∈ s} u)
        (SchurWeyl.tensorPow {i // i ∉ s} v)).comp
        (InvariantsExterior.coloredWordOut s) from LinearMap.congr_fun h t
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    SchurWeyl.tensorPow_tprod, InvariantsExterior.coloredWordOut,
    InvariantsExterior.orderedWordOut, LinearEquiv.coe_coe,
    PiTensorProduct.reindex_tprod, PiTensorProduct.tmulEquiv_symm_apply,
    TensorProduct.map_tmul, PiTensorProduct.map_tprod]
  rfl

theorem m1b_products_odd (Q : Submodule ℂ (⨂[ℂ]^2 V)) :
    ∀ n : ℕ, Odd n → m1b_products Q n = ⊥ := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => intro _; rfl
  | more n ih _ =>
    intro hn
    have hn' : Odd n := by
      obtain ⟨k, hk⟩ := hn
      exact ⟨k - 1, by omega⟩
    rw [m1b_products, ih hn']
    apply le_antisymm _ bot_le
    apply Submodule.span_le.mpr
    rintro t ⟨σ, a, b, ha, hb, rfl⟩
    rw [Submodule.mem_bot] at ha
    simp [ha]

theorem m1b_isometry_tensors_odd (B : LinearMap.BilinForm ℂ V) (r n : ℕ)
    (hn : Odd n) :
    m1b_fixed (m1b_copies r '' m1b_isometries B) n =
      m1b_products (m1b_fixed (m1b_copies r '' m1b_isometries B) 2) n := by
  rw [m1b_products_odd _ n hn]
  exact m1b_fixed_odd (m1b_copies r '' m1b_isometries B)
    ⟨-1, m1b_isometries_neg_one B, m1b_copies_neg_one r⟩ n hn

theorem m1b_tensorPow_append (u : Module.End ℂ V) (k l : ℕ)
    (a : ⨂[ℂ]^k V) (b : ⨂[ℂ]^l V) :
    SchurWeyl.tensorPow (Fin (k + l)) u
      (InvariantsExterior.tensorAppend k l (a ⊗ₜ[ℂ] b)) =
    InvariantsExterior.tensorAppend k l
      (SchurWeyl.tensorPow (Fin k) u a ⊗ₜ[ℂ] SchurWeyl.tensorPow (Fin l) u b) := by
  have h : (SchurWeyl.tensorPow (Fin (k + l)) u).comp
      (InvariantsExterior.tensorAppend k l).toLinearMap =
      (InvariantsExterior.tensorAppend k l).toLinearMap.comp
        (TensorProduct.map (SchurWeyl.tensorPow (Fin k) u)
          (SchurWeyl.tensorPow (Fin l) u)) := by
    ext x y
    change SchurWeyl.tensorPow (Fin (k + l)) u
      (InvariantsExterior.tensorAppend k l
        (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y)) =
      InvariantsExterior.tensorAppend k l
        (TensorProduct.map (SchurWeyl.tensorPow (Fin k) u)
          (SchurWeyl.tensorPow (Fin l) u)
          (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y))
    simp only [TensorProduct.map_tmul, SchurWeyl.tensorPow_tprod,
      InvariantsExterior.tensorAppend_tprod]
    congr 1
    funext i
    exact Fin.addCases (fun j => by simp) (fun j => by simp) i
  exact LinearMap.congr_fun h (a ⊗ₜ[ℂ] b)

theorem m1b_products_le_fixed (S : Set (Module.End ℂ V)) :
    ∀ n, m1b_products (m1b_fixed S 2) n ≤ m1b_fixed S n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => rw [m1b_fixed_zero]; exact le_top
  | one => exact bot_le
  | more n ih _ =>
    apply Submodule.span_le.mpr
    rintro t ⟨σ, a, b, ha, hb, rfl⟩
    change SchurWeyl.permRep ℂ V (Fin (n + 2)) σ
      (InvariantsExterior.tensorAppend n 2 (a ⊗ₜ[ℂ] b)) ∈ m1b_fixed S (n + 2)
    have hfa := ih ha
    simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hfa hb ⊢
    intro u hu
    have hc := LinearMap.congr_fun (SchurWeyl.permRep_mul_tensorPow σ u)
      (InvariantsExterior.tensorAppend n 2 (a ⊗ₜ[ℂ] b))
    change _ = SchurWeyl.tensorPow (Fin (n + 2)) u
      (SchurWeyl.permRep ℂ V (Fin (n + 2)) σ
        (InvariantsExterior.tensorAppend n 2 (a ⊗ₜ[ℂ] b))) at hc
    rw [← hc]
    change SchurWeyl.permRep ℂ V (Fin (n + 2)) σ
      (SchurWeyl.tensorPow (Fin (n + 2)) u
        (InvariantsExterior.tensorAppend n 2 (a ⊗ₜ[ℂ] b))) = _
    rw [m1b_tensorPow_append, hfa u hu, hb u hu]

end HodgeLean.Foundations.Program
