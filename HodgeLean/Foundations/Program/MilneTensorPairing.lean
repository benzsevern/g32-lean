import HodgeLean.Foundations.Program.MilneTensorTransport

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def m1b_tensorBilin (B : LinearMap.BilinForm ℂ V) (n : ℕ) :
    LinearMap.BilinForm ℂ (⨂[ℂ]^n V) :=
  PiTensorProduct.dualDistrib.comp (PiTensorProduct.map (fun _ : Fin n => B))

theorem m1b_tensorBilin_tprod (B : LinearMap.BilinForm ℂ V) (n : ℕ)
    (v w : Fin n → V) :
    m1b_tensorBilin B n (⨂ₜ[ℂ] i, v i) (⨂ₜ[ℂ] i, w i) = ∏ i, B (v i) (w i) := by
  simp only [m1b_tensorBilin, LinearMap.comp_apply, PiTensorProduct.map_tprod,
    PiTensorProduct.dualDistrib_apply]

theorem m1b_tensorBilin_isometry (B : LinearMap.BilinForm ℂ V) (n : ℕ)
    (u : Module.End ℂ V) (hu : u ∈ m1b_isometries B) (t s : ⨂[ℂ]^n V) :
    m1b_tensorBilin B n (SchurWeyl.tensorPow (Fin n) u t)
      (SchurWeyl.tensorPow (Fin n) u s) = m1b_tensorBilin B n t s := by
  have h : (m1b_tensorBilin B n).compl₁₂
      (SchurWeyl.tensorPow (Fin n) u) (SchurWeyl.tensorPow (Fin n) u) =
      m1b_tensorBilin B n := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro w
    change m1b_tensorBilin B n (SchurWeyl.tensorPow (Fin n) u (⨂ₜ[ℂ] i, v i))
      (SchurWeyl.tensorPow (Fin n) u (⨂ₜ[ℂ] i, w i)) =
      m1b_tensorBilin B n (⨂ₜ[ℂ] i, v i) (⨂ₜ[ℂ] i, w i)
    simp only [SchurWeyl.tensorPow_tprod,
      m1b_tensorBilin_tprod, hu.2]
  exact LinearMap.congr_fun (LinearMap.congr_fun h t) s

def m1b_tensorFunction (B : LinearMap.BilinForm ℂ V) (n : ℕ) :
    (⨂[ℂ]^n V) →ₗ[ℂ] MultilinearMap ℂ (fun _ : Fin n => V) ℂ :=
  PiTensorProduct.lift.symm.toLinearMap.comp (m1b_tensorBilin B n)

theorem m1b_tensorFunction_apply (B : LinearMap.BilinForm ℂ V) (n : ℕ)
    (t : ⨂[ℂ]^n V) (v : Fin n → V) :
    m1b_tensorFunction B n t v = m1b_tensorBilin B n t (⨂ₜ[ℂ] i, v i) := rfl

theorem m1b_tensorFunction_fixed (B : LinearMap.BilinForm ℂ V) (n : ℕ)
    (S : Set (Module.End ℂ V)) (hS : S ⊆ m1b_isometries B)
    (t : ⨂[ℂ]^n V) (ht : t ∈ m1b_fixed S n) (u : Module.End ℂ V) (hu : u ∈ S)
    (v : Fin n → V) :
    m1b_tensorFunction B n t (fun i => u (v i)) = m1b_tensorFunction B n t v := by
  have ht' : SchurWeyl.tensorPow (Fin n) u t = t := by
    simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at ht
    exact ht u hu
  have h := m1b_tensorBilin_isometry B n u (hS hu) t (⨂ₜ[ℂ] i, v i)
  rw [ht', SchurWeyl.tensorPow_tprod] at h
  exact h

theorem m1b_tensorFunction_injective [FiniteDimensional ℂ V]
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate) (n : ℕ) :
    Function.Injective (m1b_tensorFunction B n) := by
  let e : V ≃ₗ[ℂ] Module.Dual ℂ V := LinearEquiv.ofInjectiveOfFinrankEq B
    (LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp hB.1)) (by simp)
  let E : (⨂[ℂ]^n V) ≃ₗ[ℂ] Module.Dual ℂ (⨂[ℂ]^n V) :=
    (PiTensorProduct.congr (fun _ : Fin n => e)).trans PiTensorProduct.dualDistribEquiv
  exact PiTensorProduct.lift.symm.injective.comp E.injective

def m1b_copiesBilin (B : LinearMap.BilinForm ℂ V) (r : ℕ) :
    LinearMap.BilinForm ℂ (Fin r → V) :=
  ∑ i, B.compl₁₂ (LinearMap.proj i) (LinearMap.proj i)

theorem m1b_copiesBilin_apply (B : LinearMap.BilinForm ℂ V) (r : ℕ)
    (x y : Fin r → V) : m1b_copiesBilin B r x y = ∑ i, B (x i) (y i) := by
  simp only [m1b_copiesBilin, LinearMap.sum_apply, LinearMap.compl₁₂_apply,
    LinearMap.proj_apply]

theorem m1b_copiesBilin_single_right (B : LinearMap.BilinForm ℂ V) (r : ℕ)
    (x : Fin r → V) (i : Fin r) (y : V) :
    m1b_copiesBilin B r x (Pi.single i y) = B (x i) y := by
  classical
  rw [m1b_copiesBilin_apply]
  simp [Pi.single_apply, apply_ite]

theorem m1b_copiesBilin_single_left (B : LinearMap.BilinForm ℂ V) (r : ℕ)
    (x : V) (i : Fin r) (y : Fin r → V) :
    m1b_copiesBilin B r (Pi.single i x) y = B x (y i) := by
  classical
  rw [m1b_copiesBilin_apply]
  simp [Pi.single_apply, apply_ite, ite_apply]

theorem m1b_copiesBilin_nondegenerate (B : LinearMap.BilinForm ℂ V)
    (hB : B.Nondegenerate) (r : ℕ) : (m1b_copiesBilin B r).Nondegenerate := by
  constructor
  · intro x hx
    funext i
    apply hB.1
    intro y
    simpa only [m1b_copiesBilin_single_right] using hx (Pi.single i y)
  · intro y hy
    funext i
    apply hB.2
    intro x
    simpa only [m1b_copiesBilin_single_left] using hy (Pi.single i x)

theorem m1b_copies_isometry (B : LinearMap.BilinForm ℂ V) (r : ℕ)
    (u : Module.End ℂ V) (hu : u ∈ m1b_isometries B) :
    m1b_copies r u ∈ m1b_isometries (m1b_copiesBilin B r) := by
  refine ⟨?_, ?_⟩
  · let e : V ≃ₗ[ℂ] V := LinearEquiv.ofBijective u ((Module.End.isUnit_iff u).mp hu.1)
    exact (Module.End.isUnit_iff _).mpr (m1b_copiesEquiv e r).bijective
  · intro x y
    simp only [m1b_copiesBilin_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact hu.2 (x i) (y i)

theorem m1b_copies_tensorFunction_fixed (B : LinearMap.BilinForm ℂ V) (r n : ℕ)
    (t : ⨂[ℂ]^n (Fin r → V))
    (ht : t ∈ m1b_fixed (m1b_copies r '' m1b_isometries B) n)
    (u : Module.End ℂ V) (hu : u ∈ m1b_isometries B) (v : Fin n → Fin r → V) :
    m1b_tensorFunction (m1b_copiesBilin B r) n t (fun j => m1b_copies r u (v j)) =
      m1b_tensorFunction (m1b_copiesBilin B r) n t v := by
  have hS : m1b_copies r '' m1b_isometries B ⊆ m1b_isometries (m1b_copiesBilin B r) := by
    rintro w ⟨a, ha, rfl⟩
    exact m1b_copies_isometry B r a ha
  exact m1b_tensorFunction_fixed (V := Fin r → V) (m1b_copiesBilin B r) n
    (m1b_copies r '' m1b_isometries B) hS t ht (m1b_copies r u) ⟨u, hu, rfl⟩ v

theorem m1b_tensorFunction_bijective [FiniteDimensional ℂ V]
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate) (n : ℕ) :
    Function.Bijective (m1b_tensorFunction B n) := by
  let e : V ≃ₗ[ℂ] Module.Dual ℂ V := LinearEquiv.ofInjectiveOfFinrankEq B
    (LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp hB.1)) (by simp)
  let E : (⨂[ℂ]^n V) ≃ₗ[ℂ] Module.Dual ℂ (⨂[ℂ]^n V) :=
    (PiTensorProduct.congr (fun _ : Fin n => e)).trans PiTensorProduct.dualDistribEquiv
  exact (E.trans PiTensorProduct.lift.symm).bijective

theorem m1b_tensorFunction_fixed_iff [FiniteDimensional ℂ V]
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate) (n : ℕ)
    (S : Set (Module.End ℂ V)) (hS : S ⊆ m1b_isometries B) (t : ⨂[ℂ]^n V) :
    t ∈ m1b_fixed S n ↔ ∀ u ∈ S, ∀ v,
      m1b_tensorFunction B n t (fun i => u (v i)) = m1b_tensorFunction B n t v := by
  constructor
  · exact fun ht u hu v => m1b_tensorFunction_fixed B n S hS t ht u hu v
  · intro hf
    simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    intro u hu
    apply m1b_tensorFunction_injective B hB n
    apply MultilinearMap.ext
    intro v
    let e : V ≃ₗ[ℂ] V := LinearEquiv.ofBijective u
      ((Module.End.isUnit_iff u).mp (hS hu).1)
    let w := fun i : Fin n => e.symm (v i)
    have hv : (fun i => u (w i)) = v := by
      funext i
      exact e.apply_symm_apply (v i)
    have hp := m1b_tensorBilin_isometry B n u (hS hu) t (⨂ₜ[ℂ] i, w i)
    rw [SchurWeyl.tensorPow_tprod] at hp
    change m1b_tensorFunction B n (SchurWeyl.tensorPow (Fin n) u t)
      (fun i => u (w i)) = m1b_tensorFunction B n t w at hp
    rw [hv] at hp
    exact hp.trans ((hf u hu w).symm.trans (congrArg (m1b_tensorFunction B n t) hv))

end HodgeLean.Foundations.Program
