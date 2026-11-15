import HodgeLean.Foundations.Program.MilneTensorDefs
import Mathlib.RingTheory.SimpleModule.IsAlgClosed

noncomputable section
namespace HodgeLean.Foundations.Program

variable {s : ℕ} (d : Fin s → ℕ)

def m1b_blockUnit (i : Fin s) (a b : Fin (d i)) :
    (j : Fin s) → Matrix (Fin (d j)) (Fin (d j)) ℂ :=
  Pi.single i (Matrix.single a b 1)

theorem m1b_blockUnit_mul (i : Fin s) (a b c : Fin (d i)) :
    m1b_blockUnit d i a b * m1b_blockUnit d i b c = m1b_blockUnit d i a c := by
  ext j
  by_cases h : j = i
  · subst j
    simp [m1b_blockUnit, Matrix.single_mul_single_same]
  · simp [m1b_blockUnit, Pi.single_eq_of_ne h]

theorem m1b_blockUnit_mul_ne (i j : Fin s) (h : i ≠ j)
    (a b : Fin (d i)) (c e : Fin (d j)) :
    m1b_blockUnit d i a b * m1b_blockUnit d j c e = 0 := by
  ext k
  by_cases hi : k = i
  · subst k
    simp [m1b_blockUnit, Pi.single_eq_of_ne h]
  · simp [m1b_blockUnit, Pi.single_eq_of_ne hi]

theorem m1b_blockUnit_mul_column_ne (i : Fin s) (a b c e : Fin (d i))
    (h : b ≠ c) : m1b_blockUnit d i a b * m1b_blockUnit d i c e = 0 := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [m1b_blockUnit, Matrix.single_mul_single_of_ne, h]
  · simp [m1b_blockUnit, Pi.single_eq_of_ne hj]

theorem m1b_sum_blockUnit_diag :
    (∑ i, ∑ a : Fin (d i), m1b_blockUnit d i a a) = 1 := by
  ext i
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp [m1b_blockUnit, Matrix.sum_single_one]
  · intro j _ hj
    simp [m1b_blockUnit, Pi.single_eq_of_ne (Ne.symm hj)]
  · simp

theorem m1b_blockUnit_mul_matrix (i : Fin s) (a b : Fin (d i))
    (M : (j : Fin s) → Matrix (Fin (d j)) (Fin (d j)) ℂ) :
    m1b_blockUnit d i a b * M = ∑ c, M i b c • m1b_blockUnit d i a c := by
  ext j x y
  by_cases hj : j = i
  · subst j
    by_cases hx : a = x
    · subst x
      simp [m1b_blockUnit, Matrix.mul_apply, Matrix.single, Matrix.of_apply,
        Matrix.sum_apply, Matrix.smul_apply]
    · simp [m1b_blockUnit, Matrix.mul_apply, Matrix.single, Matrix.of_apply,
        Matrix.sum_apply, Matrix.smul_apply, hx]
  · simp [m1b_blockUnit, Pi.single_eq_of_ne hj]

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : ((i : Fin s) → Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] Module.End ℂ V)
    (z : (i : Fin s) → Fin (d i))

def m1b_matrixMultiplicity (i : Fin s) : Submodule ℂ V :=
  LinearMap.range (ρ (m1b_blockUnit d i (z i) (z i)))

def m1b_matrixExtract : V →ₗ[ℂ]
    ((i : Fin s) → Fin (d i) → m1b_matrixMultiplicity d ρ z i) :=
  LinearMap.pi fun i => LinearMap.pi fun a =>
    (ρ (m1b_blockUnit d i (z i) a)).codRestrict (m1b_matrixMultiplicity d ρ z i)
      (fun v => ⟨ρ (m1b_blockUnit d i (z i) a) v, by
        change ρ (m1b_blockUnit d i (z i) (z i))
          (ρ (m1b_blockUnit d i (z i) a) v) = _
        rw [← Module.End.mul_apply, ← map_mul, m1b_blockUnit_mul]⟩)

def m1b_matrixReconstruct :
    ((i : Fin s) → Fin (d i) → m1b_matrixMultiplicity d ρ z i) →ₗ[ℂ] V where
  toFun x := ∑ i, ∑ a, ρ (m1b_blockUnit d i a (z i)) (x i a)
  map_add' x y := by
    simp only [Pi.add_apply, Submodule.coe_add, map_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, Submodule.coe_smul, map_smul, Finset.smul_sum,
      RingHom.id_apply]

theorem m1b_reconstruct_extract (v : V) :
    m1b_matrixReconstruct d ρ z (m1b_matrixExtract d ρ z v) = v := by
  change (∑ i, ∑ a, ρ (m1b_blockUnit d i a (z i))
    (ρ (m1b_blockUnit d i (z i) a) v)) = v
  simp_rw [← Module.End.mul_apply, ← map_mul, m1b_blockUnit_mul]
  calc (∑ i, ∑ a, ρ (m1b_blockUnit d i a a) v) =
      ρ (∑ i, ∑ a, m1b_blockUnit d i a a) v := by
        simp only [map_sum, LinearMap.sum_apply]
    _ = v := by rw [m1b_sum_blockUnit_diag, map_one, Module.End.one_apply]

theorem m1b_matrixMultiplicity_project (i : Fin s)
    (x : m1b_matrixMultiplicity d ρ z i) :
    ρ (m1b_blockUnit d i (z i) (z i)) x = (x : V) := by
  obtain ⟨x, v, rfl⟩ := x
  rw [← Module.End.mul_apply, ← map_mul, m1b_blockUnit_mul]

theorem m1b_extract_reconstruct
    (x : (i : Fin s) → Fin (d i) → m1b_matrixMultiplicity d ρ z i) :
    m1b_matrixExtract d ρ z (m1b_matrixReconstruct d ρ z x) = x := by
  funext i a
  apply Subtype.ext
  change ρ (m1b_blockUnit d i (z i) a)
    (∑ j, ∑ b, ρ (m1b_blockUnit d j b (z j)) (x j b)) = (x i a : V)
  simp only [map_sum]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single a]
    · rw [← Module.End.mul_apply, ← map_mul, m1b_blockUnit_mul]
      exact m1b_matrixMultiplicity_project d ρ z i (x i a)
    · intro b _ hb
      rw [← Module.End.mul_apply, ← map_mul,
        m1b_blockUnit_mul_column_ne d i (z i) a b (z i) (Ne.symm hb),
        map_zero, LinearMap.zero_apply]
    · simp
  · intro j _ hj
    apply Finset.sum_eq_zero
    intro b _
    rw [← Module.End.mul_apply, ← map_mul,
      m1b_blockUnit_mul_ne d i j (Ne.symm hj), map_zero, LinearMap.zero_apply]
  · simp

def m1b_matrixCoordinates : V ≃ₗ[ℂ]
    ((i : Fin s) → Fin (d i) → m1b_matrixMultiplicity d ρ z i) where
  toLinearMap := m1b_matrixExtract d ρ z
  invFun := m1b_matrixReconstruct d ρ z
  left_inv := m1b_reconstruct_extract d ρ z
  right_inv := m1b_extract_reconstruct d ρ z

theorem m1b_matrixCoordinates_action
    (M : (i : Fin s) → Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (v : V) (i : Fin s) (a : Fin (d i)) :
    m1b_matrixCoordinates d ρ z (ρ M v) i a =
      ∑ b, M i a b • m1b_matrixCoordinates d ρ z v i b := by
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  change ρ (m1b_blockUnit d i (z i) a) (ρ M v) =
    ∑ b, M i a b • ρ (m1b_blockUnit d i (z i) b) v
  rw [← Module.End.mul_apply, ← map_mul, m1b_blockUnit_mul_matrix]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]

theorem m1b_matrixMultiplicity_pos [FiniteDimensional ℂ V]
    (hρ : Function.Injective ρ) (i : Fin s) :
    0 < Module.finrank ℂ (m1b_matrixMultiplicity d ρ z i) := by
  have hu : m1b_blockUnit d i (z i) (z i) ≠ 0 := by
    intro h
    have hh := congrArg (fun M => M i (z i) (z i)) h
    simpa [m1b_blockUnit, Matrix.single] using hh
  have hp : ρ (m1b_blockUnit d i (z i) (z i)) ≠ 0 := by
    intro h
    apply hu
    apply hρ
    simpa only [map_zero] using h
  have hr : m1b_matrixMultiplicity d ρ z i ≠ ⊥ := by
    change LinearMap.range _ ≠ ⊥
    intro h
    exact hp (LinearMap.range_eq_bot.mp h)
  haveI := Submodule.nontrivial_iff_ne_bot.mpr hr
  exact Module.finrank_pos

def m1b_matrixScalarCoordinates [FiniteDimensional ℂ V] :
    V ≃ₗ[ℂ] ((i : Fin s) → Fin (Module.finrank ℂ (m1b_matrixMultiplicity d ρ z i)) →
      Fin (d i) → ℂ) :=
  let b i := (Module.finBasis ℂ (m1b_matrixMultiplicity d ρ z i)).equivFun
  (m1b_matrixCoordinates d ρ z).trans
    { toFun := fun x i j a => b i (x i a) j
      invFun := fun y i a => (b i).symm (fun j => y i j a)
      left_inv := fun x => by
        funext i a
        exact (b i).symm_apply_apply (x i a)
      right_inv := fun y => by
        funext i j a
        exact congrFun ((b i).apply_symm_apply (fun j => y i j a)) j
      map_add' := fun x y => by
        funext i j a
        exact congrFun (map_add (b i) (x i a) (y i a)) j
      map_smul' := fun c x => by
        funext i j a
        exact congrFun (map_smul (b i) c (x i a)) j }

theorem m1b_matrixScalarCoordinates_action [FiniteDimensional ℂ V]
    (M : (i : Fin s) → Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (v : V) (i : Fin s)
    (j : Fin (Module.finrank ℂ (m1b_matrixMultiplicity d ρ z i))) :
    m1b_matrixScalarCoordinates d ρ z (ρ M v) i j =
      (M i).mulVec (m1b_matrixScalarCoordinates d ρ z v i j) := by
  funext a
  change (Module.finBasis ℂ (m1b_matrixMultiplicity d ρ z i)).equivFun
    (m1b_matrixCoordinates d ρ z (ρ M v) i a) j =
    ∑ b, M i a b * (Module.finBasis ℂ (m1b_matrixMultiplicity d ρ z i)).equivFun
      (m1b_matrixCoordinates d ρ z v i b) j
  rw [m1b_matrixCoordinates_action]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end HodgeLean.Foundations.Program
