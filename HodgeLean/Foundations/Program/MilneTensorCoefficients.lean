import HodgeLean.Foundations.Program.MilneTensorOrbit
import Mathlib.LinearAlgebra.Multilinear.Curry

noncomputable section
namespace HodgeLean.Foundations.Program
variable {U W : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]

def m1b_complementCoefficient {n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => U × W) ℂ) (s : Finset (Fin n))
    (x : Fin s.card → U) : MultilinearMap ℂ (fun _ : Fin sᶜ.card => W) ℂ :=
  ((MultilinearMap.curryFinFinset ℂ ℂ (U × W) (s := s) rfl rfl f)
    (fun i => (x i, 0))).compLinearMap (fun _ => LinearMap.inr ℂ U W)

theorem m1b_complementCoefficient_apply {n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => U × W) ℂ) (s : Finset (Fin n))
    (x : Fin s.card → U) (y : Fin sᶜ.card → W) :
    m1b_complementCoefficient f s x y =
      f (fun i => Sum.elim (fun j => (x j, 0)) (fun j => (0, y j))
        ((finSumEquivOfFinset (s := s) rfl rfl).symm i)) := rfl

theorem m1b_complementCoefficient_invariant {n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => U × W) ℂ) (s : Finset (Fin n))
    (x : Fin s.card → U) (g : W →ₗ[ℂ] W)
    (hf : ∀ v : Fin n → U × W, f (fun i => ((v i).1, g (v i).2)) = f v)
    (y : Fin sᶜ.card → W) :
    m1b_complementCoefficient f s x (fun i => g (y i)) =
      m1b_complementCoefficient f s x y := by
  rw [m1b_complementCoefficient_apply, m1b_complementCoefficient_apply]
  convert hf (fun i => Sum.elim (fun j => (x j, 0)) (fun j => (0, y j))
    ((finSumEquivOfFinset (s := s) rfl rfl).symm i)) using 1
  congr 1
  funext i
  cases (finSumEquivOfFinset (s := s) rfl rfl).symm i <;> simp only [Sum.elim_inl,
    Sum.elim_inr, map_zero]

theorem m1b_complementCoefficient_expansion {n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => U × W) ℂ)
    (x : Fin n → U) (y : Fin n → W) :
    f (fun i => (x i, y i)) = ∑ s : Finset (Fin n),
      m1b_complementCoefficient f s (fun j => x (s.orderEmbOfFin rfl j))
        (fun j => y (sᶜ.orderEmbOfFin rfl j)) := by
  have hxy : (fun i => (x i, y i)) = (fun i => (x i, (0 : W))) +
      (fun i => ((0 : U), y i)) := by
    funext i
    simp only [Pi.add_apply, Prod.mk_add_mk, add_zero, zero_add]
  rw [hxy, f.map_add_univ]
  apply Finset.sum_congr rfl
  intro s _
  rw [m1b_complementCoefficient_apply]
  congr 1
  funext i
  obtain ⟨j, rfl⟩ := (finSumEquivOfFinset (s := s) rfl rfl).surjective i
  cases j with
  | inl j =>
    rw [Equiv.symm_apply_apply, Sum.elim_inl, finSumEquivOfFinset_inl,
      Finset.piecewise_eq_of_mem]
    exact Finset.orderEmbOfFin_mem s rfl j
  | inr j =>
    rw [Equiv.symm_apply_apply, Sum.elim_inr, finSumEquivOfFinset_inr,
      Finset.piecewise_eq_of_notMem]
    exact Finset.mem_compl.mp (Finset.orderEmbOfFin_mem sᶜ rfl j)

theorem m1b_complementCoefficient_smul {n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => U × W) ℂ) (s : Finset (Fin n))
    (c : ℂ) (x : Fin s.card → U) :
    m1b_complementCoefficient f s (fun i => c • x i) =
      c ^ s.card • m1b_complementCoefficient f s x := by
  apply MultilinearMap.ext
  intro y
  let F := MultilinearMap.curryFinFinset ℂ ℂ (U × W) (s := s) rfl rfl f
  have h := F.map_smul_univ (fun _ => c) (fun i => (x i, (0 : W)))
  have hh := congrArg (fun q : MultilinearMap ℂ (fun _ : Fin sᶜ.card => U × W) ℂ =>
    q (fun i => (0, y i))) h
  simp only [Prod.smul_mk, smul_zero, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_apply] at hh
  exact hh

theorem m1b_complementCoefficient_odd {n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => U × W) ℂ) (s : Finset (Fin n))
    (hs : Odd s.card) (x : Fin s.card → U)
    (hf : ∀ v : Fin n → U × W, f (fun i => (-(v i).1, (v i).2)) = f v) :
    m1b_complementCoefficient f s x = 0 := by
  apply MultilinearMap.ext
  intro y
  have hinv : m1b_complementCoefficient f s (fun i => -x i) y =
      m1b_complementCoefficient f s x y := by
    rw [m1b_complementCoefficient_apply, m1b_complementCoefficient_apply]
    convert hf (fun i => Sum.elim (fun j => (x j, 0)) (fun j => (0, y j))
      ((finSumEquivOfFinset (s := s) rfl rfl).symm i)) using 1
    congr 1
    funext i
    cases (finSumEquivOfFinset (s := s) rfl rfl).symm i <;>
      simp only [Sum.elim_inl, Sum.elim_inr, neg_zero]
  have hscale := congrArg (fun q : MultilinearMap ℂ (fun _ : Fin sᶜ.card => W) ℂ => q y)
    (m1b_complementCoefficient_smul f s (-1) x)
  simp only [neg_one_smul, hs.neg_one_pow] at hscale
  exact CharZero.neg_eq_self_iff.mp (hscale.symm.trans hinv)

end HodgeLean.Foundations.Program
