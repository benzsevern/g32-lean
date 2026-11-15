import HodgeLean.Foundations.Abdulali.StandardReflection
import Mathlib.Tactic.LinearCombination

noncomputable section
namespace HodgeLean.Foundations.Abdulali
open HodgeLean.Foundations.Program

/-- Every bilinear form fixed by the full standard orthogonal group is a
scalar multiple of the standard form. Reflections eliminate off-diagonal
entries and coordinate transpositions identify diagonal entries.
Source: Weyl, The Classical Groups, Chapter II, §9 (degree-two invariants). -/
theorem standard_orthogonal_bilinear_forms (d : ℕ) (hd : 0 < d)
    (F : LinearMap.BilinForm ℂ (Fin d → ℂ))
    (hF : ∀ u ∈ m1b_isometries (1 : Matrix (Fin d) (Fin d) ℂ).toBilin',
      ∀ x y, F (u x) (u y) = F x y) :
    ∃ c : ℂ, F = c • (1 : Matrix (Fin d) (Fin d) ℂ).toBilin' := by
  classical
  let b := Pi.basisFun ℂ (Fin d)
  have hdiag (i : Fin d) : F (b i) (b i) = F (b ⟨0, hd⟩) (b ⟨0, hd⟩) := by
    let π := Equiv.swap i (⟨0, hd⟩ : Fin d)
    let u : Module.End ℂ (Fin d → ℂ) := {
      toFun := fun x j => x (π j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    have hs : u * u = 1 := by
      apply LinearMap.ext
      intro x
      ext j
      change x (π (π j)) = x j
      simp [π]
    have hu : u ∈ m1b_isometries (1 : Matrix (Fin d) (Fin d) ℂ).toBilin' := by
      refine ⟨⟨⟨u, u, hs, hs⟩, rfl⟩, ?_⟩
      intro x y
      simp only [Matrix.toBilin'_apply', Matrix.one_mulVec, dotProduct]
      exact Equiv.sum_comp π (fun j => x j * y j)
    have hub : u (b i) = b ⟨0, hd⟩ := by
      ext j
      simp only [b, Pi.basisFun_apply]
      change (Pi.single i (1 : ℂ) : Fin d → ℂ) (π j) = (Pi.single ⟨0, hd⟩ (1 : ℂ) : Fin d → ℂ) j
      simp [π, Pi.single_apply, Equiv.swap_apply_def] <;> aesop
    have h := hF u hu (b i) (b i)
    rw [hub] at h
    exact h.symm
  have hoff (i j : Fin d) (hij : i ≠ j) : F (b i) (b j) = 0 := by
    let c : Fin d → ℂ := fun k => if k = i then -1 else 1
    let u : Module.End ℂ (Fin d → ℂ) := LinearMap.pi (fun k => c k • LinearMap.proj k)
    have hcc (k : Fin d) : c k * c k = 1 := by dsimp only [c]; split_ifs <;> norm_num
    have hs : u * u = 1 := by
      apply LinearMap.ext
      intro x
      ext k
      change c k * (c k * x k) = x k
      rw [← mul_assoc, hcc, one_mul]
    have hu : u ∈ m1b_isometries (1 : Matrix (Fin d) (Fin d) ℂ).toBilin' := by
      refine ⟨⟨⟨u, u, hs, hs⟩, rfl⟩, ?_⟩
      intro x y
      simp only [Matrix.toBilin'_apply', Matrix.one_mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro k _
      change (c k * x k) * (c k * y k) = x k * y k
      calc _ = (c k * c k) * (x k * y k) := by ring
           _ = _ := by rw [hcc, one_mul]
    have hui : u (b i) = -b i := by
      ext k
      simp only [b, Pi.basisFun_apply]
      change c k * ((Pi.single i (1 : ℂ) : Fin d → ℂ) k) =
        -((Pi.single i (1 : ℂ) : Fin d → ℂ) k)
      by_cases hk : k = i
      · subst k; simp [u, c, b]
      · simp [u, c, b, hk, Pi.single_apply]
    have huj : u (b j) = b j := by
      ext k
      simp only [b, Pi.basisFun_apply]
      change c k * ((Pi.single j (1 : ℂ) : Fin d → ℂ) k) =
        (Pi.single j (1 : ℂ) : Fin d → ℂ) k
      by_cases hk : k = j
      · subst k; simp [u, c, b, Ne.symm hij]
      · simp [u, c, b, hk, Pi.single_apply]
    have h := hF u hu (b i) (b j)
    rw [hui, huj, map_neg, LinearMap.neg_apply] at h
    have hz : (2 : ℂ) * F (b i) (b j) = 0 := by linear_combination -h
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  refine ⟨F (b ⟨0, hd⟩) (b ⟨0, hd⟩), ?_⟩
  apply b.ext
  intro i
  apply b.ext
  intro j
  change F (b i) (b j) = F (b ⟨0, hd⟩) (b ⟨0, hd⟩) *
    (1 : Matrix (Fin d) (Fin d) ℂ).toBilin' (b i) (b j)
  simp only [b, Pi.basisFun_apply, Matrix.toBilin'_single, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simpa [b] using hdiag i
  · simpa [hij, b] using hoff i j hij

end HodgeLean.Foundations.Abdulali
