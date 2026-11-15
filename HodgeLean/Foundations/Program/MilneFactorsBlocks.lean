import HodgeLean.Foundations.Program.MilneFactorsMatrix
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section

namespace HodgeLean.Foundations.Program

variable {K : Type*} [Field K] {s : ℕ} (d : Fin s → ℕ)

theorem m1_block_single_central (i : Fin s)
    (X : (j : Fin s) → Matrix (Fin (d j)) (Fin (d j)) K) :
    X * Pi.single i 1 = Pi.single i 1 * X := by
  funext j
  by_cases h : i = j
  · subst j
    simp
  · simp [Pi.single, Function.update, h, Ne.symm h]


theorem m1_block_reversal_coordinate (hd : ∀ i, 0 < d i)
    (τ : ((j : Fin s) → Matrix (Fin (d j)) (Fin (d j)) K) ≃ₗ[K]
      ((j : Fin s) → Matrix (Fin (d j)) (Fin (d j)) K))
    (hmul : ∀ X Y, τ (X * Y) = τ Y * τ X) (i j : Fin s) :
    τ (Pi.single i 1) j = 0 ∨ τ (Pi.single i 1) j = 1 := by
  apply m1_matrix_central_idempotent _ _ _ ⟨0, hd j⟩
  · intro X
    have h := congrArg (fun Y => Y j)
      (m1_reversal_central τ hmul (Pi.single i 1) (m1_block_single_central d i)
        (Pi.single j X))
    simpa using h
  · have hi : (Pi.single i 1 : (j : Fin s) → Matrix (Fin (d j)) (Fin (d j)) K) *
        Pi.single i 1 = Pi.single i 1 := by
      funext k
      by_cases h : i = k
      · subst k; simp
      · simp [Pi.single, Function.update, Ne.symm h]
    have h := congrArg (fun Y => Y j) (hmul (Pi.single i 1) (Pi.single i 1))
    rw [hi] at h
    exact h.symm


theorem m1_block_single_ne_zero (hd : ∀ i, 0 < d i) (i : Fin s) :
    (Pi.single i 1 : (j : Fin s) → Matrix (Fin (d j)) (Fin (d j)) K) ≠ 0 := by
  intro h
  let z : Fin (d i) := ⟨0, hd i⟩
  have hh := congrArg (fun X => X i z z) h
  simpa using hh


theorem m1_block_reversal_image (hd : ∀ i, 0 < d i)
    (τ : ((j : Fin s) → Matrix (Fin (d j)) (Fin (d j)) K) ≃ₗ[K]
      ((j : Fin s) → Matrix (Fin (d j)) (Fin (d j)) K))
    (hτ : Function.Involutive τ) (hmul : ∀ X Y, τ (X * Y) = τ Y * τ X)
    (i : Fin s) : ∃ j, τ (Pi.single i 1) = Pi.single j 1 := by
  have hn (j : Fin s) : τ (Pi.single j 1) ≠ 0 := by
    intro h
    exact m1_block_single_ne_zero d hd j (τ.injective (h.trans τ.map_zero.symm))
  obtain ⟨j, hj⟩ : ∃ j, τ (Pi.single i 1) j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hn i (funext h)
  have hj1 : τ (Pi.single i 1) j = 1 :=
    (m1_block_reversal_coordinate d hd τ hmul i j).resolve_left hj
  have hp : τ (Pi.single i 1) * Pi.single j 1 = Pi.single j 1 := by
    funext k
    by_cases h : j = k
    · subst k
      simpa using hj1
    · simp [Pi.single, Function.update, Ne.symm h]
  have hq : τ (Pi.single j 1) * Pi.single i 1 = τ (Pi.single j 1) := by
    have h := congrArg τ hp
    rw [hmul, hτ (Pi.single i 1)] at h
    exact h
  have hzero (k : Fin s) (hk : k ≠ i) : τ (Pi.single j 1) k = 0 := by
    have h := congrArg (fun X => X k) hq
    simpa [Pi.single, Function.update, hk] using h.symm
  have hji : τ (Pi.single j 1) i = 1 := by
    rcases m1_block_reversal_coordinate d hd τ hmul j i with h | h
    · exfalso
      apply hn j
      funext k
      by_cases hk : k = i
      · subst k; exact h
      · exact hzero k hk
    · exact h
  have he : τ (Pi.single j 1) = Pi.single i 1 := by
    funext k
    by_cases hk : k = i
    · subst k; simpa using hji
    · simpa [Pi.single, Function.update, hk] using hzero k hk
  refine ⟨j, ?_⟩
  have h := congrArg τ he
  rw [hτ (Pi.single j 1)] at h
  exact h.symm


theorem m1_block_single_injective (hd : ∀ i, 0 < d i) :
    Function.Injective (fun i : Fin s =>
      (Pi.single i 1 : (j : Fin s) → Matrix (Fin (d j)) (Fin (d j)) K)) := by
  intro i j h
  by_contra hij
  let z : Fin (d i) := ⟨0, hd i⟩
  have hh := congrArg (fun X => X i z z) h
  simpa [Pi.single, Function.update, hij] using hh


theorem m1_block_permutation (hd : ∀ i, 0 < d i)
    (τ : ((j : Fin s) → Matrix (Fin (d j)) (Fin (d j)) K) ≃ₗ[K]
      ((j : Fin s) → Matrix (Fin (d j)) (Fin (d j)) K))
    (hτ : Function.Involutive τ) (hmul : ∀ X Y, τ (X * Y) = τ Y * τ X) :
    ∃ σ : Equiv.Perm (Fin s), Function.Involutive σ ∧
      ∀ i, τ (Pi.single i 1) = Pi.single (σ i) 1 := by
  choose f hf using m1_block_reversal_image d hd τ hτ hmul
  have hinv : Function.Involutive f := by
    intro i
    apply m1_block_single_injective d hd (K := K)
    change Pi.single (f (f i)) 1 = Pi.single i 1
    rw [← hf (f i), ← hf i, hτ (Pi.single i 1)]
  exact ⟨⟨f, f, hinv, hinv⟩, hinv, hf⟩


theorem m1_block_reversal_single
    (τ : ((j : Fin s) → Matrix (Fin (d j)) (Fin (d j)) K) ≃ₗ[K]
      ((j : Fin s) → Matrix (Fin (d j)) (Fin (d j)) K))
    (hmul : ∀ X Y, τ (X * Y) = τ Y * τ X) (i j : Fin s)
    (hij : τ (Pi.single i 1) = Pi.single j 1)
    (A : Matrix (Fin (d i)) (Fin (d i)) K) :
    τ (Pi.single i A) = Pi.single j (τ (Pi.single i A) j) := by
  have hp : (Pi.single i A : (j : Fin s) → Matrix (Fin (d j)) (Fin (d j)) K) *
      Pi.single i 1 = Pi.single i A := by
    funext k
    by_cases h : i = k
    · subst k; simp
    · simp [Pi.single, Function.update, Ne.symm h]
  have h := congrArg τ hp
  rw [hmul, hij] at h
  funext k
  by_cases hk : k = j
  · subst k; simp
  · have hh := congrArg (fun X => X k) h
    simpa [Pi.single, Function.update, hk] using hh.symm


theorem m1_block_sizes_equal
    (τ : ((j : Fin s) → Matrix (Fin (d j)) (Fin (d j)) K) ≃ₗ[K]
      ((j : Fin s) → Matrix (Fin (d j)) (Fin (d j)) K))
    (hτ : Function.Involutive τ) (hmul : ∀ X Y, τ (X * Y) = τ Y * τ X)
    (i j : Fin s) (hij : τ (Pi.single i 1) = Pi.single j 1) : d i = d j := by
  have hji : τ (Pi.single j 1) = Pi.single i 1 := by
    rw [← hij, hτ (Pi.single i 1)]
  let V := fun k : Fin s => Matrix (Fin (d k)) (Fin (d k)) K
  let f : V i →ₗ[K] V j := (LinearMap.proj j).comp
    (τ.toLinearMap.comp (LinearMap.single K V i))
  let g : V j →ₗ[K] V i := (LinearMap.proj i).comp
    (τ.toLinearMap.comp (LinearMap.single K V j))
  have hgf (A : V i) : g (f A) = A := by
    change τ (Pi.single j (τ (Pi.single i A) j)) i = A
    rw [← m1_block_reversal_single d τ hmul i j hij A, hτ (Pi.single i A)]
    simp
  have hfg (A : V j) : f (g A) = A := by
    change τ (Pi.single i (τ (Pi.single j A) i)) j = A
    rw [← m1_block_reversal_single d τ hmul j i hji A, hτ (Pi.single j A)]
    simp
  let e : V i ≃ₗ[K] V j := { f with invFun := g, left_inv := hgf, right_inv := hfg }
  have he := e.finrank_eq
  have hs : d i * d i = d j * d j := by
    simpa only [V, Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] using he
  nlinarith

end HodgeLean.Foundations.Program
