import HodgeLean.Foundations.Program.MilneTensorPairRepresentation
import Mathlib.LinearAlgebra.Matrix.Reindex

noncomputable section
namespace HodgeLean.Foundations.Program

def m1b_matrixUniqueAlgEquiv (I : Type*) [Unique I] (d : I → ℕ) :
    ((i : I) → Matrix (Fin (d i)) (Fin (d i)) ℂ) ≃ₐ[ℂ]
      Matrix (Fin (d default)) (Fin (d default)) ℂ :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.piUnique (fun i => Matrix (Fin (d i)) (Fin (d i)) ℂ))
    (fun _ => rfl)

def m1b_matrixPairIndexAlgEquiv {I : Type*} (d : I → ℕ) (d₀ : ℕ)
    (hd : ∀ i, d i = d₀) (e : Fin 2 ≃ I) :
    ((i : I) → Matrix (Fin (d i)) (Fin (d i)) ℂ) ≃ₐ[ℂ]
      (Matrix (Fin d₀) (Fin d₀) ℂ × Matrix (Fin d₀) (Fin d₀) ℂ) :=
  let E := (AlgEquiv.piCongrLeft ℂ (fun i => Matrix (Fin (d i)) (Fin (d i)) ℂ) e).symm
  let F := AlgEquiv.piCongrRight (fun j : Fin 2 =>
    Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hd (e j))))
  (E.trans F).trans (m1b_matrixPairPi d₀)

theorem m1b_matrixPairIndex_ids {I : Type*} [DecidableEq I]
    (d : I → ℕ) (d₀ : ℕ) (hd : ∀ i, d i = d₀) (e : Fin 2 ≃ I) :
    m1b_matrixPairIndexAlgEquiv d d₀ hd e (Pi.single (e 0) 1) = (1, 0) ∧
      m1b_matrixPairIndexAlgEquiv d d₀ hd e (Pi.single (e 1) 1) = (0, 1) := by
  have h01 : e 0 ≠ e 1 := e.injective.ne (by decide)
  have h10 : e 1 ≠ e 0 := h01.symm
  constructor
  · apply Prod.ext
    · change Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hd (e 0)))
        (Pi.single (M := fun i => Matrix (Fin (d i)) (Fin (d i)) ℂ) (e 0) 1 (e 0)) = 1
      rw [Pi.single_eq_same, map_one]
    · change Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hd (e 1)))
        (Pi.single (M := fun i => Matrix (Fin (d i)) (Fin (d i)) ℂ) (e 0) 1 (e 1)) = 0
      rw [Pi.single_eq_of_ne h10, map_zero]
  · apply Prod.ext
    · change Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hd (e 0)))
        (Pi.single (M := fun i => Matrix (Fin (d i)) (Fin (d i)) ℂ) (e 1) 1 (e 0)) = 0
      rw [Pi.single_eq_of_ne h01, map_zero]
    · change Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hd (e 1)))
        (Pi.single (M := fun i => Matrix (Fin (d i)) (Fin (d i)) ℂ) (e 1) 1 (e 1)) = 1
      rw [Pi.single_eq_same, map_one]

end HodgeLean.Foundations.Program
