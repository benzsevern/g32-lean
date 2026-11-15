import HodgeLean.Foundations.Program.RigidStartingSystemDefs
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program

theorem b65r_intertwiner_isUnit {n r : ℕ}
    (T S : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (hirr : ∀ W : Submodule ℂ (Fin n → ℂ),
      (∀ i v, v ∈ W → (T i).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : X ≠ 0)
    (hint : ∀ i, S i*X = X*T i) : IsUnit X := by
  let L := X.mulVecLin
  have hker : ∀ i v, v ∈ LinearMap.ker L → (T i).mulVec v ∈ LinearMap.ker L := by
    intro i v hv
    change X.mulVec ((T i).mulVec v) = 0
    rw [mulVec_mulVec, ← hint, ← mulVec_mulVec]
    change (S i).mulVec (L v) = 0
    rw [LinearMap.mem_ker.mp hv, mulVec_zero]
  rcases hirr (LinearMap.ker L) hker with hb | ht
  · exact mulVec_injective_iff_isUnit.mp (LinearMap.ker_eq_bot.mp hb)
  · have hz : L = 0 := LinearMap.ker_eq_top.mp ht
    have hm : X = 0 := by
      apply Matrix.ext
      intro i j
      have hh := congrArg (fun f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) ↦
        f (Pi.single j 1) i) hz
      change X.mulVec (Pi.single j 1) i = 0 at hh
      rw [mulVec_single_one] at hh
      exact hh
    exact (hX hm).elim

theorem b65r_reverse_intertwiner_isUnit {n r : ℕ}
    (T S : Fin r → Matrix (Fin n) (Fin n) ℂ)
    (hirr : ∀ W : Submodule ℂ (Fin n → ℂ),
      (∀ i v, v ∈ W → (T i).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y ≠ 0)
    (hint : ∀ i, T i*Y = Y*S i) : IsUnit Y := by
  let L := Y.mulVecLin
  have hrange : ∀ i v, v ∈ LinearMap.range L → (T i).mulVec v ∈ LinearMap.range L := by
    intro i v hv
    obtain ⟨u, rfl⟩ := hv
    refine ⟨(S i).mulVec u, ?_⟩
    change Y.mulVec ((S i).mulVec u) = (T i).mulVec (Y.mulVec u)
    rw [mulVec_mulVec, mulVec_mulVec, hint]
  rcases hirr (LinearMap.range L) hrange with hb | ht
  · have hz : L = 0 := LinearMap.range_eq_bot.mp hb
    have hm : Y = 0 := by
      apply Matrix.ext
      intro i j
      have hh := congrArg (fun f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) ↦
        f (Pi.single j 1) i) hz
      change Y.mulVec (Pi.single j 1) i = 0 at hh
      rw [mulVec_single_one] at hh
      exact hh
    exact (hY hm).elim
  · exact mulVec_surjective_iff_isUnit.mp (LinearMap.range_eq_top.mp ht)

end HodgeLean.Foundations.Program
