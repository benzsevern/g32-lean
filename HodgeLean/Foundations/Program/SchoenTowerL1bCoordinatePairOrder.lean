import HodgeLean.Foundations.Program.SchoenTowerL1aParameterMorphism
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.MvPolynomial.Rename

/-! Ordering a pair of distinct etale coordinates.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Two distinct coordinates can occupy the first two positions without changing their sections.
Source: permutation of polynomial variables; Mathlib `Equiv.Perm.exists_extending_pair`. -/
theorem s2v_l1b_coordinate_pair_order
    {R A : Type} [CommRing R] [CommRing A] (c : R →+* A)
    {n : ℕ} (z : Fin n → A) (hz : (MvPolynomial.eval₂Hom c z).Etale)
    (a b : Fin n) (hab : a ≠ b) :
    ∃ (hn : 2 ≤ n) (w : Fin n → A),
      (MvPolynomial.eval₂Hom c w).Etale ∧
      w ⟨0, by omega⟩ = z a ∧ w ⟨1, by omega⟩ = z b := by
  classical
  have hv : a.val ≠ b.val := fun H => hab (Fin.ext H)
  have hn : 2 ≤ n := by omega
  let f : Fin 2 → Fin n := fun j => ⟨j.val, by omega⟩
  let g : Fin 2 → Fin n := fun j => if j = 0 then a else b
  have hf : Function.Injective f := by
    intro j k H
    apply Fin.ext
    exact congrArg (fun t : Fin n => t.val) H
  have hg : Function.Injective g := by
    intro j k H
    fin_cases j <;> fin_cases k <;> simp_all [g]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  let E := (MvPolynomial.renameEquiv R σ).toRingEquiv
  have hcomp : (MvPolynomial.eval₂Hom c z).comp E.toRingHom =
      MvPolynomial.eval₂Hom c (fun j => z (σ j)) := by
    ext j <;> simp [E, MvPolynomial.renameEquiv]
  have hEt := RingHom.Etale.stableUnderComposition E.toRingHom
    (MvPolynomial.eval₂Hom c z) (RingHom.Etale.of_bijective E.bijective) hz
  rw [hcomp] at hEt
  refine ⟨hn, (fun j => z (σ j)), hEt, ?_, ?_⟩
  · exact congrArg z (hσ 0)
  · exact congrArg z (hσ 1)

end HodgeLean.Foundations.Program
