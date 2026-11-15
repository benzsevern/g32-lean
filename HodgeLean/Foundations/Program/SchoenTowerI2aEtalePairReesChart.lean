import HodgeLean.Foundations.Program.SchoenTowerI2aFlatPairRees
import HodgeLean.Foundations.Program.SchoenTowerI2aTransverseReesChart
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.RingHom.Etale

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- The actual paired Rees chart of an etale coordinate algebra has an etale
polynomial coordinate map with the specified ratio and every remaining coordinate.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13;
Mathlib, `Algebra.Etale.baseChange`. -/
theorem s2v_i2a_etale_pair_rees_coordinates
    (A : Type) [CommRing A] (n : ℕ) (S : Type) [CommRing S]
    [Algebra (MvPolynomial (Fin n) A) S] [Algebra.Etale (MvPolynomial (Fin n) A) S]
    (i j : Fin n) (hij : i ≠ j) :
    let P := MvPolynomial (Fin n) A
    let x := algebraMap P S (MvPolynomial.X i)
    let y := algebraMap P S (MvPolynomial.X j)
    let I := Ideal.span {x, y}
    let b : P →+* P := MvPolynomial.eval₂Hom MvPolynomial.C
      (fun k => if k = j then MvPolynomial.X i * MvPolynomial.X j else MvPolynomial.X k)
    ∃ c : P →+* s2t_reesChart I x,
      c.Etale ∧
      (∀ a : A, c (MvPolynomial.C a) = algebraMap S _ (algebraMap P S (MvPolynomial.C a))) ∧
      (∀ k, k ≠ j → c (MvPolynomial.X k) = algebraMap S _ (algebraMap P S (MvPolynomial.X k))) ∧
      c (MvPolynomial.X j) = s2v_i2a_reesFraction I x ⟨y, Ideal.subset_span (by simp)⟩ ∧
      (algebraMap S (s2t_reesChart I x)).comp (algebraMap P S) = c.comp b := by
  classical
  intro P x y I b
  let I0 : Ideal P := Ideal.span {MvPolynomial.X i, MvPolynomial.X j}
  let C0 := s2t_reesChart I0 (MvPolynomial.X i)
  let C1 := s2t_reesChart I x
  obtain ⟨eP, hPC, hPX, hPy, hPt⟩ := s2v_i2a_transverse_coordinate_rees_chart A n i j hij
  obtain ⟨e, hebase, heratio⟩ := s2v_i2a_flat_pair_rees_base_change P S
    (MvPolynomial.X i) (MvPolynomial.X j)
  let sw := Algebra.TensorProduct.comm P C0 S
  let d : C0 →+* C0 ⊗[P] S := algebraMap C0 (C0 ⊗[P] S)
  let c : P →+* C1 := e.toRingHom.comp (sw.toRingHom.comp (d.comp eP.symm.toRingHom))
  have hcEt : c.Etale := by
    exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.stableUnderComposition _ _
        (RingHom.Etale.stableUnderComposition _ _
          (RingHom.Etale.of_bijective eP.symm.bijective)
          ((RingHom.etale_algebraMap).mpr
            (inferInstance : Algebra.Etale C0 (C0 ⊗[P] S))))
        (RingHom.Etale.of_bijective sw.bijective))
      (RingHom.Etale.of_bijective e.bijective)
  have hcp (z : C0) : c (eP z) = e ((1 : S) ⊗ₜ[P] z) := by
    change e (sw (d (eP.symm (eP z)))) = _
    rw [eP.symm_apply_apply]
    change e (sw (z ⊗ₜ[P] (1 : S))) = _
    simp [sw]
  have hcC (a : A) : c (MvPolynomial.C a) =
      algebraMap S C1 (algebraMap P S (MvPolynomial.C a)) := by
    rw [← hPC a, hcp, hebase, hPC a]
  have hcX (k : Fin n) (hk : k ≠ j) : c (MvPolynomial.X k) =
      algebraMap S C1 (algebraMap P S (MvPolynomial.X k)) := by
    rw [← hPX k hk, hcp, hebase, hPX k hk]
  have hct : c (MvPolynomial.X j) =
      s2v_i2a_reesFraction I x ⟨y, Ideal.subset_span (by simp)⟩ := by
    rw [← hPt, hcp]
    exact heratio
  refine ⟨c, hcEt, hcC, hcX, hct, ?_⟩
  apply MvPolynomial.ringHom_ext
  · intro a
    change algebraMap S C1 (algebraMap P S (MvPolynomial.C a)) = c (b (MvPolynomial.C a))
    simp [b, MvPolynomial.eval₂Hom]
    exact (hcC a).symm
  · intro k
    change algebraMap S C1 (algebraMap P S (MvPolynomial.X k)) = c (b (MvPolynomial.X k))
    by_cases hk : k = j
    · subst k
      have H := hcp (algebraMap P C0 (MvPolynomial.X j))
      rw [hPy, hebase] at H
      simpa [b, MvPolynomial.eval₂Hom] using H.symm
    · simp [b, MvPolynomial.eval₂Hom, hk]
      exact (hcX k hk).symm

end HodgeLean.Foundations.Program
