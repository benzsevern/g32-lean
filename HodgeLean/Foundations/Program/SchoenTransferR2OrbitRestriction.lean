import HodgeLean.Foundations.Program.SchoenTransferR2PullbackPowers
import HodgeLean.Foundations.CyclicAction

/-! # Primitive restriction on every retained orbit component

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- An equivariant restriction vanishing on the primitive part also vanishes
on every actual orbit component.
Source: Schoen (1988), §1, cyclic character decomposition and equivariance.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_primitive_orbit_restriction_zero
    {Q W V : Over (Spec ↧ℂ)} (ι : Q ⟶ W) (φ : W ⟶ V)
    (δ : W ⟶ W) (d : V ⟶ V) (hequiv : δ ≫ φ = φ ≫ d) (n m : ℕ)
    (hzero : ∀ u ∈ isotypic (s2e_pullback ℚ d n) m,
      s2e_pullback ℚ (ι ≫ φ) n u = 0)
    (i : ℕ) (u : Cohomology ℚ (TopCat.of (ComplexPoint V)) n)
    (hu : u ∈ isotypic (s2e_pullback ℚ d n) m) :
    s2e_pullback ℚ ((ι ≫ (End.of δ ^ i).asHom) ≫ φ) n u = 0 := by
  have hpow : ∀ j : ℕ, (End.of δ ^ j).asHom ≫ φ = φ ≫ (End.of d ^ j).asHom := by
    intro j
    induction j with
    | zero => change (𝟙 W) ≫ φ = φ ≫ (𝟙 V); simp
    | succ j hj =>
      have hδ : (End.of δ ^ (j + 1)).asHom = (End.of δ ^ j).asHom ≫ δ := by
        rw [pow_succ']; rfl
      have hd : (End.of d ^ (j + 1)).asHom = (End.of d ^ j).asHom ≫ d := by
        rw [pow_succ']; rfl
      rw [hδ, hd, Category.assoc, hequiv, ← Category.assoc, hj, Category.assoc]
  let T := s2e_pullback ℚ d n
  let p := Polynomial.cyclotomic m ℚ
  have hc : Polynomial.aeval T p * T ^ i = T ^ i * Polynomial.aeval T p := by
    calc
      _ = Polynomial.aeval T (p * Polynomial.X ^ i) := by
        rw [map_mul, map_pow, Polynomial.aeval_X]
      _ = Polynomial.aeval T (Polynomial.X ^ i * p) := by rw [mul_comm p]
      _ = _ := by rw [map_mul, map_pow, Polynomial.aeval_X]
  have hui : (T ^ i) u ∈ isotypic T m := by
    change Polynomial.aeval T p ((T ^ i) u) = 0
    rw [← Module.End.mul_apply, hc, Module.End.mul_apply]
    change (T ^ i) (Polynomial.aeval T p u) = 0
    change Polynomial.aeval T p u = 0 at hu
    rw [hu, map_zero]
  rw [Category.assoc, hpow, ← Category.assoc, s4_assembly_pullback_comp,
    LinearMap.comp_apply, s4_assembly_pullback_pow]
  exact hzero _ hui

#print axioms s4_assembly_primitive_orbit_restriction_zero
end HodgeLean.Foundations.Program
