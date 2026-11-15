import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.EtaleHolomorphicAlgebra
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.HolomorphicInverse

/-! # Holomorphic evaluations in standard étale algebras

HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Classical
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Set Filter Topology HodgeLean.Foundations.Analytic
open HodgeLean.Foundations.Program
namespace AlgebraicGeometry.SingularCycles

/-- Continuous point families in a standard étale algebra are holomorphic over a holomorphic base.
Source: SGA 1, Exposé XII, §1; standard étale presentations and analytic simple roots. -/
theorem standardEtale_holomorphic_evaluation {M : Type*} [TopologicalSpace M]
    (S : an_ReducedSpace M) {U : Set M} (hU : IsOpen U)
    {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    [Algebra A B] [IsScalarTower ℂ A B] (P : StandardEtalePresentation A B)
    (e : U → (B →ₐ[ℂ] ℂ)) (he : ∀ b, Continuous (fun y => e y b))
    (hbase : ∀ a, S.IsHolFun (fun y => e y (algebraMap A B a))) (b : B) :
    S.IsHolFun (fun y => e y b) := by
  let eA : U → (A →ₐ[ℂ] ℂ) := fun y => (e y).comp (IsScalarTower.toAlgHom ℂ A B)
  let r : U → ℂ := fun y => e y P.x
  have hr : S.IsHolFun r := by
    apply holFun_algebraic_simple_root S hU eA hbase P.f r (he P.x)
    · intro y
      rw [s2e_c11_relativePolynomial_map, P.hasMap.1, map_zero]
    · intro y
      rw [s2e_c11_relativePolynomial_map]
      exact isUnit_iff_ne_zero.mp (P.hasMap.isUnit_derivative_f.map (e y))
  obtain ⟨p, n, hp⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x b
  let a : U → ℂ := fun y => Polynomial.eval₂ (eA y).toRingHom (r y) p
  let d : U → ℂ := fun y => Polynomial.eval₂ (eA y).toRingHom (r y) P.g ^ n
  have ha : S.IsHolFun a := holFun_polynomial_eval S (fun y => (eA y).toRingHom) hbase r hr p
  have hd₀ := holFun_polynomial_eval S (fun y => (eA y).toRingHom) hbase r hr P.g
  have hd : S.IsHolFun d := (S.atlas.holSubring U).pow_mem hd₀ n
  have hdn : ∀ y, d y ≠ 0 := by
    intro y
    apply pow_ne_zero n
    rw [s2e_c11_relativePolynomial_map]
    exact isUnit_iff_ne_zero.mp (P.hasMap.2.map (e y))
  have hinv := holFun_inv S d hd hdn
  have hmul : S.IsHolFun (fun y => a y * (d y)⁻¹) := (S.atlas.holSubring U).mul_mem ha hinv
  have heq : (fun y => e y b) = fun y => a y * (d y)⁻¹ := by
    funext y
    rw [← div_eq_mul_inv, eq_div_iff (hdn y)]
    have h := congrArg (fun t : B => e y t) hp
    simpa only [map_mul, map_pow, ← s2e_c11_relativePolynomial_map] using h
  rw [heq]
  exact hmul

end AlgebraicGeometry.SingularCycles
