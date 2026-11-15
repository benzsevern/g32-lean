import HodgeLean.Foundations.Program.SchoenTowerI2aRetainedOpenPairCharts
import HodgeLean.Foundations.Program.SchoenTowerI2aEtaleCoordinateNonzero
import HodgeLean.Foundations.Program.SchoenTowerI2aEtalePairReesChart

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every specified retained point over an actual affine etale base chart has
an open Rees chart with its selected ratio, all other parameters and the
coefficient square into the original retained base.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13;
Mathlib, `Algebra.Etale.baseChange`. -/
theorem s2v_i2a_retained_open_etale_pair_chart_at_point
    (Q : Scheme.{0}) (A : Type) [CommRing A] [IsDomain A] (n : ℕ) (R : Type) [CommRing R] [IsDomain R]
    [Algebra (MvPolynomial (Fin n) A) R] [Algebra.Etale (MvPolynomial (Fin n) A) R]
    (π : Spec (CommRingCat.of R) ⟶ Q) (Y B : Over Q)
    [IsIntegral B.left] [IsLocallyNoetherian B.left]
    (b : B ⟶ Y) (K : Y.left.IdealSheafData)
    (c₀ : Over.mk π ⟶ Y) [IsOpenImmersion c₀.left]
    (huniv : ∀ (Z : Over Q) (h : Z ⟶ Y),
      (∀ p : Z.left, ∃ U : Z.left.affineOpens, p ∈ U.1 ∧
        Nonempty (((K.comap h.left).ideal U) ≃ₗ[Γ(Z.left, U)] Γ(Z.left, U))) →
      ∃! v : Z ⟶ B, v ≫ b = h)
    (hcartier : ∀ p : B.left, ∃ U : B.left.affineOpens, p ∈ U.1 ∧
      Nonempty (((K.comap b.left).ideal U) ≃ₗ[Γ(B.left, U)] Γ(B.left, U)))
    (i j : Fin n) (hij : i ≠ j)
    (hK : (K.comap c₀.left).ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩ =
      (Ideal.span {algebraMap (MvPolynomial (Fin n) A) R (MvPolynomial.X i),
        algebraMap (MvPolynomial (Fin n) A) R (MvPolynomial.X j)}).map
          (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) (p : B.left) (hp : b.left p ∈ Set.range c₀.left) :
    let P := MvPolynomial (Fin n) A
    let z : Fin n → R := fun k => algebraMap P R (MvPolynomial.X k)
    ∃ a d : Fin n, ((a = i ∧ d = j) ∨ (a = j ∧ d = i)) ∧
      ∃ (g : Spec (CommRingCat.of (s2t_reesChart (Ideal.span {z a, z d}) (z a))) ⟶ B.left)
        (c : P →+* s2t_reesChart (Ideal.span {z a, z d}) (z a)),
        IsOpenImmersion g ∧ p ∈ Set.range g ∧ c.Etale ∧
        g ≫ b.left = Spec.map (CommRingCat.ofHom (algebraMap R _)) ≫ c₀.left ∧
        (∀ k, k ≠ d → c (MvPolynomial.X k) = algebraMap R _ (z k)) ∧
        c (MvPolynomial.X d) = s2v_i2a_reesFraction (Ideal.span {z a, z d}) (z a)
          ⟨z d, Ideal.subset_span (by simp)⟩ ∧
        (algebraMap R (s2t_reesChart (Ideal.span {z a, z d}) (z a))).comp (algebraMap P R) =
          c.comp (MvPolynomial.eval₂Hom MvPolynomial.C
            (fun k => if k = d then MvPolynomial.X a * MvPolynomial.X d else MvPolynomial.X k)) := by
  classical
  intro P z
  obtain ⟨gx, gy, hgx, hgy, hxb, hyb, hcover⟩ :=
    s2v_i2a_retained_pair_charts_over_open_base Q Y B b K huniv hcartier R π c₀
      (z i) (z j) (s2v_i2a_etale_coordinate_ne_zero A n R i)
      (s2v_i2a_etale_coordinate_ne_zero A n R j) hK p hp
  rcases hcover with hp | hp
  · obtain ⟨c, hc, _, hcX, hct, hsq⟩ := s2v_i2a_etale_pair_rees_coordinates A n R i j hij
    exact ⟨i, j, Or.inl ⟨rfl, rfl⟩, gx, c, hgx, hp, hc, hxb, hcX, hct, hsq⟩
  · obtain ⟨c, hc, _, hcX, hct, hsq⟩ := s2v_i2a_etale_pair_rees_coordinates A n R j i hij.symm
    exact ⟨j, i, Or.inr ⟨rfl, rfl⟩, gy, c, hgy, hp, hc, hyb, hcX, hct, hsq⟩

end HodgeLean.Foundations.Program
