import HodgeLean.Foundations.Program.SchoenTowerI2aSpectrumStrictBranch
import HodgeLean.Foundations.Program.SchoenTowerI2aRetainedOpenEtalePairChart
import HodgeLean.Foundations.Program.SchoenTowerI2aEtaleCoordinateNonzero
import HodgeLean.Foundations.Program.SchoenTowerI2aEtalePairReesChart

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every actual labeled branch equation on an affine etale base chart
transports simultaneously to a retained Rees point chart, including the unit
ideal for every label in the removed coordinate slot.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13;
Mathlib, `Algebra.Etale.baseChange`. -/
theorem s2v_i2a_retained_labeled_strict_chart_at_point
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
          (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    (ι : Type) (D : ι → Y.left.IdealSheafData) (κ : ι → Fin n)
    (hD : ∀ t, ((D t).comap c₀.left).ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩ =
      (Ideal.span {algebraMap (MvPolynomial (Fin n) A) R (MvPolynomial.X (κ t))}).map
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    (p : B.left) (hp : b.left p ∈ Set.range c₀.left) :
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
            (fun k => if k = d then MvPolynomial.X a * MvPolynomial.X d else MvPolynomial.X k)) ∧
        ∀ t, ((s2c_strictTransform b.left (D t) K).comap g).ideal ⟨⊤, isAffineOpen_top _⟩ =
          if κ t = a then ⊤ else Ideal.span
            {((Scheme.ΓSpecIso (CommRingCat.of (s2t_reesChart (Ideal.span {z a, z d}) (z a)))).inv.hom
              (c (MvPolynomial.X (κ t))))} := by
  classical
  intro P z
  obtain ⟨a, d, horient, g, c, hg, hpg, hc, hgb, hcX, hct, hsq⟩ :=
    s2v_i2a_retained_open_etale_pair_chart_at_point Q A n R π Y B b K c₀ huniv hcartier
      i j hij hK p hp
  have had : a ≠ d := by
    rcases horient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hij
    · exact hij.symm
  have hcentre : (K.comap c₀.left).ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩ =
      (Ideal.span {z a, z d}).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
    rcases horient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hK
    · change (K.comap c₀.left).ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩ =
        (Ideal.span {z d, z a}).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom at hK
      simpa only [Set.pair_comm (z d) (z a)] using hK
  letI : IsOpenImmersion g := hg
  refine ⟨a, d, horient, g, c, hg, hpg, hc, hgb, hcX, hct, hsq, ?_⟩
  intro t
  exact s2v_i2a_spectrum_etale_strict_branch_ideal A n a d (κ t) had R
    (s2t_reesChart (Ideal.span {z a, z d}) (z a)) (algebraMap P R) c hc
    (algebraMap R _) hsq b.left c₀.left g hgb (D t) K (hD t) hcentre

end HodgeLean.Foundations.Program
