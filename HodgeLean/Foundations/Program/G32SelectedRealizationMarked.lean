import HodgeLean.Foundations.Program.G32SelectedRealizationImage
import HodgeLean.Foundations.Program.G32SelectedRealizationIntegralProjector

noncomputable section
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open scoped TensorProduct CategoryTheory.MonObj Manifold ContDiff
namespace HodgeLean.Foundations.Program

theorem g32y_torus_map_period (X Y : Over (Spec ↧ℂ))
    [GrpObj X] [GrpObj Y] [IsIntegral X.left] [IsIntegral Y.left]
    [Smooth X.hom] [Smooth Y.hom] [IsProjective X.hom] [IsProjective Y.hom]
    (f : X ⟶ Y) (φ : b2_abelianLattice X →+ b2_abelianLattice Y)
    (hφ : b2_abelianF X ≤ (b2_abelianF Y).comap (b2_cplxMap φ))
    (hpt : ∀ t, Point.map f (Additive.toMul (b2_abelianToPoint X t)) =
      Additive.toMul (b2_abelianToPoint Y (b2_torusHom _ _ φ hφ t))) :
    ∀ x l, abelianPeriod X (homPullback f 1 x) l = abelianPeriod Y x (φ l) := by
  have hl (l : b2_abelianLattice X) :
      (Point.continuousMap f).comp (abelianLatticeLoop X l) = abelianLatticeLoop Y (φ l) := by
    apply ContinuousMap.ext
    intro z
    induction z using QuotientAddGroup.induction_on with
    | H t =>
      change Point.map f (Additive.toMul (oneParameterSubgroup X (dim X.left)
        (l : Fin (dim X.left) → ℂ) t)) =
          Additive.toMul (oneParameterSubgroup Y (dim Y.left) (φ l) t)
      rw [← complexExponential_smul, ← complexExponential_smul]
      have hh := hpt (QuotientAddGroup.mk (Submodule.Quotient.mk ((t : ℂ) ⊗ₜ[ℤ] l)))
      change Point.map f (Additive.toMul (complexExponential X (dim X.left)
        ((t : ℂ) • (l : Fin (dim X.left) → ℂ)))) =
          Additive.toMul (complexExponential Y (dim Y.left)
            ((t : ℂ) • (φ l : Fin (dim Y.left) → ℂ))) at hh
      exact hh
  intro x l
  have hc : cupComparison X 1 (homPullback f 1 x) =
      cohomologyMap ℚ 1 (TopCat.ofHom (Point.continuousMap f)) (cupComparison Y 1 x) := by
    simp [homPullback]
  change loopPeriod (abelianLatticeLoop X l) (cupComparison X 1 (homPullback f 1 x)) =
    loopPeriod (abelianLatticeLoop Y (φ l)) (cupComparison Y 1 x)
  rw [hc, ← loopPeriod_comp, hl]

theorem g32y_algebraize_period_map (X Y : Over (Spec ↧ℂ))
    [GrpObj X] [GrpObj Y] [IsIntegral X.left] [IsIntegral Y.left]
    [Smooth X.hom] [Smooth Y.hom] [IsProjective X.hom] [IsProjective Y.hom]
    (φ : b2_abelianLattice X →+ b2_abelianLattice Y)
    (hφ : b2_abelianF X ≤ (b2_abelianF Y).comap (b2_cplxMap φ)) :
    ∃ f : X ⟶ Y, IsMonHom f ∧ ∀ x l,
      abelianPeriod X (homPullback f 1 x) l = abelianPeriod Y x (φ l) := by
  obtain ⟨f, hf, hpt⟩ := g32y_algebraize_torus_map X Y φ hφ
  exact ⟨f, hf, g32y_torus_map_period X Y f φ hφ hpt⟩

theorem g32y_weil_of_period_intertwining (J P : Over (Spec ↧ℂ))
    [GrpObj J] [GrpObj P] [IsIntegral J.left] [IsIntegral P.left]
    [Smooth J.hom] [Smooth P.hom] [IsProjective J.hom] [IsProjective P.hom]
    (q : J ⟶ P) (z : J ⟶ J)
    (pL : b2_abelianLattice J →+ b2_abelianLattice P)
    (zL : b2_abelianLattice J →+ b2_abelianLattice J)
    (A : Module.End ℚ (HQ P 1))
    (aL : b2_abelianLattice P →+ b2_abelianLattice P)
    (hq : ∀ x l, abelianPeriod J (homPullback q 1 x) l = abelianPeriod P x (pL l))
    (hz : ∀ x l, abelianPeriod J (homPullback z 1 x) l = abelianPeriod J x (zL l))
    (hA : ∀ x l, abelianPeriod P (A x) l = abelianPeriod P x (aL l))
    (hmark : ∀ l, aL (pL l) = pL l + 2 • pL (zL l)) :
    ∀ x, homPullback q 1 (A x) =
      homPullback q 1 x + (2 : ℚ) • homPullback z 1 (homPullback q 1 x) := by
  intro x
  obtain ⟨eJ, heJ⟩ := spec_abelianPeriod_equiv J
  obtain ⟨eP, heP⟩ := spec_abelianPeriod_equiv P
  apply eJ.injective
  apply AddMonoidHom.ext
  intro l
  rw [heJ, heJ, hq, hA, map_add, Pi.add_apply, map_smul, Pi.smul_apply, hz, hq, hq]
  rw [hmark, ← heP, ← heP, ← heP, map_add, map_nsmul]
  simp only [nsmul_eq_mul, smul_eq_mul]
  norm_num

theorem g32y_lattice_retract_periods (X Y : Over (Spec ↧ℂ))
    [GrpObj X] [GrpObj Y] [IsIntegral X.left] [IsIntegral Y.left]
    [Smooth X.hom] [Smooth Y.hom] [IsProjective X.hom] [IsProjective Y.hom]
    (f : AbelianEnd X)
    (iL : b2_abelianLattice Y →+ b2_abelianLattice X)
    (pL : b2_abelianLattice X →+ b2_abelianLattice Y)
    (hiL : b2_abelianF Y ≤ (b2_abelianF X).comap (b2_cplxMap iL))
    (hpL : b2_abelianF X ≤ (b2_abelianF Y).comap (b2_cplxMap pL))
    (N : ℕ) (hret : pL.comp iL = N • AddMonoidHom.id _)
    (hφ : ∀ x l, abelianPeriod X (abelianEndAction X f x) l =
      abelianPeriod X x (iL (pL l))) :
    ∃ i : Y ⟶ X, ∃ q : X ⟶ Y,
      IsMonHom i ∧ IsMonHom q ∧ i ≫ q = 𝟙 Y ^ N ∧ q ≫ i = f.hom ∧
      (∀ x l, abelianPeriod Y (homPullback i 1 x) l = abelianPeriod X x (iL l)) ∧
      ∀ x l, abelianPeriod X (homPullback q 1 x) l = abelianPeriod Y x (pL l) := by
  obtain ⟨i, q, hi, hq, hr, hqi, hipt, hqpt⟩ :=
    g32y_lattice_retract_points X Y f iL pL hiL hpL N hret hφ
  exact ⟨i, q, hi, hq, hr, hqi, g32y_torus_map_period Y X i iL hiL hipt,
    g32y_torus_map_period X Y q pL hpL hqpt⟩

end HodgeLean.Foundations.Program
