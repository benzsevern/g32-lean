import HodgeLean.Foundations.Program.SchoenTowerL1bCommonEtaleCoefficients
import HodgeLean.Foundations.Program.SchoenTowerL1bTwoRootBound
import HodgeLean.Foundations.Program.SchoenTowerL1bSupports

/-! The coordinate count at an actual intersection of two retained branches.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- Two distinct actual branch supports meeting under the quotient require at least two ordered coordinates. -/
theorem s2v_l1b_branch_intersection_coordinate_bound
    (Z B : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (hdim : TopologicalSpace.dim Z.left = 1) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) → ∃! u : B ⟶ T, γ ≫ u = f)
    (b : Fin 2 → ComplexPoint Z) (hb : b 0 ≠ b 1)
    (x : ComplexPoint (g3_power Z (h + 1)))
    (hx : ∀ k, (Point.map γ x).underlying ∈ (s2c_branchIdeal Z B h γ (b k)).support) :
    2 ≤ h + 1 := by
  obtain ⟨O, hxO, P, a, z, ha, hP, hI, _⟩ :=
    s2v_l1b_common_two_branch_etale_coefficients Z B hdim h γ hγinv hγ b hb x
  let U := ComplexPoint.openScheme B O.1
  let V := ComplexPoint.openScheme (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1)
  let u : U ⟶ B := ComplexPoint.openInclusion B O.1
  let v : V ⟶ g3_power Z (h + 1) :=
    ComplexPoint.openInclusion (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1)
  let q : V ⟶ U := Over.homMk (γ.left ∣_ O.1) (by
    change (γ.left ∣_ O.1) ≫ (O.1.ι ≫ B.hom) =
      (γ.left ⁻¹ᵁ O.1).ι ≫ (g3_power Z (h + 1)).hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w γ])
  let p := ComplexPoint.asOpenPoint (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1) x hxO
  have hp : Point.map u (Point.map q p) = Point.map γ x := by
    change (p ≫ q) ≫ u = x ≫ γ
    rw [Category.assoc]
    have hs : q ≫ u = v ≫ γ := by
      apply Over.OverMorphism.ext
      exact morphismRestrict_ι γ.left O.1
    rw [hs, ← Category.assoc]
    have hv : p ≫ v = x := by
      apply Over.OverMorphism.ext
      exact ComplexPoint.liftToOpen_fac (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1) x hxO
    rw [hv]
  have heval (k : Fin 2) :
      Point.evaluate ⊤ (P.eval (algebraMap ℂ Γ(U.left, ⊤) (a k))) (Point.map q p) = 0 := by
    apply (s2v_l1b_evaluate_zero_iff_support U
      ((s2c_branchIdeal Z B h γ (b k)).comap O.1.ι)
      ⟨⊤, @isAffineOpen_top _ O.2⟩ _ (hI k) (Point.map q p) (by trivial)).mpr
    rw [Scheme.IdealSheafData.support_comap]
    change (Point.map u (Point.map q p)).underlying ∈
      (s2c_branchIdeal Z B h γ (b k)).support
    rw [hp]
    exact hx k
  let φ := s2t_affinePointAlgHom V p
  have hzero (k : Fin 2) : φ ((s2t_overSectionsAlgHom q)
      (P.eval (algebraMap ℂ Γ(U.left, ⊤) (a k)))) = 0 := by
    rw [s2t_affinePointAlgHom_apply]
    exact (Point.evaluate_map q ⊤ _ p).symm.trans (heval k)
  exact s2v_l1b_descended_two_root_coordinate_bound (h + 1) z
    (s2t_overSectionsAlgHom q) P hP φ (a 0) (a 1) ha (hzero 0) (hzero 1)

end HodgeLean.Foundations.Program
