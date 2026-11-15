import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorStalkSpectrum
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorFibreIdeal
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorDVRUnramified
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorCurveDVR

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters IsLocalRing
namespace HodgeLean.Foundations.Program

/-- The symmetric quotient preserves prime parameters over the generic point of a coordinate fibre. -/
theorem s2v_l1b_divisor_coordinate_fibre_quotient_prime
    (Z B : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ σ, s2_permute Z (h + 1) σ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ σ, s2_permute Z (h + 1) σ ≫ f = f) → ∃! b : B ⟶ T, γ ≫ b = f)
    (b : ComplexPoint Z) (i : Fin (h + 1))
    (y : (g3_power Z (h + 1)).left) (hy : Order.coheight y = 1)
    (hγy : Order.coheight (γ.left y) = 1)
    (hyi : (g3_proj Z (h + 1) i).left y = b.underlying)
    (p : B.left.presheaf.stalk (γ.left y)) (hp : Prime p) :
    Prime ((γ.left.stalkMap y).hom p) := by
  let f := (g3_proj Z (h + 1) i).left
  letI : IsDiscreteValuationRing (B.left.presheaf.stalk (γ.left y)) :=
    s2v_l1b_divisor_codimension_one_dvr B _ hγy
  letI : IsDiscreteValuationRing (Z.left.presheaf.stalk (f y)) := by
    have HD (q : Z.left) (he : b.underlying = q) :
        IsDiscreteValuationRing (Z.left.presheaf.stalk q) := by
      subst q
      exact s2v_l1b_divisor_curve_point_dvr Z hdimZ b
    exact HD (f y) hyi.symm
  letI : IsDominant f := s2v_l1b_divisor_projection_dominant Z (h + 1) i
  obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible (Z.left.presheaf.stalk (f y))
  have hπ : Prime π := hπirr.prime
  have hmapπ : Prime ((f.stalkMap y).hom π) :=
    s2v_l1b_divisor_prime_of_maximal_ideal_map (f.stalkMap y).hom
      (s2v_l1b_divisor_dominant_stalk_injective f y)
      (s2v_l1b_divisor_coordinate_maximal_ideal_prime Z hdimZ h b i y hy hyi) π hπ
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show γ.left y ∈ (⊤ : B.left.Opens) from trivial)
  let Ub : B.left.affineOpens := ⟨U, hU⟩
  have HI := s2v_l1b_divisor_coordinate_fibre_ideal Z B hdimZ h γ hγsurj hγinv hγ
    b i y hy hyi Ub hyU
  rw [hπirr.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at HI
  exact s2v_l1b_divisor_dvr_prime_of_extended_ideal (γ.left.stalkMap y).hom
    (((s2c_branchIdeal Z B h γ b).ideal Ub).map
      (B.left.presheaf.germ U (γ.left y) hyU).hom) _ hmapπ HI p hp

end HodgeLean.Foundations.Program
