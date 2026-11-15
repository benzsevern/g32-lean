import HodgeLean.Foundations.Program.UniversalFamilyProofs
import HodgeLean.Papers.WeilTransferDefs

/-! Theta algebraization with a retained integral quadratic action. -/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct CategoryTheory.MonObj
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Algebraize a polarized marked weight-one lattice, keeping its quadratic action.
The construction uses the original integral Riemann form for the polarization.
Source: Birkenhake–Lange, Complex Abelian Varieties, 2nd ed., Theorem 4.5.1
and §§1.2, 2.2; van Geemen, LNM 1594, §§5.7–5.11. -/
def weil_marked_torus (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (E : LinearMap.BilinForm ℤ Λ) (hE : b2_IsRiemannForm Λ F E)
    (J : Λ →+ Λ) (hJ : ∀ x, J (J x) = (-3 : ℤ) • x)
    (hJF : F ≤ F.comap (b2_cplxMap J)) : g32t_Sixfold := by
  let X := b5_model Λ F hF E
  letI : GrpObj X := b5_groupObj Λ F hF E hE
  letI : IsCommMonObj X := b5_commutative Λ F hF E hE
  letI : IsIntegral X.left := b5_integral Λ F hF E hE
  letI : Smooth X.hom := b5_smooth Λ F hF E hE
  letI : IsProjective X.hom := b5_projective Λ F hF E hE
  let e := b5_periodEquiv Λ F hF E hE
  exact
    { X := X
      W :=
        { J := b4b_cohomologyAction Λ X e J
          J_sq := b4b_action_sq_aux Λ X e J hJ
          preserves := b4b_action_preserves_aux Λ X e F
            (b5_period_filtration Λ F hF E hE) J hJF }
      pol := latticeClassHQ X (b2_bilinToAddHom (b4b_transportForm Λ X e E)) }

example (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (E : LinearMap.BilinForm ℤ Λ) (hE : b2_IsRiemannForm Λ F E)
    (J : Λ →+ Λ) (hJ : ∀ x, J (J x) = (-3 : ℤ) • x)
    (hJF : F ≤ F.comap (b2_cplxMap J)) :
    (weil_marked_torus Λ F hF E hE J hJ hJF).X = b5_model Λ F hF E := rfl

/-- The integral marking fixes twice the dimension of the algebraic fibre.
Source: Birkenhake–Lange, Complex Abelian Varieties, 2nd ed., §1.1. -/
theorem weil_marked_torus_rank (Λ : Type) [AddCommGroup Λ]
    [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (E : LinearMap.BilinForm ℤ Λ) (hE : b2_IsRiemannForm Λ F E)
    (J : Λ →+ Λ) (hJ : ∀ x, J (J x) = (-3 : ℤ) • x)
    (hJF : F ≤ F.comap (b2_cplxMap J)) :
    Module.finrank ℤ Λ = 2 * dim (weil_marked_torus Λ F hF E hE J hJ hJF).X.left := by
  let P := weil_marked_torus Λ F hF E hE J hJ hJF
  let e : Λ ≃+ b2_abelianLattice P.X := b5_periodEquiv Λ F hF E hE
  have hmark := e.toIntLinearEquiv.finrank_eq
  have hab : Module.finrank ℤ (b2_abelianLattice P.X) = 2 * dim P.X.left := by
    rw [← b2_two_mul_finrank (b2_abelianF P.X) (b2_abelianF_isWeightOne P.X),
      b2_abelian_finrank]
  exact hmark.trans hab

/-- The G32 marked fibre is the rank-twelve instance of the same construction.
Source: G32 v0.16, §2.1; the definitions of `b60b_univ` and `weil_marked_torus`. -/
theorem weil_marked_torus_g32 (τ : g32m_Domain) :
    weil_marked_torus b60_Lattice (b60_F τ) (b60_weight_one τ) b60_E
      ((b60_riemann_iff τ).2 τ.property) b60_omega.toAddMonoidHom
      (fun x => LinearMap.congr_fun b60_omega_square x)
      (fun x hx => b60_omega_preserves τ ⟨x, hx, rfl⟩) = b60b_univ τ := rfl

#print axioms weil_marked_torus
#print axioms weil_marked_torus_rank
#print axioms weil_marked_torus_g32

end HodgeLean.Foundations.Program
