import HodgeLean.Foundations.Program.WeilTorusFamily
import HodgeLean.Foundations.Program.TorusAlgebraization
import HodgeLean.Foundations.Program.PrymFamilyB4Defs

/-! # B6-0b: marked algebraic fibres

The implication from domain membership to B2 Riemann relations supplies B5's model,
its group structure and its integral marking. HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The theta Proj of the fixed Weil lattice with the filtration at the given domain point.
Source: G32 v0.16, §2.1; van Geemen, LNM 1594, §§5.7–5.11;
Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 4.5.1 and §7.3. -/
def b60b_model (τ : g32m_Domain) : Over (Spec ↧ℂ) :=
  b5_model b60_Lattice (b60_F τ) (b60_weight_one τ) b60_E

example (τ : g32m_Domain) :
    (b60b_model τ).left =
      b5_X b60_Lattice (b60_F τ) (b60_weight_one τ) b60_E := rfl

/-- The group object given by B5 addition, identity and inversion.
Source: Birkenhake–Lange, §1.1 and Theorem 4.5.1; B5 theta algebraization. -/
instance b60b_grp (τ : g32m_Domain) : GrpObj (b60b_model τ) :=
  b5_groupObj b60_Lattice (b60_F τ) (b60_weight_one τ) b60_E
    ((b60_riemann_iff τ).2 τ.property)

example (τ : g32m_Domain) : GrpObj (b60b_model τ) := inferInstance

/-- Commutativity of the B5 group object.
Source: Birkenhake–Lange, §1.1 and Theorem 4.5.1; B5 theta algebraization. -/
instance b60b_comm (τ : g32m_Domain) : IsCommMonObj (b60b_model τ) :=
  b5_commutative b60_Lattice (b60_F τ) (b60_weight_one τ) b60_E
    ((b60_riemann_iff τ).2 τ.property)

example (τ : g32m_Domain) : IsCommMonObj (b60b_model τ) := inferInstance

/-- Integrality of the B5 theta model.
Source: Birkenhake–Lange, §1.1 and Theorem 4.5.1; B5 theta algebraization. -/
instance b60b_integral (τ : g32m_Domain) : IsIntegral (b60b_model τ).left :=
  b5_integral b60_Lattice (b60_F τ) (b60_weight_one τ) b60_E
    ((b60_riemann_iff τ).2 τ.property)

example (τ : g32m_Domain) : IsIntegral (b60b_model τ).left := inferInstance

/-- Smoothness of the B5 theta model.
Source: Birkenhake–Lange, §1.1 and Theorem 4.5.1; B5 theta algebraization. -/
instance b60b_smooth (τ : g32m_Domain) : Smooth (b60b_model τ).hom :=
  b5_smooth b60_Lattice (b60_F τ) (b60_weight_one τ) b60_E
    ((b60_riemann_iff τ).2 τ.property)

example (τ : g32m_Domain) : Smooth (b60b_model τ).hom := inferInstance

/-- Projectivity of the B5 theta model.
Source: Birkenhake–Lange, §1.1 and Theorem 4.5.1; B5 theta algebraization. -/
instance b60b_projective (τ : g32m_Domain) : IsProjective (b60b_model τ).hom :=
  b5_projective b60_Lattice (b60_F τ) (b60_weight_one τ) b60_E
    ((b60_riemann_iff τ).2 τ.property)

example (τ : g32m_Domain) : IsProjective (b60b_model τ).hom := inferInstance

/-- The specified integral marking of the theta model.
Source: Birkenhake–Lange, §1.1; B5 `b5_periodEquiv`. -/
def b60b_marking (τ : g32m_Domain) : b60_Lattice ≃+ b2_abelianLattice (b60b_model τ) :=
  b5_periodEquiv b60_Lattice (b60_F τ) (b60_weight_one τ) b60_E
    ((b60_riemann_iff τ).2 τ.property)

example (τ : g32m_Domain) (l : b60_Lattice) :
    (b60b_marking τ).symm (b60b_marking τ l) = l := (b60b_marking τ).symm_apply_apply l

/-- The action dual to multiplication by √−3 on the marked lattice.
Source: G32 v0.16, Definition 2.1; Birkenhake–Lange, §1.2. -/
def b60b_J (τ : g32m_Domain) : HQ (b60b_model τ) 1 →ₗ[ℚ] HQ (b60b_model τ) 1 :=
  b4b_cohomologyAction b60_Lattice (b60b_model τ) (b60b_marking τ)
    b60_omega.toAddMonoidHom

example (τ : g32m_Domain) : b60b_J τ 0 = 0 := map_zero _

/-- The original integral Riemann form transported to the period lattice.
Source: Birkenhake–Lange, §1.3; G32 v0.16, §2.1. -/
def b60b_form (τ : g32m_Domain) : LinearMap.BilinForm ℤ (b2_abelianLattice (b60b_model τ)) :=
  b4b_transportForm b60_Lattice (b60b_model τ) (b60b_marking τ) b60_E

example (τ : g32m_Domain) : b60b_form τ 0 0 = 0 := by
  simp only [map_zero]

/-- The degree-two class of the original form, without the third Veronese factor.
Source: Birkenhake–Lange, Lemma 1.3.1 and §2.2; G32 v0.16, §2.1. -/
def b60b_pol (τ : g32m_Domain) : HQ (b60b_model τ) 2 :=
  latticeClassHQ (b60b_model τ) (b2_bilinToAddHom (b60b_form τ))

example (τ : g32m_Domain) : b60b_pol τ =
    latticeClassHQ (b60b_model τ) (b2_bilinToAddHom (b60b_form τ)) := rfl

end HodgeLean.Foundations.Program
