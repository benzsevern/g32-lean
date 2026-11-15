import HodgeLean.Foundations.Program.SchoenInvariantAffineNeighborhoods
import Mathlib.Algebra.Ring.Action.Group
import Mathlib.Algebra.Algebra.Subalgebra.Operations

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Pullback by inverse automorphisms gives a left action on global sections. -/
@[instance_reducible]
def s2_schemeSectionAction (X : Scheme) (G : Type) [Group G]
    (ρ : G →* Aut X) : MulSemiringAction G Γ(X, ⊤) where
  smul g s := (ρ g⁻¹).asIso.hom.appTop s
  one_smul s := by
    change (ρ (1 : G)⁻¹).asIso.hom.appTop s = s
    simp
  mul_smul g k s := by
    change (ρ (g * k)⁻¹).asIso.hom.appTop s =
      (ρ g⁻¹).asIso.hom.appTop ((ρ k⁻¹).asIso.hom.appTop s)
    have he : (ρ (g * k)⁻¹).asIso.hom =
        (ρ g⁻¹).asIso.hom ≫ (ρ k⁻¹).asIso.hom := by
      rw [mul_inv_rev, map_mul]
      rfl
    rw [he, Scheme.Hom.comp_appTop]
    rfl
  smul_zero g := map_zero _
  smul_add g := map_add _
  smul_one g := map_one _
  smul_mul g := map_mul _

/-- Equivariant scheme morphisms induce equivariant pullbacks on section rings. -/
theorem s2_schemeSectionAction_naturality {X Y : Scheme} (G : Type) [Group G]
    (ρX : G →* Aut X) (ρY : G →* Aut Y) (f : X ⟶ Y)
    (hf : ∀ g : G, f ≫ (ρY g).asIso.hom = (ρX g).asIso.hom ≫ f)
    (g : G) (s : Γ(Y, ⊤)) :
    letI := s2_schemeSectionAction X G ρX
    letI := s2_schemeSectionAction Y G ρY
    f.appTop (g • s) = g • f.appTop s := by
  change f.appTop ((ρY g⁻¹).asIso.hom.appTop s) =
    (ρX g⁻¹).asIso.hom.appTop (f.appTop s)
  have he := congrArg (fun k : X ⟶ Y => k.appTop) (hf g⁻¹)
  exact congrArg (fun k : Γ(Y, ⊤) ⟶ Γ(X, ⊤) => k s) he

/-- The affine spectrum presentation intertwines the section-ring and scheme actions. -/
theorem s2_schemeSectionAction_isoSpec (X : Scheme) [IsAffine X]
    (G : Type) [Group G] (ρ : G →* Aut X) (g : G) :
    letI := s2_schemeSectionAction X G ρ
    X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
      (MulSemiringAction.toRingHom G Γ(X, ⊤) g)) =
      (ρ g⁻¹).asIso.hom ≫ X.isoSpec.hom := by
  exact X.isoSpec_hom_naturality (ρ g⁻¹).asIso.hom

/-- Pullback of fixed sections along an equivariant scheme morphism. -/
def s2_fixedSectionPullback {X Y : Scheme} (G : Type) [Group G]
    (ρX : G →* Aut X) (ρY : G →* Aut Y) (f : X ⟶ Y)
    (hf : ∀ g : G, f ≫ (ρY g).asIso.hom = (ρX g).asIso.hom ≫ f) :
    letI := s2_schemeSectionAction X G ρX
    letI := s2_schemeSectionAction Y G ρY
    FixedPoints.subring Γ(Y, ⊤) G →+* FixedPoints.subring Γ(X, ⊤) G := by
  letI := s2_schemeSectionAction X G ρX
  letI := s2_schemeSectionAction Y G ρY
  refine (f.appTop.hom.comp (FixedPoints.subring Γ(Y, ⊤) G).subtype).codRestrict _ ?_
  intro s g
  change g • f.appTop s.val = f.appTop s.val
  rw [← s2_schemeSectionAction_naturality G ρX ρY f hf]
  exact congrArg (fun t => f.appTop t) (s.property g)

end HodgeLean.Foundations.Program
