import HodgeLean.Foundations.Program.SchoenQuotientFiniteType
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Scheme-point orbit fibres give exactly the same orbit fibres on rational points
for a finite-type source over an algebraically closed field. -/
theorem s2_gluedQuotientMap_rational_fibres {k : Type} [Field k] [IsAlgClosed k]
    (X : Scheme.{0}) [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (s : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType s]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hover : ∀ g : G, (ρ g).asIso.hom ≫ s = s)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val)
    (x y : Spec (CommRingCat.of k) ⟶ X) (hx : x ≫ s = 𝟙 _) (hy : y ≫ s = 𝟙 _) :
    x ≫ s2_gluedQuotientMap X G ρ hcover = y ≫ s2_gluedQuotientMap X G ρ hcover ↔
      ∃ g : G, x ≫ (ρ g).asIso.hom = y := by
  constructor
  · intro hxy
    have hp := congrArg (fun f => f (IsLocalRing.closedPoint k)) hxy
    obtain ⟨g, hg⟩ := (s2_gluedQuotientMap_fibres X G ρ hcover
      (x (IsLocalRing.closedPoint k)) (y (IsLocalRing.closedPoint k))).mp hp
    refine ⟨g, ext_of_apply_closedPoint_eq s ?_ hy hg⟩
    rw [Category.assoc, hover, hx]
  · rintro ⟨g, rfl⟩
    rw [Category.assoc, s2_gluedQuotientMap_invariant]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Surjective morphisms between finite-type schemes over an algebraically closed
field are surjective on rational points. -/
theorem s2_rationalPoint_surjective_of_surjective {k : Type} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of k))
    (t : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType s] [LocallyOfFiniteType t]
    (q : X ⟶ Y) (hq : Function.Surjective q) (hqt : q ≫ t = s)
    (y : Spec (CommRingCat.of k) ⟶ Y) (hy : y ≫ t = 𝟙 _) :
    ∃ x : Spec (CommRingCat.of k) ⟶ X, x ≫ s = 𝟙 _ ∧ x ≫ q = y := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace s
  let p := y (IsLocalRing.closedPoint k)
  have hp : IsClosed ({p} : Set Y) := (pointEquivClosedPoint t ⟨y, hy⟩).property
  obtain ⟨u, hu⟩ := hq p
  have hfibre : (q ⁻¹' ({p} : Set Y)).Nonempty := ⟨u, hu⟩
  obtain ⟨v, hv, hvc⟩ := nonempty_inter_closedPoints hfibre
    (hp.preimage q.continuous).isLocallyClosed
  let x := pointOfClosedPoint s v hvc
  refine ⟨x, pointOfClosedPoint_comp s v hvc, ?_⟩
  apply ext_of_apply_closedPoint_eq t
  · rw [Category.assoc, hqt]
    exact pointOfClosedPoint_comp s v hvc
  · exact hy
  · change q (x (IsLocalRing.closedPoint k)) = p
    rw [pointOfClosedPoint_apply]
    exact hv

/-- The glued invariant projection is surjective on rational points over an
algebraically closed field, with its actual induced structure morphism. -/
theorem s2_gluedQuotientMap_rational_surjective {k : Type} [Field k] [IsAlgClosed k]
    (X : Scheme.{0}) [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (s : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType s]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hover : ∀ g : G, (ρ g).asIso.hom ≫ s = s)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val)
    (y : Spec (CommRingCat.of k) ⟶ s2_invariantAffineGlued X G ρ)
    (hy : y ≫ s2_gluedQuotientStructure s G ρ hover hcover = 𝟙 _) :
    ∃ x : Spec (CommRingCat.of k) ⟶ X, x ≫ s = 𝟙 _ ∧
      x ≫ s2_gluedQuotientMap X G ρ hcover = y := by
  haveI : IsNoetherianRing Γ(Spec (CommRingCat.of k), ⊤) :=
    isNoetherianRing_of_ringEquiv k (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm
  haveI := s2_gluedQuotientStructure_locallyOfFiniteType s G ρ hover hcover
  exact s2_rationalPoint_surjective_of_surjective s
    (s2_gluedQuotientStructure s G ρ hover hcover) (s2_gluedQuotientMap X G ρ hcover)
    (s2_gluedQuotientMap_surjective X G ρ hcover)
    (s2_gluedQuotientStructure_fac s G ρ hover hcover) y hy

end HodgeLean.Foundations.Program
