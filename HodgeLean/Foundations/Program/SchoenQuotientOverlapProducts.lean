import HodgeLean.Foundations.Program.SchoenQuotientBase
import HodgeLean.Foundations.Program.SchoenNoetherianFiniteDescent

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Invariant affine comparisons commute with the actual glued chart immersions. -/
theorem s2_invariantAffineQuotientMap_gluedι (X : Scheme.{0}) [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (U V : s2_InvariantAffineOpen X G ρ) (h : U ≤ V) :
    s2_invariantAffineQuotientMap X G ρ U V h ≫ s2_invariantAffineGluedι X G ρ V =
      s2_invariantAffineGluedι X G ρ U :=
  colimit.w (s2_invariantAffineDiagram X G ρ) (homOfLE h)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The invariant quotient of a chart intersection maps to the relative product
of the two quotient charts over the actual induced base structure. -/
def s2_quotientOverlapPair {X S : Scheme.{0}} [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [IsAffine S]
    (s : X ⟶ S) (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hover : ∀ g : G, (ρ g).asIso.hom ≫ s = s)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val)
    (U V : s2_InvariantAffineOpen X G ρ) :
    s2_invariantAffineQuotientObj X G ρ (s2_invariantAffineOpenInf X G ρ U V) ⟶
      pullback (s2_invariantAffineGluedι X G ρ U ≫ s2_gluedQuotientStructure s G ρ hover hcover)
        (s2_invariantAffineGluedι X G ρ V ≫ s2_gluedQuotientStructure s G ρ hover hcover) :=
  pullback.lift
    (s2_invariantAffineQuotientMap X G ρ (s2_invariantAffineOpenInf X G ρ U V) U (by change U.val ⊓ V.val ≤ U.val; exact inf_le_left))
    (s2_invariantAffineQuotientMap X G ρ (s2_invariantAffineOpenInf X G ρ U V) V (by change U.val ⊓ V.val ≤ V.val; exact inf_le_right))
    (by simp only [← Category.assoc, s2_invariantAffineQuotientMap_gluedι])

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual quotient overlap morphism into the relative chart product is a monomorphism. -/
theorem s2_quotientOverlapPair_mono {X S : Scheme.{0}} [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [IsAffine S]
    (s : X ⟶ S) (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hover : ∀ g : G, (ρ g).asIso.hom ≫ s = s)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val)
    (U V : s2_InvariantAffineOpen X G ρ) : Mono (s2_quotientOverlapPair s G ρ hover hcover U V) := by
  let W := s2_invariantAffineOpenInf X G ρ U V
  have hWU : W ≤ U := by change U.val ⊓ V.val ≤ U.val; exact inf_le_left
  haveI : IsOpenImmersion (s2_invariantAffineQuotientMap X G ρ W U hWU) :=
    s2_invariantAffineDiagram_map_openImmersion X G ρ (homOfLE hWU)
  constructor
  intro Z a b hab
  have he := congrArg (fun k => k ≫ pullback.fst
    (s2_invariantAffineGluedι X G ρ U ≫ s2_gluedQuotientStructure s G ρ hover hcover)
    (s2_invariantAffineGluedι X G ρ V ≫ s2_gluedQuotientStructure s G ρ hover hcover)) hab
  simp only [Category.assoc, s2_quotientOverlapPair, pullback.lift_fst] at he
  exact (cancel_mono (s2_invariantAffineQuotientMap X G ρ W U hWU)).mp he

/-- Each actual affine chart quotient projection respects the induced base map. -/
theorem s2_invariantAffineProjection_base {X S : Scheme.{0}} [IsIntegral X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [IsAffine S]
    (s : X ⟶ S) (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (hover : ∀ g : G, (ρ g).asIso.hom ≫ s = s)
    (hcover : ∀ x : X, ∃ U : s2_InvariantAffineOpen X G ρ, x ∈ U.val)
    (U : s2_InvariantAffineOpen X G ρ) :
    U.val.ι ≫ s = s2_invariantAffineProjection X G ρ U ≫
      (s2_invariantAffineGluedι X G ρ U ≫ s2_gluedQuotientStructure s G ρ hover hcover) := by
  calc
    U.val.ι ≫ s = U.val.ι ≫ (s2_gluedQuotientMap X G ρ hcover ≫
        s2_gluedQuotientStructure s G ρ hover hcover) :=
      congrArg (fun k => U.val.ι ≫ k) (s2_gluedQuotientStructure_fac s G ρ hover hcover).symm
    _ = _ := by rw [← Category.assoc, s2_gluedQuotientMap_ι, Category.assoc]

end HodgeLean.Foundations.Program
