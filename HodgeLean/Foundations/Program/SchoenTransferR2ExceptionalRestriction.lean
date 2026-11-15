import HodgeLean.Foundations.Program.SchoenTowerChecks
import HodgeLean.Foundations.Program.SchoenCycleIntersectionDefs

/-! # Primitive restriction to an actual exceptional preimage

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- Composition of the retained morphisms gives contravariant composition on cohomology.
Source: Hatcher, Algebraic Topology, §3.1, functoriality of singular cochains.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_pullback_comp (R : Type) [CommRing R]
    {X Y Z : Over (Spec ↧ℂ)} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    s2e_pullback R (f ≫ g) n = (s2e_pullback R f n).comp (s2e_pullback R g n) := by
  change cohomologyMap R n
    ((TopCat.ofHom (Point.continuousMap f)) ≫ (TopCat.ofHom (Point.continuousMap g))) = _
  exact cohomologyMap_comp R n _ _

/-- Exceptional primitive vanishing kills restriction of a primitive eigenvector
along every actual component morphism factoring through that exceptional preimage.
Source: Schoen (1988), Lemma 2.6, p. 18, the exceptional-preimage square.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_exceptional_eigen_restriction_zero
    {W B E V Q : Over (Spec ↧ℂ)} (β : W ⟶ B) (j : E ⟶ B)
    (d : W ⟶ W) (hd : d ≫ β = β) (f : W ⟶ V) (d₀ : V ⟶ V)
    (hf : d ≫ f = f ≫ d₀)
    (ρ : Q ⟶ s2b_preimage β j) (ι : Q ⟶ W)
    (hρ : ρ ≫ s2b_toCover β j = ι)
    (m n : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)
    (hvanish : ∀ z : Cohomology ℂ (TopCat.of (ComplexPoint (s2b_preimage β j))) n,
      s2b_preimageCohomologyDeck β j d hd n z = ζ • z → z = 0)
    (u : Cohomology ℂ (TopCat.of (ComplexPoint V)) n)
    (hu : s2e_pullback ℂ d₀ n u = ζ • u) :
    s2e_pullback ℂ (ι ≫ f) n u = 0 := by
  let z := s2e_pullback ℂ (s2b_toCover β j ≫ f) n u
  have hsquare : s2b_preimageDeck β j d hd ≫ (s2b_toCover β j ≫ f) =
      (s2b_toCover β j ≫ f) ≫ d₀ := by
    have hs : s2b_preimageDeck β j d hd ≫ s2b_toCover β j = s2b_toCover β j ≫ d :=
      CategoryTheory.Limits.pullback.lift_fst _ _ _
    rw [← Category.assoc, hs, Category.assoc, hf, Category.assoc]
  have hz : s2b_preimageCohomologyDeck β j d hd n z = ζ • z := by
    change s2e_pullback ℂ (s2b_preimageDeck β j d hd) n z = ζ • z
    dsimp only [z]
    rw [← LinearMap.comp_apply, ← s4_assembly_pullback_comp, hsquare,
      s4_assembly_pullback_comp, LinearMap.comp_apply, hu, map_smul]
  have hz0 : z = 0 := hvanish z hz
  rw [← hρ, Category.assoc, s4_assembly_pullback_comp, LinearMap.comp_apply]
  change s2e_pullback ℂ ρ n z = 0
  rw [hz0, map_zero]

#print axioms s4_assembly_exceptional_eigen_restriction_zero
#print axioms s4_assembly_pullback_comp
end HodgeLean.Foundations.Program
