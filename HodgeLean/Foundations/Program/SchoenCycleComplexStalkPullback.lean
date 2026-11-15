import HodgeLean.Foundations.Program.SchoenCycleStalkScalars

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual geometric stalk pullback preserves the prescribed complex scalar maps.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
def s2e_complex_stalk_pullback
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    (f : X ⟶ Y) (x : X.left) :
    letI : Algebra ℂ (X.left.presheaf.stalk x) := (HodgeLean.Foundations.Curves.stalkC x).toAlgebra
    letI : Algebra ℂ (Y.left.presheaf.stalk (f.left x)) :=
      (HodgeLean.Foundations.Curves.stalkC (f.left x)).toAlgebra
    Y.left.presheaf.stalk (f.left x) →ₐ[ℂ] X.left.presheaf.stalk x := by
  letI : Algebra ℂ (X.left.presheaf.stalk x) := (HodgeLean.Foundations.Curves.stalkC x).toAlgebra
  letI : Algebra ℂ (Y.left.presheaf.stalk (f.left x)) :=
    (HodgeLean.Foundations.Curves.stalkC (f.left x)).toAlgebra
  exact
    { toRingHom := (f.left.stalkMap x).hom
      commutes' := s2e_stalkMap_complex_scalars X Y f x }

#print axioms s2e_complex_stalk_pullback

/-- Actual complex stalk pullback preserves every power of the actual maximal ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_complex_stalk_pullback_preserves_powers
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    (f : X ⟶ Y) (x : X.left) :
    letI : Algebra ℂ (X.left.presheaf.stalk x) := (HodgeLean.Foundations.Curves.stalkC x).toAlgebra
    letI : Algebra ℂ (Y.left.presheaf.stalk (f.left x)) :=
      (HodgeLean.Foundations.Curves.stalkC (f.left x)).toAlgebra
    ∀ N a, a ∈ IsLocalRing.maximalIdeal (Y.left.presheaf.stalk (f.left x)) ^ N →
      s2e_complex_stalk_pullback X Y f x a ∈ IsLocalRing.maximalIdeal (X.left.presheaf.stalk x) ^ N := by
  intro N a ha
  let φ := (f.left.stalkMap x).hom
  change φ a ∈ IsLocalRing.maximalIdeal (X.left.presheaf.stalk x) ^ N
  have h : (IsLocalRing.maximalIdeal (Y.left.presheaf.stalk (f.left x)) ^ N).map φ ≤
      IsLocalRing.maximalIdeal (X.left.presheaf.stalk x) ^ N := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' (IsLocalRing.map_maximalIdeal_le φ) N
  exact h (Ideal.mem_map_of_mem φ ha)

#print axioms s2e_complex_stalk_pullback_preserves_powers
end HodgeLean.Foundations.Program
