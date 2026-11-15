import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Pullback of sections in an invariant actual ideal -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Sections in an invariant actual ideal remain in that ideal under pullback to an invariant affine chart.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.5. -/
theorem s2e_invariant_ideal_section_pullback
    {X : Scheme} (I : X.IdealSheafData) (u : X ⟶ X) [IsIso u]
    (hu : I.map u = I) (U : X.affineOpens) (hU : U.1 ≤ u ⁻¹ᵁ U.1)
    (s : Γ(X, U.1)) (hs : s ∈ I.ideal U) :
    (u.appLE U.1 U.1 hU).hom s ∈ I.ideal U := by
  let V : X.affineOpens := ⟨u ⁻¹ᵁ U.1, U.2.preimage u⟩
  have hm : (u.app U.1).hom s ∈ I.ideal V := by
    change s ∈ (I.ideal V).comap (u.app U.1).hom
    rw [← Scheme.IdealSheafData.ideal_map_of_isAffineHom, hu]
    exact hs
  rw [← I.map_ideal (show U ≤ V from hU)]
  exact Ideal.mem_map_of_mem (X.presheaf.map (homOfLE hU).op).hom hm

end HodgeLean.Foundations.Program
