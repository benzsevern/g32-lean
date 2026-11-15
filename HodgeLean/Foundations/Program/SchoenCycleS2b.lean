import HodgeLean.Foundations.Program.SchoenCycleS2bProofs

/-! # Projective residue intersections
Implication from distinct residue coordinates in an adapted coefficient basis to
scheme ideals on projective charts and their global intersections.
Cartier generators and blowup transport are later units.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open Manifold
open scoped ContDiff BigOperators
namespace HodgeLean.Foundations.Program

/-- The actual projective residue ideals pull back to the normalized linear equations.
Source: Schoen (1988), Lemma 2.3(vi), printed pp. 13–14; Lemma 2.4 proof, printed p. 15. -/
theorem s2e_chain_residue_projective_chart
    (k : ℕ) (T : Finset (Fin (k + 1))) (i : Fin (k + 1)) :
    Ideal.map (Scheme.ΓSpecIso
        ↧(MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ)).hom.hom
      (((s2e_s2b_intersectionIdeal k T).comap (s2e_s2b_chart i)).ideal ⟨⊤, isAffineOpen_top _⟩) =
    Ideal.span ((fun j : Fin (k + 1) =>
      if h : j = i then (1 : MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ)
      else MvPolynomial.X ⟨j, h⟩) '' (↑T : Set (Fin (k + 1)))) :=
  s2e_chain_residue_projective_chart_aux k T i

example := @s2e_chain_residue_projective_chart

/-- The local residue intersections glue as a projective scheme of the stated dimension.
Source: Schoen (1988), Lemma 2.3(vi), printed pp. 13–14; Lemma 2.4 proof, printed p. 15. -/
theorem s2e_chain_residue_projective_intersection
    (k : ℕ) (T : Finset (Fin (k + 1))) (hT : T.card ≤ k) :
    Nonempty ((s2e_s2b_intersectionIdeal k T).subscheme ≅
      ProjectiveSpace (Fin (k - T.card + 1)) (Spec ↧ℂ)) :=
  s2e_chain_residue_projective_intersection_aux k T hT

example := @s2e_chain_residue_projective_intersection

/-- All homogeneous coordinates vanishing gives an empty projective intersection.
Source: Schoen (1988), Lemma 2.3(vi), printed pp. 13–14; Lemma 2.4 proof, printed p. 15. -/
theorem s2e_chain_residue_projective_empty
    (k : ℕ) (T : Finset (Fin (k + 1))) (hT : k < T.card) :
    IsEmpty (s2e_s2b_intersectionIdeal k T).subscheme :=
  s2e_chain_residue_projective_empty_aux k T hT

example := @s2e_chain_residue_projective_empty

/-- The vanishing ideal of the actual differential residue locus is the
coordinate hyperplane ideal in an explicitly adapted coefficient basis.
Source: Schoen (1988), Lemma 2.3(iv,vi), printed pp. 13–14. -/
theorem s2e_chain_differential_residue_ideal
    (E C : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (hE : Module.finrank ℂ E = 1) (k r : ℕ)
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (b : (Fin (k + 1) → ℂ) ≃ₗ[ℂ] (b3_HolForm E C × (Fin r → ℂ)))
    (ι : Fin r ↪ Fin (k + 1))
    (hb : ∀ v j, (b v).2 j = v (ι j)) (j : Fin r) :
    Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure
      {p | ∃ (v : Fin (k + 1) → ℂ) (hv : v ≠ 0),
        b4c_res (hE := hE) (s2e_pairedDifferentialLinear hE w (b v)) (x j) = 0 ∧
        p = (vectorToComplexPoint v hv).underlying}) =
      s2e_s2b_residueIdeal k (ι j) :=
  s2e_chain_differential_residue_ideal_aux E C hE k r w x hres b ι hb j

example := @s2e_chain_differential_residue_ideal

end HodgeLean.Foundations.Program
