import HodgeLean.Foundations.Program.SchoenCycleCurveStalkJets
import HodgeLean.Foundations.Program.SchoenCycleAffineStalkJets

/-! # Regular affine parameters for actual curve jets -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Any stalk element has an exact representative on an affine neighbourhood
contained in a prescribed open neighbourhood.
Source: Hartshorne, Algebraic Geometry, II.1 and II.2, affine bases and stalks. -/
theorem s2e_affine_germ_representative (X : Scheme) (p : X)
    (U : X.Opens) (hp : p ∈ U) (r : X.presheaf.stalk p) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : V ≤ U) (hV : p ∈ V)
      (s : Γ(X, V)), (X.presheaf.germ V p hV).hom s = r := by
  obtain ⟨W, hW, s, hs⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hV, hpV, hsub⟩ := exists_isAffineOpen_mem_and_subset (show p ∈ U ⊓ W from ⟨hp, hW⟩)
  let i : V ⟶ W := homOfLE (fun _ h => (hsub h).2)
  refine ⟨V, hV, (fun _ h => (hsub h).1), hpV, X.presheaf.map i.op s, ?_⟩
  change (X.presheaf.map i.op ≫ X.presheaf.germ V p hpV).hom s = r
  rw [X.presheaf.germ_res]
  exact hs

/-- An actual curve point has a regular parameter on an arbitrarily small
affine neighbourhood, giving polynomial coordinates at every finite order.
Source: Hartshorne, Algebraic Geometry, II.8, smooth curve local rings;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_smooth_curve_affine_parameter
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (p : ComplexPoint X) (U : X.left.Opens) (hp : p.underlying ∈ U) :
    let R := X.left.presheaf.stalk p.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p.underlying).toAlgebra
    ∃ (V : X.left.Opens) (_ : IsAffineOpen V) (_ : V ≤ U)
      (hV : p.underlying ∈ V) (s : Γ(X.left, V)),
      let t := (X.left.presheaf.germ V p.underlying hV).hom s
      Irreducible t ∧ IsLocalRing.maximalIdeal R = Ideal.span {t} ∧
        ∀ N : ℕ, Nonempty ((Polynomial ℂ ⧸ Ideal.span {(Polynomial.X ^ N : Polynomial ℂ)})
          ≃ₐ[ℂ] (R ⧸ Ideal.span {t ^ N})) := by
  let R := X.left.presheaf.stalk p.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p.underlying).toAlgebra
  obtain ⟨t, ht, hm, hc⟩ := s2e_smooth_curve_stalk_finite_jet_coordinates X p
  obtain ⟨V, hV, hVU, hpV, s, hs⟩ := s2e_affine_germ_representative X.left
    p.underlying U hp t
  refine ⟨V, hV, hVU, hpV, s, ?_⟩
  dsimp only
  rw [hs]
  exact ⟨ht, hm, hc⟩

end HodgeLean.Foundations.Program
