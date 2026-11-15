import HodgeLean.Foundations.Program.G32Native.CanonicalCoefficientForms

/-! # The exact canonical divisor over the marked Abel component -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native

/-- The marked homogeneous form supplies an exact divisor tuple over the original sheet. -/
theorem canonical_abel_marked_divisor_tuple (G : CanonicalAbelGeometry) (x : ComplexPoint G.Q) :
    ∃ z : Fin (2 * G.k) → ComplexPoint G.Z,
      b4c_divForm (hE := Module.finrank_fin_fun (n := 1) ℂ)
        (canonicalCoefficientForm G (g32n_homogeneousLine G.k G.eQ x).rep).val =
          ∑ i, Finsupp.single (z i) (1 : ℤ) ∧
      Point.map G.γ (s2_lift (2 * G.k) z) = Point.map G.β (Point.map G.ι x) := by
  letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint G.Z)) :=
    Module.finite_of_finrank_pos (by rw [G.hd]; omega)
  let θ := canonicalCoefficientForm G (g32n_homogeneousLine G.k G.eQ x).rep
  have hθ : θ ≠ 0 := (canonicalCoefficientForm G).map_ne_zero_iff.mpr
    (g32n_homogeneousLine G.k G.eQ x).rep_nonzero
  obtain ⟨z, hz⟩ := s2e_holomorphic_divisor_exists_tuple
    (Module.finrank_fin_fun (n := 1) ℂ) G.k (by rw [G.hd]; omega) θ hθ
  refine ⟨z, hz, ?_⟩
  have he := s2e_canonicalQuotientPoint_eq G.Z G.B (2 * G.k) G.γ G.invariantγ G.hg θ hθ z hz
  have hc := congrFun G.canonical (Point.map G.eQ.hom x)
  rw [canonicalCoefficientForm_homogeneous_point G x] at hc
  have hs := congrArg (fun f => Point.map f x) G.square
  change Point.map G.β (Point.map G.ι x) =
    Point.map G.ℓ (Point.map G.eQ.hom x) at hs
  exact he.symm.trans (hc.symm.trans hs.symm)

#print axioms canonical_abel_marked_divisor_tuple
end HodgeLean.Foundations.Program.G32Native
