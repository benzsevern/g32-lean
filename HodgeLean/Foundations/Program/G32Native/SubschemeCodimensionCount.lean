import HodgeLean.Foundations.Program.G32Native.SmoothRelativeDimensionCount
import HodgeLean.Ported.Hironaka.Scheme.Smooth.AdaptedCoordinates

/-! Compare the dimension count of a subscheme with a quotient-stalk codimension. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace HodgeLean.Foundations.Program

/-- Quotient-stalk codimension adds to the subscheme dimension count to give ambient dimension. -/
theorem g32l4_subscheme_dimCount_add_codimension
    {k : Type*} [Field k] [PerfectField k] {X : Scheme}
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : X.IdealSheafData) (r : ℕ)
    (hcodim : ∀ q : I.subscheme,
      ringKrullDim (X.presheaf.stalk (I.subschemeι q) ⧸ I.stalkIdeal (I.subschemeι q)) + r =
        ringKrullDim (X.presheaf.stalk (I.subschemeι q))) (q : I.subscheme) :
    dimCount (I.subschemeι ≫ f) q + r = n := by
  letI := f.stalkAlgebra (I.subschemeι q)
  letI := (I.subschemeι ≫ f).stalkAlgebra q
  have hX := Scheme.ringKrullDim_stalk_add_trdeg_residueField_of_smoothOfRelativeDimension
    f n (I.subschemeι q)
  simp only at hX
  have hq := hcodim q
  rw [ringKrullDim_eq_of_ringEquiv (I.stalkQuotientEquiv q)] at hq
  dsimp only [dimCount]
  rw [trdeg_residueField_stalk_subschemeι I f q, add_right_comm, hq]
  exact hX

end HodgeLean.Foundations.Program
