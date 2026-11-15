import HodgeLean.Ported.Hironaka.Scheme.Smooth.AdaptedCoordinates

/-! Relative dimension bounds for smooth closed subschemes. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace HodgeLean.Foundations.Program

/-- A nonempty smooth closed subscheme has relative dimension at most its smooth ambient. -/
theorem g32l4_smooth_subscheme_relativeDimension_le
    {k : Type*} [Field k] [PerfectField k] {X : Scheme}
    (f : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (m n : ℕ)
    [SmoothOfRelativeDimension n f]
    [SmoothOfRelativeDimension m (I.subschemeι ≫ f)] (z : I.subscheme) : m ≤ n := by
  letI := f.stalkAlgebra (I.subschemeι z)
  letI := (I.subschemeι ≫ f).stalkAlgebra z
  have hX := Scheme.ringKrullDim_stalk_add_trdeg_residueField_of_smoothOfRelativeDimension
    f n (I.subschemeι z)
  have hZ := Scheme.ringKrullDim_stalk_add_trdeg_residueField_of_smoothOfRelativeDimension
    (I.subschemeι ≫ f) m z
  simp only at hX hZ
  rw [trdeg_residueField_stalk_subschemeι I f z] at hZ
  have hle := ringKrullDim_le_of_surjective (I.subschemeι.stalkMap z).hom
    (I.subschemeι.stalkMap_surjective z)
  have hsum := add_le_add_right hle
    ((Cardinal.toENat (Algebra.trdeg k (ResidueField (X.presheaf.stalk (I.subschemeι z)))) : ℕ∞) : WithBot ℕ∞)
  rw [add_comm _ (ringKrullDim (I.subscheme.presheaf.stalk z)),
    add_comm _ (ringKrullDim (X.presheaf.stalk (I.subschemeι z))), hZ, hX] at hsum
  exact_mod_cast hsum

end HodgeLean.Foundations.Program
