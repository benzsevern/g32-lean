import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorCoordinatePrime
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorIncidenceSupport
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorCurvePoints
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorFibreGeneric

import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorCoordinateProjection

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters IsLocalRing
namespace HodgeLean.Foundations.Program

/-- A coheight one ordered point with a specified complex coordinate is generic in that coordinate fibre. -/
theorem s2v_l1b_divisor_coordinate_fibre_generic
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1) (n : ℕ)
    (b : ComplexPoint Z) (i : Fin (n + 1))
    (y : (g3_power Z (n + 1)).left) (hy : Order.coheight y = 1)
    (hyi : (g3_proj Z (n + 1) i).left y = b.underlying) :
    y = (s2c_branchInsertion Z n b ≫ s2_permute Z (n + 1) (Equiv.swap 0 i)).left
      (genericPoint (g3_power Z n).left) := by
  classical
  letI : IsIso (s2_permute Z (n + 1) (Equiv.swap 0 i)) :=
    (s2_permuteIso Z (n + 1) (Equiv.swap 0 i)).isIso_hom
  letI : IsClosedImmersion (s2c_branchInsertion Z n b).left :=
    s2v_l1b_divisor_insertion_closedImmersion Z n b
  letI : IsIso (s2_permute Z (n + 1) (Equiv.swap 0 i)).left :=
    ((Over.forget (Spec ↧ℂ)).mapIso (s2_permuteIso Z (n + 1) (Equiv.swap 0 i))).isIso_hom
  let f := (s2c_branchInsertion Z n b ≫ s2_permute Z (n + 1) (Equiv.swap 0 i)).left
  letI : IsClosedImmersion f := by
    change IsClosedImmersion ((s2c_branchInsertion Z n b).left ≫
      (s2_permute Z (n + 1) (Equiv.swap 0 i)).left)
    infer_instance
  have hfcoord (t : (g3_power Z n).left) :
      (g3_proj Z (n + 1) i).left (f t) = b.underlying := by
    have H := congrArg (fun k : (g3_power Z n).left ⟶ Z.left => k t)
      (s2v_l1b_divisor_coordinate_insertion_isPullback Z n b i).w
    change (g3_proj Z (n + 1) i).left (f t) = b.left ((g3_power Z n).hom t) at H
    exact H.trans (congrArg b.left (Subsingleton.elim (α := Spec ↧ℂ) _ (closedPoint ℂ)))
  have hng (t : (g3_power Z n).left) : f t ≠ genericPoint (g3_power Z (n + 1)).left := by
    intro he
    have H := hfcoord t
    rw [he] at H
    letI := s2v_l1b_divisor_projection_dominant Z (n + 1) i
    rw [s2_dominant_genericPoint] at H
    exact s2v_l1b_divisor_curve_complex_ne_generic Z hdimZ b H.symm
  have hmem : y ∈ (f.ker.support : Set _) := by
    change y ∈ (s2c_branchInsertion Z n b ≫ s2_permute Z (n + 1) (Equiv.swap 0 i)).left.ker.support
    rw [s2v_l1b_divisor_coordinate_insertion_kernel, Scheme.IdealSheafData.support_comap]
    change (g3_proj Z (n + 1) i).left y ∈ (b.left.ker.support : Set Z.left)
    rw [s2v_l1b_divisor_complex_point_kernel_support]
    exact hyi
  rw [Scheme.Hom.support_ker, f.isClosedMap.isClosed_range.closure_eq] at hmem
  obtain ⟨t, ht⟩ := hmem
  have htgen := s2v_l1b_divisor_embedded_coheight_one_generic f f.isEmbedding hng t (by rwa [ht])
  rw [← ht, htgen]

/-- At a coheight one ordered point, every coordinate except a specified complex coordinate is generic. -/
theorem s2v_l1b_divisor_other_coordinates_generic
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1) (n : ℕ)
    (b : ComplexPoint Z) (i : Fin (n + 1))
    (y : (g3_power Z (n + 1)).left) (hy : Order.coheight y = 1)
    (hyi : (g3_proj Z (n + 1) i).left y = b.underlying) :
    ∀ j, j ≠ i → (g3_proj Z (n + 1) j).left y = genericPoint Z.left := by
  intro j hji
  rw [s2v_l1b_divisor_coordinate_fibre_generic Z hdimZ n b i y hy hyi]
  letI := s2v_l1b_divisor_coordinate_fibre_projection_dominant Z n b i j hji
  exact s2_dominant_genericPoint ((s2c_branchInsertion Z n b ≫
    s2_permute Z (n + 1) (Equiv.swap 0 i) ≫ g3_proj Z (n + 1) j).left)

end HodgeLean.Foundations.Program
