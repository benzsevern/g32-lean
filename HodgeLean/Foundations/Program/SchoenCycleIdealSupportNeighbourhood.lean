import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! # Affine unit ideals away from support -/
noncomputable section
open AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Away from its support an actual ideal sheaf has a unit ideal on an affine neighbourhood.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.5. -/
theorem s2e_affine_ideal_eq_top_of_not_mem_support
    {X : Scheme} (I : X.IdealSheafData) (x : X) (hx : x ∉ I.support) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ I.ideal U = ⊤ := by
  let W : X.Opens := ⟨(I.support : Set X)ᶜ, I.support.isClosed.isOpen_compl⟩
  obtain ⟨U, hU, hxU, hsub⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ W from hx)
  refine ⟨⟨U, hU⟩, hxU, ?_⟩
  apply PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have he := hU.fromSpec_image_zeroLocus (I.ideal ⟨U, hU⟩)
  have hm : hU.fromSpec p ∈ I.support :=
    (I.zeroLocus_inter_subset_supportSet ⟨U, hU⟩) (he ▸ Set.mem_image_of_mem _ hp)
  have hpU : hU.fromSpec p ∈ U := (Set.ext_iff.mp hU.range_fromSpec _).mp ⟨p, rfl⟩
  exact (hsub hpU) hm

end HodgeLean.Foundations.Program
