import HodgeLean.Foundations.Program.SchoenTowerL1bPrincipalNeighborhoods
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerPrincipal
import Mathlib.AlgebraicGeometry.Properties

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Nonzero local equations for finitely many ideals persist on a common affine neighborhood. -/
theorem s2v_l1b_simultaneous_nonzero_principal_neighborhood
    (X : Scheme) [IsIntegral X] {J : Type*} [Finite J]
    (I : J → X.IdealSheafData) (x : X) (V : X.Opens) (hxV : x ∈ V)
    (hI : ∀ j, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ g : Γ(X, U), (I j).ideal U = Ideal.span {g} ∧ g ≠ 0) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ V ∧
      ∃ g : J → Γ(X, U), ∀ j, (I j).ideal U = Ideal.span {g j} ∧ g j ≠ 0 := by
  classical
  choose W hxW g hg hgn using hI
  let O : X.Opens := ⟨⋂ j, (W j).1,
    isOpen_iInter_of_finite fun j => (W j).1.isOpen⟩
  have hxO : x ∈ O := Set.mem_iInter.mpr hxW
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ V ⊓ O from ⟨hxV, hxO⟩)
  have hUW (j : J) : U ≤ (W j).1 := fun z hz =>
    Set.mem_iInter.mp (hUV hz).2 j
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  refine ⟨⟨U, hU⟩, hxU, fun z hz => (hUV hz).1,
    (fun j => (X.presheaf.map (homOfLE (hUW j)).op).hom (g j)), ?_⟩
  intro j
  refine ⟨s2v_l1b_principal_restrict X (I j) ⟨U, hU⟩ (W j) (hUW j) (g j) (hg j), ?_⟩
  intro hz
  apply hgn j
  exact map_injective_of_isIntegral X (homOfLE (hUW j))
    (hz.trans (map_zero (X.presheaf.map (homOfLE (hUW j)).op).hom).symm)

/-- Local rank-one ideal trivializations give simultaneous nonzero equations near the specified point. -/
theorem s2v_l1b_simultaneous_cartier_equations
    (X : Scheme) [IsIntegral X] {J : Type*} [Finite J]
    (I : J → X.IdealSheafData) (x : X) (V : X.Opens) (hxV : x ∈ V)
    (hI : ∀ j, ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty ((I j).ideal U ≃ₗ[Γ(X, U)] Γ(X, U))) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ V ∧
      ∃ g : J → Γ(X, U), ∀ j, (I j).ideal U = Ideal.span {g j} ∧ g j ≠ 0 := by
  apply s2v_l1b_simultaneous_nonzero_principal_neighborhood X I x V hxV
  intro j
  obtain ⟨U, hxU, ⟨e⟩⟩ := hI j
  haveI : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  obtain ⟨g, hg, hreg⟩ := s2v_l1b_generator_of_ideal_trivialization ((I j).ideal U) e
  refine ⟨U, hxU, g, hg, ?_⟩
  intro hz
  have he : (0 : Γ(X, U)) * g = 1 * g := by rw [hz, mul_zero, mul_zero]
  exact zero_ne_one (hreg he)

end HodgeLean.Foundations.Program
