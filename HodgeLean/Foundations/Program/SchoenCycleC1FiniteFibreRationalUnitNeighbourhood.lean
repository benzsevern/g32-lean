import HodgeLean.Foundations.Program.SchoenCycleC1RationalUnitNeighbourhood
import Mathlib.AlgebraicGeometry.Morphisms.Finite

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Actual rational units along a whole finite scheme fibre persist over
one affine base neighbourhood contained in any specified base open. -/
theorem s2e_c1_finite_fibre_rational_unit_neighbourhood
    {X Y : Scheme} [IsIntegral X] (f : X ⟶ Y) [IsFinite f]
    (y : Y) (U : Y.Opens) (hy : y ∈ U) (t : X.functionField)
    (hlocal : ∀ x : X, f x = y → ∃ u : (X.presheaf.stalk x)ˣ,
      algebraMap (X.presheaf.stalk x) X.functionField (u : _) = t) :
    ∃ V : Y.affineOpens, y ∈ V.1 ∧ V.1 ≤ U ∧
      ∀ x : X, f x ∈ V.1 → ∃ u : (X.presheaf.stalk x)ˣ,
        algebraMap (X.presheaf.stalk x) X.functionField (u : _) = t := by
  classical
  let F := {x : X // f x = y}
  have hloc (x : F) : ∃ W : X.Opens, x.val ∈ W ∧
      ∀ q : X, q ∈ W → ∃ u : (X.presheaf.stalk q)ˣ,
        algebraMap (X.presheaf.stalk q) X.functionField (u : _) = t := by
    obtain ⟨u, hu⟩ := hlocal x.val x.property
    obtain ⟨W, _, _, hxW, v, hv⟩ := s2e_c1_rational_unit_neighbourhood X x.val ⊤ trivial t u hu
    letI : Nonempty W := ⟨⟨x.val, hxW⟩⟩
    refine ⟨W, hxW, ?_⟩
    intro q hq
    refine ⟨Units.map (X.presheaf.germ W q hq).hom.toMonoidHom v, ?_⟩
    change algebraMap (X.presheaf.stalk q) X.functionField
      ((X.presheaf.germ W q hq).hom (v : Γ(X, W))) = t
    rw [X.algebraMap_germ_eq_germToFunctionField]
    exact hv
  choose W hW hunit using hloc
  let O : X.Opens := ⨆ x : F, W x
  let B : Y.Opens := ⟨(f '' (O : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ O.isOpen.isClosed_compl).isOpen_compl⟩
  have hyB : y ∈ B := by
    rintro ⟨x, hx, hxy⟩
    exact hx (Opens.mem_iSup.mpr ⟨⟨x, hxy⟩, hW ⟨x, hxy⟩⟩)
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVB⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ B ⊓ U from ⟨hyB, hy⟩) (B ⊓ U).isOpen
  refine ⟨⟨V, hV⟩, hyV, hVB.trans inf_le_right, ?_⟩
  intro x hx
  have hxO : x ∈ O := by
    by_contra hn
    exact (hVB hx).1 ⟨x, hn, rfl⟩
  obtain ⟨q, hq⟩ := Opens.mem_iSup.mp hxO
  exact hunit q x hq

end HodgeLean.Foundations.Program
