import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Reformulated bridge of A3-B4a: ambient lifts of finitely many germs

Finitely many elements of a stalk of a closed subscheme are images of germs of ambient sections on
one affine open neighbourhood. Source: Hartshorne, *Algebraic Geometry*, §II.3 (closed immersions
are surjective on stalks) and §II.2 (affine opens form a base). -/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- Finitely many stalk elements on a closed subscheme lift to ambient sections on one affine
open neighbourhood of the image point. Source: Hartshorne, *Algebraic Geometry*, §II.2, §II.3. -/
theorem a3b4g_closed_immersion_affine_germ_lifts_core
    {Z K : Scheme.{0}} (i : K ⟶ Z) [IsClosedImmersion i]
    (w : K) (n : ℕ) (xs : Fin n → K.presheaf.stalk w) :
    ∃ (U : Z.Opens) (_ : IsAffineOpen U) (hw : i w ∈ U)
      (g : Fin n → Γ(Z, U)),
      ∀ j, (i.stalkMap w) (Z.presheaf.germ U (i w) hw (g j)) = xs j := by
  choose y hy using fun j => i.stalkMap_surjective w (xs j)
  choose V hV s hs using fun j => Z.presheaf.exists_germ_eq (y j)
  let W : Z.Opens := ⨅ j, V j
  have hW : i w ∈ W := by
    rw [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
    exact hV
  obtain ⟨_, ⟨U, hU, rfl⟩, hwU, hUW⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open hW W.2
  have hUV : ∀ j, U ≤ V j := fun j => (SetLike.coe_subset_coe.mp hUW).trans (iInf_le _ j)
  refine ⟨U, hU, hwU, fun j => Z.presheaf.map (homOfLE (hUV j)).op (s j), fun j => ?_⟩
  rw [TopCat.Presheaf.germ_res_apply, hs, hy]

end HodgeLean.Adapters
