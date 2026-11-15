import HodgeLean.Foundations.Program.SchoenTowerN2a

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

theorem n2b_generic_preimage {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)]
    (e : (f ⁻¹ᵁ U).toScheme ≅ U.toScheme) (he : e.hom = f ∣_ U)
    (x : X) (hx : f x = genericPoint Y) : x = genericPoint X := by
  have hy : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  let z : (f ⁻¹ᵁ U).toScheme := ⟨x, by change f x ∈ U; rw [hx]; exact hy⟩
  have hz : e.hom z = genericPoint U.toScheme := by
    apply U.ι.isOpenEmbedding.injective
    change U.ι (e.hom z) = U.ι (genericPoint U.toScheme)
    rw [genericPoint_eq_of_isOpenImmersion U.ι]
    rw [he]
    exact (morphismRestrict_base_coe f U z).trans hx
  have hz' : z = genericPoint (f ⁻¹ᵁ U).toScheme := by
    apply e.hom.isOpenEmbedding.injective
    rw [hz, genericPoint_eq_of_isOpenImmersion e.hom]
  calc
    x = (f ⁻¹ᵁ U).ι z := rfl
    _ = _ := congrArg (f ⁻¹ᵁ U).ι hz'
    _ = genericPoint X := genericPoint_eq_of_isOpenImmersion _

theorem n2b_dominant_of_generic_mem_range {X Y : Scheme} [IsIntegral Y]
    (f : X ⟶ Y) (x : X) (hx : f x = genericPoint Y) : IsDominant f := by
  rw [isDominant_iff, denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← (genericPoint_spec Y)]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨x, hx⟩)

end HodgeLean.Foundations.Program
