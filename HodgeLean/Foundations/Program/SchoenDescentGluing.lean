import HodgeLean.Foundations.Program.SchoenDescentCompatibility

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Compatible local descents on a target-open cover glue to a global factorization. -/
theorem s2_descent_of_openCover {X Y T : Scheme.{0}} (q : X ⟶ Y) [Surjective q]
    (hq : ∀ x : X, Function.Injective (q.stalkMap x)) (f : X ⟶ T)
    {I : Type} (U : I → Y.Opens) (hU : TopologicalSpace.IsOpenCover U)
    (d : ∀ i, (U i).toScheme ⟶ T)
    (hd : ∀ i, (q ∣_ U i) ≫ d i = (q ⁻¹ᵁ U i).ι ≫ f) :
    ∃ e : Y ⟶ T, q ≫ e = f := by
  let C := Y.openCoverOfIsOpenCover U hU
  have hcompat : ∀ i j : I, pullback.fst (U i).ι (U j).ι ≫ d i =
      pullback.snd (U i).ι (U j).ι ≫ d j := by
    intro i j
    have H := isPullback_opens_inf (U i) (U j)
    apply (cancel_epi H.isoPullback.hom).mp
    simp only [← Category.assoc, H.isoPullback_hom_fst, H.isoPullback_hom_snd]
    exact s2_localDescent_compatible q hq f (U i) (U j) (d i) (d j) (hd i) (hd j)
  let e := C.glueMorphisms d hcompat
  refine ⟨e, ?_⟩
  let C' := X.openCoverOfIsOpenCover (fun i => q ⁻¹ᵁ U i) (hU.comap q.base.hom)
  apply C'.hom_ext
  intro i
  change (q ⁻¹ᵁ U i).ι ≫ (q ≫ e) = (q ⁻¹ᵁ U i).ι ≫ f
  rw [← Category.assoc, ← morphismRestrict_ι q (U i), Category.assoc]
  have he : (U i).ι ≫ e = d i := C.ι_glueMorphisms d hcompat i
  rw [he, hd i]

end HodgeLean.Foundations.Program
