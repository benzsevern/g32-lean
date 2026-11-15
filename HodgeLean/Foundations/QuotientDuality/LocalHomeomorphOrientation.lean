import HodgeLean.Foundations.QuotientDuality.LocalHomeomorphSupport

/-! Transport of coherent local orientations independently of absolute homology. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem homeomorph_transport_coherent_orientation
    (X Y : TopCat.{0}) (H : X ≃ₜ Y) (n : ℕ) (o : LocalRationalOrientation X n) :
    Nonempty (LocalRationalOrientation Y n) := by
  let g (y : Y) := relativeHomologyMap ℚ n (targetPointHomeomorphPairIso H y).hom
    (o.generator (H.symm y))
  have hbij (y : Y) (i : ℕ) : Function.Bijective
      (relativeHomologyMap ℚ i (targetPointHomeomorphPairIso H y).hom) := by
    change Function.Bijective
      (((relativeHomologyFunctor ℚ i).map (targetPointHomeomorphPairIso H y).hom).hom)
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  refine ⟨{
    generator := g
    generates := ?_
    vanishes := ?_
    coherent := ?_ }⟩
  · intro y
    have he : (fun q : ℚ => relativeHomologyMap ℚ n
        (targetPointHomeomorphPairIso H y).hom (q • o.generator (H.symm y))) =
        (fun q : ℚ => q • g y) := by
      funext q
      exact map_smul _ _ _
    change Function.Bijective (fun q : ℚ => q • g y)
    rw [← he]
    exact (hbij y n).comp (o.generates (H.symm y))
  · intro y i hi
    letI := o.vanishes (H.symm y) i hi
    exact (hbij y i).2.subsingleton
  · intro y
    obtain ⟨U, hxU, c, hc⟩ := o.coherent (H.symm y)
    let V : Opens Y := ⟨H '' (U : Set X), H.isOpenMap _ U.isOpen⟩
    have hyV : y ∈ V := ⟨H.symm y, hxU, H.apply_symm_apply y⟩
    let v := relativeHomologyMap ℚ n (homeomorphSupportPairMap H (U : Set X)) c
    refine ⟨V, hyV, v, fun z hz => ?_⟩
    have hx : H.symm z ∈ U := by
      obtain ⟨x, hx, he⟩ := hz
      rw [← he, H.symm_apply_apply]
      exact hx
    have hsq := congrArg (fun f => relativeHomologyMap ℚ n f c)
      (homeomorph_support_restriction_square H (U : Set X) z hz hx)
    rw [relativeHomologyMap_comp, relativeHomologyMap_comp,
      LinearMap.comp_apply, LinearMap.comp_apply] at hsq
    exact hsq.symm.trans ((congrArg
      (relativeHomologyMap ℚ n (targetPointHomeomorphPairIso H z).hom) (hc (H.symm z) hx)))

#print axioms homeomorph_transport_coherent_orientation
end HodgeLean.Foundations.QuotientDuality
