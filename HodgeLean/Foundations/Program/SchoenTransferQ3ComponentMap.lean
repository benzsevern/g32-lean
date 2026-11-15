import HodgeLean.Foundations.Program.SchoenTransferQ3ComponentDomination

/-! The retained morphism on the reduced support components. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Mapping the actual reduced prime ideal gives the reduced prime ideal of
the image point. -/
theorem s4_q3_primeIdeal_map
    {X W : Scheme} (q : X ⟶ W) (p : X) :
    (ccm3_primeIdeal X p).map q = ccm3_primeIdeal W (q p) := by
  simp only [ccm3_primeIdeal, Scheme.IdealSheafData.map_vanishingIdeal]
  apply congrArg Scheme.IdealSheafData.vanishingIdeal
  apply Closeds.ext
  change closure (q '' closure ({p} : Set X)) = closure ({q p} : Set W)
  rw [closure_image_closure q.continuous, Set.image_singleton]

/-- The specified finite morphism induces a finite surjection between the
actual reduced closures of a source prime and its target image. -/
theorem s4_q3_finite_map_on_reduced_components
    {X W : Scheme} (q : X ⟶ W) [IsFinite q] (p : X) :
    ∃ f : (ccm3_primeIdeal X p).subscheme ⟶ (ccm3_primeIdeal W (q p)).subscheme,
      f ≫ (ccm3_primeIdeal W (q p)).subschemeι =
        (ccm3_primeIdeal X p).subschemeι ≫ q ∧
      IsFinite f ∧ Function.Surjective f := by
  let I := ccm3_primeIdeal X p
  let J := ccm3_primeIdeal W (q p)
  have hIJ : J ≤ I.map q := le_of_eq (s4_q3_primeIdeal_map q p).symm
  let f := I.subschemeMap J q hIJ
  have hf : f ≫ J.subschemeι = I.subschemeι ≫ q :=
    I.subschemeMap_subschemeι J q hIJ
  letI : IsFinite (f ≫ J.subschemeι) := by rw [hf]; infer_instance
  letI : IsFinite f := IsFinite.of_comp f J.subschemeι
  have hI : (I.support : Set X) = closure ({p} : Set X) := by
    dsimp only [I, ccm3_primeIdeal]
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hJ : (J.support : Set W) = closure ({q p} : Set W) := by
    dsimp only [J, ccm3_primeIdeal]
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have himage : q '' (I.support : Set X) = (J.support : Set W) := by
    rw [hI, hJ, ← q.isClosedMap.closure_image_eq_of_continuous q.continuous,
      Set.image_singleton]
  refine ⟨f, hf, inferInstance, ?_⟩
  intro t
  have ht : J.subschemeι t ∈ (J.support : Set W) :=
    J.range_subschemeι ▸ Set.mem_range_self t
  rw [← himage] at ht
  obtain ⟨z, hz, hzt⟩ := ht
  obtain ⟨s, hs⟩ := I.range_subschemeι.symm ▸ hz
  refine ⟨s, J.subschemeι.isClosedEmbedding.injective ?_⟩
  have hfs := congrArg (fun g : I.subscheme ⟶ W => g s) hf
  change J.subschemeι (f s) = q (I.subschemeι s) at hfs
  exact hfs.trans (by rw [hs]; exact hzt)

end HodgeLean.Foundations.Program
