import HodgeLean.Foundations.QuotientDuality.LocalChartEmbedding

/-! Exact local degree on a common chart domain over a singleton fibre. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

variable {U X Y : TopCat.{0}} (f : X ⟶ Y) (j : U → X)
    (hj : IsOpenEmbedding j) (hk : IsOpenEmbedding (fun z => f (j z)))
    (x : U) (hf : ∀ z, f z = f (j x) → z = j x)

theorem imagePointPairMap_comp_singletonFibre :
    imagePointPairMap (TopCat.ofHom ⟨j, hj.continuous⟩) hj.injective x ≫
      singletonFibrePairMap f (j x) (f (j x)) hf =
    imagePointPairMap
      (TopCat.ofHom ⟨fun z => f (j z), f.hom.continuous.comp hj.continuous⟩)
      hk.injective x := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext z
    rfl
  · ext z
    rfl

theorem singletonFibre_map_lifted_chart_class (d : ℕ)
    (E : OpenPartialHomeomorph U (Fin d → ℂ)) (hx : x ∈ E.source) :
    relativeHomologyMap ℚ (2 * d) (singletonFibrePairMap f (j x) (f (j x)) hf)
      (localClassOfChart d (E.lift_openEmbedding hj) (j x) ⟨x, hx, rfl⟩) =
    localClassOfChart d (E.lift_openEmbedding hk) (f (j x)) ⟨x, hx, rfl⟩ := by
  let J := imagePointPairMap (TopCat.ofHom ⟨j, hj.continuous⟩) hj.injective x
  let F := singletonFibrePairMap f (j x) (f (j x)) hf
  let K := imagePointPairMap
    (TopCat.ofHom ⟨fun z => f (j z), f.hom.continuous.comp hj.continuous⟩)
    hk.injective x
  calc
    relativeHomologyMap ℚ (2 * d) F _ =
        relativeHomologyMap ℚ (2 * d) F
          (relativeHomologyMap ℚ (2 * d) J (localClassOfChart d E x hx)) :=
      congrArg (relativeHomologyMap ℚ (2 * d) F)
        (localClassOfChart_lift_openEmbedding j hj d E x hx).symm
    _ = relativeHomologyMap ℚ (2 * d) K (localClassOfChart d E x hx) := by
      have hcomp := congrArg (fun m => relativeHomologyMap ℚ (2 * d) m
        (localClassOfChart d E x hx)) (imagePointPairMap_comp_singletonFibre f j hj hk x hf)
      simp only [relativeHomologyMap_comp, LinearMap.comp_apply] at hcomp
      convert hcomp using 1 <;> rfl
    _ = _ := localClassOfChart_lift_openEmbedding (fun z => f (j z)) hk d E x hx

#print axioms imagePointPairMap_comp_singletonFibre
#print axioms singletonFibre_map_lifted_chart_class
end HodgeLean.Foundations.QuotientDuality
