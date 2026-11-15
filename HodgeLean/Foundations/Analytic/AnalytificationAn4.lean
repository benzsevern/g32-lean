import HodgeLean.Foundations.Analytic.AnalytificationDefs

noncomputable section

open Set Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ComplexPoint

namespace HodgeLean.Foundations.Analytic

lemma AnalytificationAn4_cuspParam_isEmbedding :
    IsEmbedding (fun z : ℂ ↦ ![z ^ 2, z ^ 3]) := by
  let F : ℂ → (Fin 2 → ℂ) := fun z ↦ ![z ^ 2, z ^ 3]
  have hF : Continuous F := by
    fun_prop
  have hproper : IsProperMap F := by
    apply isProperMap_of_comp_of_t2 hF (continuous_apply 0)
    convert (Polynomial.X ^ 2 : Polynomial ℂ).isProperMap_eval (by simp) using 1
    funext z
    simp [F]
  have hinj : Function.Injective F := by
    intro z w h
    have h2 : z ^ 2 = w ^ 2 := congr_fun h 0
    have h3 : z ^ 3 = w ^ 3 := congr_fun h 1
    by_cases hz : z = 0
    · subst z
      norm_num at h2
      exact (sq_eq_zero_iff.mp h2.symm).symm
    · calc
        z = z ^ 3 / z ^ 2 := by field_simp
        _ = w ^ 3 / w ^ 2 := by rw [h2, h3]
        _ = w := by
          have hw : w ≠ 0 := by
            intro hw
            subst w
            norm_num at h2
            exact hz h2
          field_simp
  exact (IsClosedEmbedding.of_continuous_injective_isClosedMap
    hF hinj hproper.isClosedMap).isEmbedding

lemma AnalytificationAn4_cuspPolynomial_deriv_zero
    (p : MvPolynomial (Fin 2) ℂ) :
    HasDerivAt (fun z : ℂ ↦ MvPolynomial.eval ![z ^ 2, z ^ 3] p) 0 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const (x := (0 : ℂ)) a
  | add p q hp hq =>
      convert hp.add hq using 1
      · funext z; simp
      · simp
  | mul_X p i hp =>
      fin_cases i
      · have hpow : HasDerivAt (fun z : ℂ ↦ z ^ 2) 0 0 := by
          have hid : HasDerivAt (fun z : ℂ ↦ z) 1 0 := hasDerivAt_id 0
          convert hid.pow 2 using 1 <;> norm_num
        have h := hp.mul hpow
        convert h using 1
        · funext z; simp
        · simp
      · have hpow : HasDerivAt (fun z : ℂ ↦ z ^ 3) 0 0 := by
          have hid : HasDerivAt (fun z : ℂ ↦ z) 1 0 := hasDerivAt_id 0
          convert hid.pow 3 using 1 <;> norm_num
        have h := hp.mul hpow
        convert h using 1
        · funext z; simp
        · simp

lemma AnalytificationAn4_cuspChart_isEmbedding :
    IsEmbedding (f4_cuspChart.dom.domRestrict f4_cuspChart.toFun) := by
  have he := (affineSpaceHomeomorph (Fin 1)).isEmbedding
  have hp := AnalytificationAn4_cuspParam_isEmbedding
  rw [show f4_cuspChart.dom = univ by
    ext z
    change (z.underlying ∈ (⊤ : (f4_affineSpace 1).left.Opens)) ↔ z ∈ univ
    simp]
  have hfull : IsEmbedding f4_cuspChart.toFun := by
    have hparam := hp.comp (Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).isEmbedding
    dsimp only [f4_cuspChart]
    have hfun :
        ({ U := ⟨⊤, isAffineOpen_top _⟩, n := 2,
            coord := ![AffineSpace.coord (Spec ↧ℂ) 0 ^ 2,
              AffineSpace.coord (Spec ↧ℂ) 0 ^ 3], k := 1,
            eqn := ![MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2] } :
          f4_RawChart (f4_affineSpace 1)).toFun =
          ((fun z : ℂ ↦ ![z ^ 2, z ^ 3]) ∘
            (Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)) ∘
            (affineSpaceHomeomorph (Fin 1))) := by
      funext z
      ext i
      fin_cases i <;>
        simp only [f4_RawChart.toFun, Matrix.cons_val_zero, Matrix.cons_val_one,
          Function.comp_apply, Homeomorph.piUnique_apply, affineSpaceHomeomorph,
          affineSpaceEquiv_apply] <;>
        rw [evaluate_top_eq_appTop] <;> simp
    rw [hfun]
    exact hparam.comp he
  exact hfull.comp IsEmbedding.subtypeVal

lemma AnalytificationAn4_cuspParam_range :
    (fun z : ℂ ↦ ![z ^ 2, z ^ 3]) '' univ =
      an_zeroLocus univ (fun w : Fin 2 → ℂ ↦ ![w 0 ^ 3 - w 1 ^ 2]) := by
  ext w
  constructor
  · rintro ⟨z, -, rfl⟩
    simp [an_zeroLocus]
    ring
  · intro hw
    have heq : w 0 ^ 3 = w 1 ^ 2 := by
      simpa [an_zeroLocus, sub_eq_zero] using congr_fun hw.2 0
    by_cases hx : w 0 = 0
    · have hy : w 1 = 0 := by
        rw [hx] at heq
        norm_num at heq
        exact sq_eq_zero_iff.mp heq.symm
      refine ⟨0, mem_univ _, ?_⟩
      funext i
      fin_cases i <;> simp [hx, hy]
    · refine ⟨w 1 / w 0, mem_univ _, ?_⟩
      funext i
      fin_cases i
      · change (w 1 / w 0) ^ 2 = w 0
        field_simp [hx]
        exact heq.symm
      · change (w 1 / w 0) ^ 3 = w 1
        field_simp [hx]
        rw [heq]
        ring

end HodgeLean.Foundations.Analytic
