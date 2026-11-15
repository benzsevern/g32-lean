import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.RegularPairEvaluationExt

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The literal chart embedding factors faithfully through the original base field, with its prescribed coefficient and ratio values. -/
theorem regular_pair_chart_base_field_factorization
    {R K L : Type*} [CommRing R] [Field K] [Field L]
    (u v : R) (F : R →+* K) (κ : K →+* L)
    (G : RegularPairChart.ring u v →+* L)
    (hG : G.comp (RegularPairChart.coeff u v) = κ.comp F)
    (hinj : Function.Injective G) (hv : F v ≠ 0) :
    ∃ H : RegularPairChart.ring u v →+* K,
      H.comp (RegularPairChart.coeff u v) = F ∧
      H (RegularPairChart.ratio u v) = F u / F v ∧
      κ.comp H = G ∧ Function.Injective H := by
  obtain ⟨H, hH, _⟩ := RegularPairChart.universal u v F (F u / F v)
    (div_mul_cancel₀ (F u) hv).symm
  have hGc (r : R) : G (RegularPairChart.coeff u v r) = κ (F r) :=
    DFunLike.congr_fun hG r
  have hratio : G (RegularPairChart.ratio u v) = κ (F u / F v) := by
    rw [map_div₀]
    apply (eq_div_iff (by simpa only [map_zero] using κ.injective.ne hv)).mpr
    have h := congrArg G (RegularPairChart.chart_relation u v)
    change G (RegularPairChart.coeff u v u) =
      G (RegularPairChart.ratio u v * RegularPairChart.coeff u v v) at h
    rw [map_mul, hGc, hGc] at h
    exact h.symm
  have hfactor : κ.comp H = G := by
    apply regular_pair_evaluation_ext u v
    · rw [RingHom.comp_assoc, hH.1, hG]
    · change κ (H (RegularPairChart.ratio u v)) = _
      rw [hH.2, hratio]
  refine ⟨H, hH.1, hH.2, hfactor, ?_⟩
  intro a b hab
  apply hinj
  rw [← hfactor]
  exact congrArg κ hab

end AlgebraicGeometry.RamifiedNormalization.StageFour
