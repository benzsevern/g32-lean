import HodgeLean.Foundations.HermitianClassC4

noncomputable section
namespace HodgeLean.Foundations.HermitianClass

/-- A nonzero isotropic vector in a regular Hermitian space yields an orthogonal pair
of lengths one and minus one.
Source: Scharlau, *Quadratic and Hermitian Forms*, Chapter 7, §1. -/
theorem hermClass_hyperbolic_pair (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (hn : h.Nondegenerate)
    (x : W) (hx : x ≠ 0) (hxx : h x x = 0) :
    ∃ a b : W, h a a = 1 ∧ h b b = -1 ∧ h a b = 0 := by
  let K := QuadraticAlgebra ℚ (-3) 0
  obtain ⟨y, hxy⟩ := not_forall.mp (fun hall => hx (hn.1 x hall))
  let y0 := (h x y)⁻¹ • y
  have hxy0 : h x y0 = 1 := by
    simp [y0, hxy]
  have hy0x : h y0 x = 1 := by
    simpa [hxy0] using (hh.eq x y0).symm
  have hfix : (starRingEnd K) (h y0 y0) = h y0 y0 := hh.eq y0 y0
  let y1 := y0 - (h y0 y0 / 2) • x
  have hxy1 : h x y1 = 1 := by
    simp [y1, hxy0, hxx]
  have hy1x : h y1 x = 1 := by
    simpa [hxy1] using (hh.eq x y1).symm
  have hy1y1 : h y1 y1 = 0 := by
    simp [y1, hxx, hy0x, hxy0, map_ofNat]
    rw [hfix]
    ring
  let a := x + (1 / 2 : K) • y1
  let b := x - (1 / 2 : K) • y1
  refine ⟨a, b, ?_, ?_, ?_⟩
  · simp [a, hxx, hy1y1, hxy1, hy1x, map_ofNat]
    norm_num
  · simp [b, hxx, hy1y1, hxy1, hy1x, map_ofNat]
    norm_num
  · simp [a, b, hxx, hy1y1, hxy1, hy1x, map_ofNat]

#print axioms hermClass_hyperbolic_pair

/-- Splitting a nonisotropic line leaves a regular orthogonal complement.
Source: Scharlau, *Quadratic and Hermitian Forms*, Chapter 7, §1. -/
theorem hermClass_line_split (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (hn : h.Nondegenerate)
    (x : W) (hxx : h x x ≠ 0) :
    let U : Submodule (QuadraticAlgebra ℚ (-3) 0) W :=
      (QuadraticAlgebra ℚ (-3) 0) ∙ x
    let V := U.orthogonalBilin h
    IsCompl U V ∧ (h.domRestrict₁₂ V V).Nondegenerate := by
  let K := QuadraticAlgebra ℚ (-3) 0
  let U : Submodule K W := K ∙ x
  let V : Submodule K W := U.orthogonalBilin h
  have hdisj : Disjoint U V := by
    exact disjoint_iff.2 (LinearMap.span_singleton_inf_orthogonal_eq_bot h x hxx)
  have hcodisj : Codisjoint U V := by
    rw [codisjoint_iff, eq_top_iff]
    intro y _
    let c : K := (h x x)⁻¹ * h x y
    have hc : h x (y - c • x) = 0 := by
      simp only [map_sub, map_smul, smul_eq_mul, c]
      field_simp
      ring
    refine Submodule.mem_sup.2 ⟨c • x, ?_, y - c • x, ?_, by abel⟩
    · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
    · intro z hz
      rcases Submodule.mem_span_singleton.1 hz with ⟨r, rfl⟩
      simp [hc]
  have hcompl : IsCompl U V := ⟨hdisj, hcodisj⟩
  refine ⟨hcompl, ?_⟩
  let hV := h.domRestrict₁₂ V V
  have hleft : hV.SeparatingLeft := by
    intro z hz
    apply Subtype.ext
    apply hn.1 z
    intro y
    let uv := (U.prodEquivOfIsCompl V hcompl).symm y
    have hy : y = uv.1 + uv.2 := by
      simpa [uv] using (U.prodEquivOfIsCompl V hcompl).apply_symm_apply y |>.symm
    rw [hy]
    have huv : h z uv.1 = 0 := by
      apply hh.isRefl.eq_zero
      exact z.property uv.1 uv.1.property
    rw [map_add, huv, zero_add]
    exact hz uv.2
  refine ⟨hleft, ?_⟩
  intro z hz
  apply hleft z
  intro y
  exact (hh.domRestrict V).isRefl.eq_zero (hz y)

#print axioms hermClass_line_split

/-- A regular Hermitian line gives coordinates consisting of its scalar coordinate and its
orthogonal complement.
Source: Scharlau, *Quadratic and Hermitian Forms*, Chapter 7, §1. -/
theorem hermClass_line_decomposition (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (hn : h.Nondegenerate)
    (x : W) (hxx : h x x ≠ 0) :
    ∃ V : Submodule (QuadraticAlgebra ℚ (-3) 0) W,
      ∃ e : W ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
        (QuadraticAlgebra ℚ (-3) 0 × V),
        (h.domRestrict₁₂ V V).Nondegenerate ∧
          e x = (1, 0) ∧
          ∀ y z, h y z = star (e y).1 * h x x * (e z).1 + h (e y).2 (e z).2 := by
  let K := QuadraticAlgebra ℚ (-3) 0
  let U : Submodule K W := K ∙ x
  let V : Submodule K W := U.orthogonalBilin h
  have hx : x ≠ 0 := ne_zero_of_map hxx
  have hs := hermClass_line_split W h hh hn x hxx
  let ex : K ≃ₗ[K] U := by
    simpa [U] using LinearEquiv.toSpanNonzeroSingleton K W x hx
  let e0 := U.prodEquivOfIsCompl V hs.1
  let ep := ex.symm.prodCongr (LinearEquiv.refl K V)
  let e : W ≃ₗ[K] K × V := e0.symm.trans ep
  have hex : e x = (1, 0) := by
    let xu : U := ⟨x, Submodule.mem_span_singleton_self x⟩
    have hx0 : e0.symm x = (xu, 0) := by
      exact Submodule.prodEquivOfIsCompl_symm_apply_left U V hs.1 xu
    change ep (e0.symm x) = (1, 0)
    rw [hx0]
    apply Prod.ext
    · change ex.symm xu = 1
      have he1 : ex 1 = xu := by
        apply Subtype.ext
        change (1 : K) • x = x
        simp
      rw [← he1, ex.symm_apply_apply]
    · rfl
  refine ⟨V, e, hs.2, hex, fun y z ↦ ?_⟩
  let yu := (U.prodEquivOfIsCompl V hs.1).symm y
  let zu := (U.prodEquivOfIsCompl V hs.1).symm z
  have hy : y = yu.1 + yu.2 := by
    simpa [yu] using (U.prodEquivOfIsCompl V hs.1).apply_symm_apply y |>.symm
  have hz : z = zu.1 + zu.2 := by
    simpa [zu] using (U.prodEquivOfIsCompl V hs.1).apply_symm_apply z |>.symm
  let ry : K := ex.symm yu.1
  let rz : K := ex.symm zu.1
  have hyu : (yu.1 : W) = ry • x := by
    change (yu.1 : W) = (ex (ex.symm yu.1) : U)
    rw [ex.apply_symm_apply]
  have hzu : (zu.1 : W) = rz • x := by
    change (zu.1 : W) = (ex (ex.symm zu.1) : U)
    rw [ex.apply_symm_apply]
  have hyz : h (yu.1 : W) (zu.2 : W) = 0 := by
    exact zu.2.property yu.1 yu.1.property
  have hzy : h (yu.2 : W) (zu.1 : W) = 0 := by
    exact hh.isRefl.eq_zero (yu.2.property zu.1 zu.1.property)
  have hey : e y = (ry, yu.2) := by
    simp [e, ep, e0, yu, ry]
  have hez : e z = (rz, zu.2) := by
    simp [e, ep, e0, zu, rz]
  rw [hey, hez, hy, hz]
  simp only [map_add, LinearMap.add_apply, Prod.fst, Prod.snd]
  rw [hyz, hzy]
  simp only [add_zero, zero_add, hyu, hzu, map_smul, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul]
  ring

#print axioms hermClass_line_decomposition

end HodgeLean.Foundations.HermitianClass
