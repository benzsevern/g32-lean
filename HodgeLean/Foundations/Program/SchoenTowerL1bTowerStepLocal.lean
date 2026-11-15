import HodgeLean.Foundations.Program.SchoenTowerL1bTowerStepSupported
import HodgeLean.Foundations.Program.SchoenTowerL1bTowerStepOffCentre

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Simultaneous branch coordinates persist through one retained blowup, with
all branches absent at the new point removed from the resulting neighborhood. -/
theorem s2v_l1b_tower_step_local
    (B X : Over (Spec ↧ℂ)) (p : X ⟶ B) {J σ : Type}
    [Fintype J] [DecidableEq σ]
    (D : J → B.left.IdealSheafData) (R P : J → Prop)
    (hPR : ∀ t, P t → R t) (a b : J) (hab : a ≠ b)
    (hPa : ¬ P a) (hPb : ¬ P b) (hRa : R a) (hRb : R b)
    (hcartier : ∀ x : X.left, ∃ V : X.left.affineOpens, x ∈ V.1 ∧
      Nonempty (((((D a ⊔ D b).comap p.left)).ideal V) ≃ₗ[Γ(X.left, V)] Γ(X.left, V)))
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (g : T ⟶ B),
      (∀ x : T.left, ∃ V : T.left.affineOpens, x ∈ V.1 ∧
        Nonempty (((((D a ⊔ D b).comap g.left)).ideal V) ≃ₗ[Γ(T.left, V)] Γ(T.left, V))) →
      ∃! u : T ⟶ X, u ≫ p = g)
    (x : ComplexPoint X)
    (U : B.left.affineOpens) (z : σ → Γ(B.left, U))
    (f : {t // R t ∧ (Point.map p x).underlying ∈ (D t).support} ↪ σ)
    (hxU : (Point.map p x).underlying ∈ U.1)
    (het : (MvPolynomial.eval₂Hom (B.hom.appLE ⊤ U.1 le_top).hom z).Etale)
    (hD : ∀ t, (D t.val).ideal U = Ideal.span {z (f t)})
    (habs : ∀ t, R t → (Point.map p x).underlying ∉ (D t).support → (D t).ideal U = ⊤) :
    ∃ (V : X.left.affineOpens) (w : σ → Γ(X.left, V))
      (g : {t // P t ∧ x.underlying ∈
        (s2c_strictTransform p.left (D t) (D a ⊔ D b)).support} ↪ σ),
      x.underlying ∈ V.1 ∧
      (MvPolynomial.eval₂Hom (X.hom.appLE ⊤ V.1 le_top).hom w).Etale ∧
      (∀ t, (s2c_strictTransform p.left (D t.val) (D a ⊔ D b)).ideal V =
        Ideal.span {w (g t)}) ∧
      (∀ t, P t → x.underlying ∉
        (s2c_strictTransform p.left (D t) (D a ⊔ D b)).support →
        (s2c_strictTransform p.left (D t) (D a ⊔ D b)).ideal V = ⊤) := by
  classical
  by_cases hboth : (Point.map p x).underlying ∈ (D a).support ∧
      (Point.map p x).underlying ∈ (D b).support
  · exact s2v_l1b_tower_step_two_supported B X p D R P hPR a b hab hPa hPb hRa hRb
      hcartier hblowup x hboth.1 hboth.2 U z f hxU het hD habs
  have hI : (D a ⊔ D b).ideal U = ⊤ := by
    change (D a).ideal U ⊔ (D b).ideal U = _
    by_cases ha : (Point.map p x).underlying ∈ (D a).support
    · have hb : (Point.map p x).underlying ∉ (D b).support := fun hb => hboth ⟨ha, hb⟩
      rw [habs b hRb hb, sup_top_eq]
    · rw [habs a hRa ha, top_sup_eq]
  letI := s2v_l1b_blowup_unit_centre_iso B X p (D a ⊔ D b) hcartier hblowup U hI
  obtain ⟨V₀, hV₀, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show x.underlying ∈ p.left ⁻¹ᵁ U.1 from hxU)
  let V : X.left.affineOpens := ⟨V₀, hV₀⟩
  let w : σ → Γ(X.left, V) := fun j => (p.left.appLE U.1 V.1 hVU).hom (z j)
  have he : (MvPolynomial.eval₂Hom (X.hom.appLE ⊤ V.1 le_top).hom w).Etale :=
    s2v_l1b_etale_coordinates_of_restrict B X p U V hVU z het
  let E : {t // P t} → X.left.IdealSheafData := fun t =>
    s2c_strictTransform p.left (D t.val) (D a ⊔ D b)
  let e : {t : {t // P t} // ((Point.map p x).underlying ∈ (D t.val).support)} ↪ σ :=
    { toFun := fun t => f ⟨t.val.val, hPR _ t.val.property, t.property⟩
      inj' := by
        intro t u he
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun t : {t // R t ∧ (Point.map p x).underlying ∈ (D t).support} => t.val) (f.injective he) }
  have hK : ((D a ⊔ D b).comap p.left).ideal V = ⊤ := by
    rw [s2v_l1b_comap_ideal_affine_charts p.left (D a ⊔ D b) U V hVU,
      hI, Ideal.map_top]
  have hE (t : {t : {t // P t} // ((Point.map p x).underlying ∈ (D t.val).support)}) :
      (E t.val).ideal V = Ideal.span {w (e t)} := by
    change (s2c_strictTransform p.left (D t.val.val) (D a ⊔ D b)).ideal V = _
    rw [s2v_l1b_strictTransform_off_centre_chart p.left _ _ V hK,
      s2v_l1b_comap_ideal_affine_charts p.left _ U V hVU,
      hD ⟨t.val.val, hPR _ t.val.property, t.property⟩, Ideal.map_span, Set.image_singleton]
    exact (s2v_l1b_etale_coordinate_radical (X.hom.appLE ⊤ V.1 le_top).hom w he (e t)).radical
  have hu (t : {t // P t}) (ht : ¬ ((Point.map p x).underlying ∈ (D t.val).support)) : (E t).ideal V = ⊤ :=
    s2v_l1b_tower_step_absent_branch p.left (D t.val) (D a ⊔ D b) U V hVU
      (habs _ (hPR _ t.property) ht)
  obtain ⟨W, v, g, hxW, hev, hEW, hunit⟩ :=
    s2v_l1b_refine_supported_coordinates X E (fun t => (Point.map p x).underlying ∈ (D t.val).support) V w e he hE hu x hxV
  let j : {t // P t ∧ x.underlying ∈
      (s2c_strictTransform p.left (D t) (D a ⊔ D b)).support} ↪
      {t : {t // P t} // x.underlying ∈ (E t).support} :=
    { toFun := fun t => ⟨⟨t.val, t.property.1⟩, t.property.2⟩
      inj' := by intro t u h; exact Subtype.ext (congrArg (fun t => t.val.val) h) }
  exact ⟨W, v, j.trans g, hxW, hev, fun t => hEW (j t),
    fun t ht hn => hunit ⟨t, ht⟩ hn⟩

end HodgeLean.Foundations.Program
