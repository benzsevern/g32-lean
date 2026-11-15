import HodgeLean.Foundations.Program.SchoenTowerL1bTowerStepCover
import HodgeLean.Foundations.Program.SchoenTowerL1bTowerStepRefinement

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- At a point above both centre branches, simultaneous coordinates for the
remaining branches give simultaneous coordinates for their actual transforms. -/
theorem s2v_l1b_tower_step_two_supported
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
    (ha : (Point.map p x).underlying ∈ (D a).support)
    (hb : (Point.map p x).underlying ∈ (D b).support)
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
  let a' : {t // R t ∧ (Point.map p x).underlying ∈ (D t).support} := ⟨a, hRa, ha⟩
  let b' : {t // R t ∧ (Point.map p x).underlying ∈ (D t).support} := ⟨b, hRb, hb⟩
  have hab' : f a' ≠ f b' := fun he => hab (congrArg Subtype.val (f.injective he))
  let f' : {t : {t // P t} // ((Point.map p x).underlying ∈ (D t.val).support)} → σ := fun t =>
    f ⟨t.val.val, hPR _ t.val.property, t.property⟩
  have hfa : ∀ t, f' t ≠ f a' := by
    intro t he
    have hv := congrArg Subtype.val (f.injective he)
    change t.val.val = a at hv
    exact hPa (hv ▸ t.val.property)
  have hfb : ∀ t, f' t ≠ f b' := by
    intro t he
    have hv := congrArg Subtype.val (f.injective he)
    change t.val.val = b at hv
    exact hPb (hv ▸ t.val.property)
  have hI : (D a ⊔ D b).ideal U = Ideal.span {z (f a'), z (f b')} := by
    change (D a).ideal U ⊔ (D b).ideal U = _
    rw [hD a', hD b', ← Ideal.span_union]
    congr 1
  obtain ⟨V₁, V₂, h₁, h₂, w₁, w₂, hcover, he₁, he₂, hD₁, hD₂⟩ :=
    s2v_l1b_tower_step_coordinate_cover B X p (D a ⊔ D b) hcartier hblowup U z het
      (f a') (f b') hab' hI (fun t : {t : {t // P t} // ((Point.map p x).underlying ∈ (D t.val).support)} => D t.val.val)
      f' hfa hfb (fun t => hD ⟨t.val.val, hPR _ t.val.property, t.property⟩)
  have hx : x.underlying ∈ V₁.1 ∨ x.underlying ∈ V₂.1 := by
    change x.underlying ∈ V₁.1 ⊔ V₂.1
    rw [hcover]
    exact hxU
  let E : {t // P t} → X.left.IdealSheafData := fun t =>
    s2c_strictTransform p.left (D t.val) (D a ⊔ D b)
  let e : {t : {t // P t} // ((Point.map p x).underlying ∈ (D t.val).support)} ↪ σ :=
    { toFun := f'
      inj' := by
        intro t u he
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun t : {t // R t ∧ (Point.map p x).underlying ∈ (D t).support} => t.val) (f.injective he) }
  have finish (V : X.left.affineOpens) (hV : V.1 ≤ p.left ⁻¹ᵁ U.1)
      (w : σ → Γ(X.left, V)) (hxV : x.underlying ∈ V.1)
      (he : (MvPolynomial.eval₂Hom (X.hom.appLE ⊤ V.1 le_top).hom w).Etale)
      (hE : ∀ t, (E t.val).ideal V = Ideal.span {w (e t)}) :
      ∃ (W : X.left.affineOpens) (v : σ → Γ(X.left, W))
        (g : {t // P t ∧ x.underlying ∈
          (s2c_strictTransform p.left (D t) (D a ⊔ D b)).support} ↪ σ),
        x.underlying ∈ W.1 ∧
        (MvPolynomial.eval₂Hom (X.hom.appLE ⊤ W.1 le_top).hom v).Etale ∧
        (∀ t, (s2c_strictTransform p.left (D t.val) (D a ⊔ D b)).ideal W = Ideal.span {v (g t)}) ∧
        (∀ t, P t → x.underlying ∉
          (s2c_strictTransform p.left (D t) (D a ⊔ D b)).support →
          (s2c_strictTransform p.left (D t) (D a ⊔ D b)).ideal W = ⊤) := by
    have hu (t : {t // P t}) (ht : ¬ ((Point.map p x).underlying ∈ (D t.val).support)) : (E t).ideal V = ⊤ :=
      s2v_l1b_tower_step_absent_branch p.left (D t.val) (D a ⊔ D b) U V hV
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
  rcases hx with hx | hx
  · exact finish V₁ h₁ w₁ hx he₁ hD₁
  · exact finish V₂ h₂ w₂ hx he₂ hD₂

end HodgeLean.Foundations.Program
