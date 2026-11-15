import HodgeLean.Foundations.Program.G32Native.PairedResidualNativeTowerCoordinates
import HodgeLean.Foundations.Program.G32Native.PairedResidualSuppliedBlowupCharts
import HodgeLean.Foundations.Program.G32Native.PairedResidualChartFibreUnion
import HodgeLean.Foundations.Program.SchoenTowerL1bFlatRegularPair

/-! # Actual affine quotient charts at a retained paired centre -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters AlgebraicGeometry.RegularPairChart
namespace HodgeLean.Foundations.Program.G32Native.FibreC
open HodgeLean.Foundations.Program

/-- At each retained paired centre the supplied blow-up has its two actual binomial charts,
with both original branch ideals and their coefficient maps retained. -/
theorem residual_native_tower_pair_charts
    (Z B₀ : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B₀.left] [Smooth B₀.hom]
    (hdim : TopologicalSpace.dim Z.left = 1) (n r : ℕ)
    (γ : g3_power Z (n + 1) ⟶ B₀) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hinv : ∀ τ, s2_permute Z (n + 1) τ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (n + 1) ⟶ T),
      (∀ τ, s2_permute Z (n + 1) τ ≫ f = f) → ∃! u : B₀ ⟶ T, γ ≫ u = f)
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (B : Fin (r + 1) → Over (Spec ↧ℂ)) (e₀ : B 0 ≅ B₀)
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData)
    (hD₀ : ∀ t, D 0 t = (s2c_branchIdeal Z B₀ n γ (y t)).comap e₀.hom.left)
    (htransform : ∀ (i : Fin r) t, D i.succ t = s2c_strictTransform (b i).left
      (D i.castSucc t) (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩))
    (hcartier : ∀ (i : Fin r) (x : (B i.succ).left),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      ∃ U : (B i.succ).left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap (b i).left).ideal U) ≃ₗ[Γ((B i.succ).left, U)]
          Γ((B i.succ).left, U)))
    (hblowup : ∀ (i : Fin r) (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B i.succ, u ≫ b i = f)
    (i : Fin r) (x : ComplexPoint (B i.castSucc))
    (hx₁ : x.underlying ∈ (D i.castSucc ⟨2 * i.val, by omega⟩).support)
    (hx₂ : x.underlying ∈ (D i.castSucc ⟨2 * i.val + 1, by omega⟩).support) :
    ∃ (U : (B i.castSucc).left.affineOpens) (u v : Γ((B i.castSucc).left, U)),
      x.underlying ∈ U.1 ∧
      (D i.castSucc ⟨2 * i.val, by omega⟩).ideal U = Ideal.span {u} ∧
      (D i.castSucc ⟨2 * i.val + 1, by omega⟩).ideal U = Ideal.span {v} ∧
      ∃ (V₁ V₂ : (B i.succ).left.affineOpens)
        (h₁ : V₁.1 ≤ (b i).left ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ (b i).left ⁻¹ᵁ U.1)
        (e₁ : ring u v ≃+* Γ((B i.succ).left, V₁))
        (e₂ : ring v u ≃+* Γ((B i.succ).left, V₂)),
        V₁.1 ⊔ V₂.1 = (b i).left ⁻¹ᵁ U.1 ∧
        e₁.toRingHom.comp (coeff u v) = ((b i).left.appLE U.1 V₁.1 h₁).hom ∧
        e₂.toRingHom.comp (coeff v u) = ((b i).left.appLE U.1 V₂.1 h₂).hom ∧
        Ideal.span {((b i).left.appLE U.1 V₁.1 h₁).hom (u - v)} =
          Ideal.span {e₁ (ratio u v - 1)} ⊓
            Ideal.span {((b i).left.appLE U.1 V₁.1 h₁).hom v} ∧
        Ideal.span {((b i).left.appLE U.1 V₂.1 h₂).hom (v - u)} =
          Ideal.span {e₂ (ratio v u - 1)} ⊓
            Ideal.span {((b i).left.appLE U.1 V₂.1 h₂).hom u} := by
  classical
  obtain ⟨U, z, f, hxU, het, hD, _⟩ := residual_native_tower_branch_coordinates
    Z B₀ hdim n r γ hsurj hinv hquot y hy B e₀ b D hD₀ htransform hcartier hblowup
      i.castSucc x
  let t₁ : {t : Fin (2 * r) // 2 * i.castSucc.val ≤ t.val ∧
      x.underlying ∈ (D i.castSucc t).support} :=
    ⟨⟨2 * i.val, by omega⟩, by exact ⟨by change 2 * i.val ≤ 2 * i.val; omega, hx₁⟩⟩
  let t₂ : {t : Fin (2 * r) // 2 * i.castSucc.val ≤ t.val ∧
      x.underlying ∈ (D i.castSucc t).support} :=
    ⟨⟨2 * i.val + 1, by omega⟩,
      by exact ⟨by change 2 * i.val ≤ 2 * i.val + 1; omega, hx₂⟩⟩
  have hne : f t₁ ≠ f t₂ := by
    intro he
    have ht := congrArg (fun t => t.val.val) (f.injective he)
    change 2 * i.val = 2 * i.val + 1 at ht
    omega
  obtain ⟨hv, hu⟩ := s2v_l1b_etale_coordinate_pair
    ((B i.castSucc).hom.appLE ⊤ U.1 le_top).hom z het (f t₁) (f t₂) hne
  obtain ⟨hu', hv'⟩ := s2v_l1b_etale_coordinate_pair
    ((B i.castSucc).hom.appLE ⊤ U.1 le_top).hom z het (f t₂) (f t₁) hne.symm
  have hI : (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      D i.castSucc ⟨2 * i.val + 1, by omega⟩).ideal U = Ideal.span {z (f t₁), z (f t₂)} := by
    change (D i.castSucc t₁.val).ideal U ⊔ (D i.castSucc t₂.val).ideal U = _
    rw [hD t₁, hD t₂, ← Ideal.span_union, Set.singleton_union]
  obtain ⟨V₁, V₂, h₁, h₂, e₁, e₂, hc, he₁, he₂⟩ :=
    residual_supplied_blowup_pair_charts (B i.castSucc) (B i.succ) (b i)
      (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔ D i.castSucc ⟨2 * i.val + 1, by omega⟩)
      (hcartier i) (hblowup i) U (z (f t₁)) (z (f t₂)) hI hv hu hu' hv'
  refine ⟨U, z (f t₁), z (f t₂), hxU, hD t₁, hD t₂,
    V₁, V₂, h₁, h₂, e₁, e₂, hc, he₁, he₂, ?_, ?_⟩
  · exact residual_chart_difference_fibre_transport _ _ e₁ _ he₁
  · exact residual_chart_difference_fibre_transport _ _ e₂ _ he₂

#print axioms residual_native_tower_pair_charts
end HodgeLean.Foundations.Program.G32Native.FibreC
