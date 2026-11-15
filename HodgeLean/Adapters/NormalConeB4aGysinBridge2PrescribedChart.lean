import HodgeLean.Adapters.NormalConeB4aGysinBridge2OpenCharts
import HodgeLean.Adapters.NormalConeB4aClassHolomorphicCharts
import HodgeLean.Adapters.NormalConeB4aClassChartTransport

/-! # Reformulated bridge of A3-B4a: holomorphic charts with prescribed first coordinates

Regular functions `g₀, …, g_{n−1}` on an open `U` of a complex scheme, vanishing at a complex
point `x` lying in an open of fixed relative dimension `n + c`, whose derivative in the chart of
that open at `x` is surjective, are the first coordinates of a holomorphic chart of the complex
points into `ℂⁿ × ℂᶜ`, centred at `x` and with source inside `U`.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §1.1.5 and §2.2; Dieudonné, *Foundations of
Modern Analysis*, (10.2.5). -/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry IsLocalRing Point Topology Filter
open HodgeLean.Foundations.Analytic
open scoped Manifold ContDiff

/-- Restricting a holomorphic chart to an open keeps it holomorphic. -/
theorem a3b4g_isHolChart_restrOpen {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)}
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q] {r c : ℕ}
    (e : OpenPartialHomeomorph (ComplexPoint (Over.mk q)) ((Fin r → ℂ) × (Fin c → ℂ)))
    (he : a3b4_IsHolChart q e) (W : Set (ComplexPoint (Over.mk q))) (hW : IsOpen W) :
    a3b4_IsHolChart q (e.restrOpen W hW) := by
  have hsub : (e.restrOpen W hW).source ⊆ e.source := fun _ h => h.1
  exact ⟨fun j => anb_isHolFun_restrict _ hsub (he.1 j),
    fun j => anb_isHolFun_restrict _ hsub (he.2 j)⟩

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- Holomorphic charts with prescribed first coordinates. -/
theorem a3b4g_prescribed_chart {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)}
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    (Z₁ : Z.Opens) {n c : ℕ}
    [SmoothOfRelativeDimension (n + c) (ComplexPoint.openScheme (Over.mk q) Z₁).hom]
    [LocallyOfFiniteType (ComplexPoint.openScheme (Over.mk q) Z₁).hom]
    [QuasiCompact (ComplexPoint.openScheme (Over.mk q) Z₁).hom]
    [IsSeparated (ComplexPoint.openScheme (Over.mk q) Z₁).hom]
    (x₁ : ComplexPoint (ComplexPoint.openScheme (Over.mk q) Z₁))
    (U : Z.Opens) (g : Fin n → Γ(Z, U))
    (hxU : Point.map (ComplexPoint.openInclusion (Over.mk q) Z₁) x₁ ∈
      Point.overOpen (X := Over.mk q) U)
    (hg0 : ∀ j, Point.evaluate (X := Over.mk q) U (g j)
      (Point.map (ComplexPoint.openInclusion (Over.mk q) Z₁) x₁) = 0)
    (hsurj : Function.Surjective (fderiv ℂ (fun a j => Point.evaluate (X := Over.mk q) U (g j)
        (Point.map (ComplexPoint.openInclusion (Over.mk q) Z₁)
          ((chartAt (Fin (n + c) → ℂ) x₁).symm a))) (chartAt (Fin (n + c) → ℂ) x₁ x₁))) :
    ∃ Φ : OpenPartialHomeomorph (ComplexPoint (Over.mk q)) ((Fin n → ℂ) × (Fin c → ℂ)),
      a3b4_IsHolChart q Φ ∧ Point.map (ComplexPoint.openInclusion (Over.mk q) Z₁) x₁ ∈ Φ.source ∧
      Φ (Point.map (ComplexPoint.openInclusion (Over.mk q) Z₁) x₁) = 0 ∧
      Φ.source ⊆ Point.overOpen (X := Over.mk q) U ∧
      ∀ z ∈ Φ.source, ∀ j, (Φ z).1 j = Point.evaluate (X := Over.mk q) U (g j) z := by
  classical
  letI : LocallyOfFiniteType (Over.mk q).hom := ‹LocallyOfFiniteType q›
  letI : QuasiCompact (Over.mk q).hom := ‹QuasiCompact q›
  letI : IsSeparated (Over.mk q).hom := ‹IsSeparated q›
  let Y₁ := ComplexPoint.openScheme (Over.mk q) Z₁
  let ι := ComplexPoint.openInclusion (Over.mk q) Z₁
  let χ := chartAt (Fin (n + c) → ℂ) x₁
  set a₀ := χ x₁ with ha₀def
  have hxχ : x₁ ∈ χ.source := mem_chart_source _ x₁
  let Γf : (Fin (n + c) → ℂ) → (Fin n → ℂ) := fun a j =>
    Point.evaluate (X := Over.mk q) U (g j) (Point.map ι (χ.symm a))
  have hΓeq : ∀ a j, Γf a j = Point.evaluate (X := Y₁) (ι.left ⁻¹ᵁ U) (ι.left.app U (g j))
      (χ.symm a) := fun a j => Point.evaluate_map ι U (g j) _
  have hΓan : AnalyticAt ℂ Γf a₀ := by
    rw [analyticAt_pi_iff]
    intro j
    have h := ComplexPoint.analyticAt_localChart_symm_evaluate Y₁ (n + c) x₁ (χ.map_source hxχ)
      (ι.left ⁻¹ᵁ U) (ι.left.app U (g j)) (by
        change χ.symm a₀ ∈ _
        rw [ha₀def, χ.left_inv hxχ]
        exact hxU)
    convert h using 1
    funext a
    exact hΓeq a j
  obtain ⟨B, hB⟩ := (fderiv ℂ Γf a₀).exists_right_inverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  obtain ⟨e₀, ha₀, he₀1, he₀an, he₀inv, L, hL⟩ := a3b4g_analytic_splitSubmersion_chart hΓan B hB
  have hker : Module.finrank ℂ (fderiv ℂ Γf a₀).ker = c := by
    have h := LinearMap.finrank_range_add_finrank_ker ((fderiv ℂ Γf a₀ :
      (Fin (n + c) → ℂ) →L[ℂ] (Fin n → ℂ)) : (Fin (n + c) → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h
    simp only [Module.finrank_fin_fun] at h
    change Module.finrank ℂ (LinearMap.ker _) = c
    omega
  let K₂ : (fderiv ℂ Γf a₀).ker ≃L[ℂ] (Fin c → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [hker, Module.finrank_fin_fun])
  let κ₀ : Fin c → ℂ := K₂ (e₀ a₀).2
  let A : ((Fin n → ℂ) × (fderiv ℂ Γf a₀).ker) ≃ₜ ((Fin n → ℂ) × (Fin c → ℂ)) :=
    (Homeomorph.refl _).prodCongr (K₂.toHomeomorph.trans (Homeomorph.subRight κ₀))
  let ΦY : OpenPartialHomeomorph (ComplexPoint Y₁) ((Fin n → ℂ) × (Fin c → ℂ)) :=
    χ.trans (e₀.trans A.toOpenPartialHomeomorph)
  have hΦYapply : ∀ p, ΦY p = ((e₀ (χ p)).1, K₂ (e₀ (χ p)).2 - κ₀) := fun p => rfl
  have hx₁ : x₁ ∈ ΦY.source := by
    simp only [ΦY, OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      Set.preimage_univ, Set.inter_univ]
    exact ⟨hxχ, ha₀⟩
  have hcont : ContMDiffAt 𝓘(ℂ, Fin (n + c) → ℂ) 𝓘(ℂ, (Fin n → ℂ) × (Fin c → ℂ)) ω ΦY x₁ := by
    have hX : ContMDiffAt 𝓘(ℂ, Fin (n + c) → ℂ) 𝓘(ℂ, Fin (n + c) → ℂ) ω χ x₁ :=
      (contMDiffOn_chart (I := 𝓘(ℂ, Fin (n + c) → ℂ)) (n := ω) (x := x₁)).contMDiffAt
        (χ.open_source.mem_nhds hxχ)
    have hE : ContMDiffAt 𝓘(ℂ, Fin (n + c) → ℂ)
        𝓘(ℂ, (Fin n → ℂ) × (fderiv ℂ Γf a₀).ker) ω e₀ (χ x₁) :=
      he₀an.contDiffAt.contMDiffAt
    let Alin : ((Fin n → ℂ) × (fderiv ℂ Γf a₀).ker) →L[ℂ] ((Fin n → ℂ) × (Fin c → ℂ)) :=
      (ContinuousLinearMap.id ℂ (Fin n → ℂ)).prodMap K₂.toContinuousLinearMap
    have hAeq : (A : ((Fin n → ℂ) × (fderiv ℂ Γf a₀).ker) → ((Fin n → ℂ) × (Fin c → ℂ))) =
        fun p => Alin p - (0, κ₀) := by
      funext p
      ext <;> simp [A, Alin]
    have hA : ContMDiffAt 𝓘(ℂ, (Fin n → ℂ) × (fderiv ℂ Γf a₀).ker)
        𝓘(ℂ, (Fin n → ℂ) × (Fin c → ℂ)) ω A (e₀ (χ x₁)) := by
      rw [hAeq]
      exact (Alin.contDiff.sub contDiff_const).contMDiff.contMDiffAt
    show ContMDiffAt _ _ ω (A ∘ (e₀ ∘ χ)) x₁
    exact hA.comp x₁ (hE.comp x₁ hX)
  obtain ⟨W₀, hW₀, hxW₀, hhol⟩ :=
    a3b4a_classLocal_exists_holomorphic_restriction Y₁ (n + c) n c ΦY x₁ hx₁ hcont
  haveI : Nonempty (ComplexPoint Y₁) := ⟨x₁⟩
  obtain ⟨E, hE, hEsrc, hEval⟩ :=
    a3b4a_classHolomorphicChart_openTransport (Over.mk q) Z₁ n c (ΦY.restrOpen W₀ hW₀) hhol
  refine ⟨E.restrOpen (Point.overOpen (X := Over.mk q) U) (isOpen_overOpen (X := Over.mk q) U),
    a3b4g_isHolChart_restrOpen E hE _ _, ⟨?_, hxU⟩, ?_, fun z hz => hz.2, ?_⟩
  · rw [hEsrc]
    exact ⟨x₁, ⟨hx₁, hxW₀⟩, rfl⟩
  · change E (Point.map ι x₁) = 0
    rw [hEval]
    change ΦY x₁ = 0
    rw [hΦYapply, he₀1]
    ext j
    · change Γf a₀ j = 0
      rw [hΓeq, ha₀def, χ.left_inv hxχ, ← Point.evaluate_map]
      exact hg0 j
    · change (K₂ (e₀ (χ x₁)).2 - κ₀) j = 0
      rw [show κ₀ = K₂ (e₀ (χ x₁)).2 from rfl, sub_self]
      rfl
  · intro z hz j
    have hzE : z ∈ E.source := hz.1
    rw [hEsrc] at hzE
    obtain ⟨p, hp, rfl⟩ := hzE
    change (E (Point.map ι p)).1 j = _
    rw [hEval]
    change (ΦY p).1 j = _
    rw [hΦYapply, he₀1]
    change Γf (χ p) j = _
    have hpχ : p ∈ χ.source := hp.1.1
    simp only [Γf, χ.left_inv hpχ]
    rfl

end HodgeLean.Adapters
