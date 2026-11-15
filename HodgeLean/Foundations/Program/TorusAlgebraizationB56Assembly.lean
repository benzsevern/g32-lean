import HodgeLean.Foundations.Program.TorusAlgebraizationB56Holomorphic
import HodgeLean.Foundations.Program.TorusAlgebraizationB55Analytic
import HodgeLean.Foundations.Analytic.Analytification

/-! # Holomorphy of the theta map and of its inverse, and holomorphic functions

Let `θ : T → X(ℂ)` be a homeomorphism from the torus with `θ ∘ cover = P`, where `P` is the theta
evaluation on the cover. By `b56_theta_contMDiff` and `b56_local_section`, `θ` and `θ⁻¹` are
holomorphic, and a function on an open `U ⊆ X(ℂ)` is holomorphic exactly when its pullback to
the cover is.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Topology Filter
open scoped TensorProduct Manifold ContDiff
open HodgeLean.Foundations.Analytic

namespace HodgeLean.Foundations.Program

variable {Λ : Type} [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
  {F : Submodule ℂ (ℂ ⊗[ℤ] Λ)} {hF : b2_IsWeightOne Λ F} {Q : LinearMap.BilinForm ℤ Λ}

/-- The torus cover identifies points differing by a lattice vector. -/
theorem b56_torusCover_add_lattice (z : b5_V Λ F) (l : Λ) :
    b2_torusCover Λ F (z + b5_lattice Λ F l) = b2_torusCover Λ F z := by
  rw [b55_torusCover_add]
  have h : b2_torusCover Λ F (b5_lattice Λ F l) = 0 := by
    simp only [b2_torusCover, b5_lattice, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearMap.coe_restrictScalars, AddMonoidHom.coe_toIntLinearMap]
    change (QuotientAddGroup.mk ((b2_coordHomeomorph Λ F).symm
      ((b2_coordHomeomorph Λ F) (b2_latticeMap Λ F l))) : b2_torus Λ F) = 0
    rw [Homeomorph.symm_apply_apply, QuotientAddGroup.eq_zero_iff]
    exact ⟨l, rfl⟩
  rw [h, add_zero]

/-- The torus cover is surjective. -/
theorem b56_torusCover_surjective : Function.Surjective (b2_torusCover Λ F) := by
  intro t
  refine ⟨b2_coordHomeomorph Λ F (Quotient.out t), ?_⟩
  simp only [b2_torusCover, Homeomorph.symm_apply_apply]
  exact QuotientAddGroup.out_eq' t

theorem b56_eval_of (s : b5_sections Λ F hF Q 3) :
    (fun w ↦ b5_eval Λ F hF Q w (DirectSum.of _ 1 s)) = s.val := by
  funext w
  simp [b5_eval]

/-- Basepoint freeness of `L³` in the form used by the theta map. -/
theorem b56_bpf_of (h : ∀ z, ∃ s : b5_sections Λ F hF Q 3, s.val z ≠ 0) :
    ∀ z, ∃ t ∈ b5_grade Λ F hF Q 1, b5_eval Λ F hF Q z t ≠ 0 := by
  intro z
  obtain ⟨s, hs⟩ := h z
  refine ⟨DirectSum.of _ 1 s, ⟨s, rfl⟩, ?_⟩
  rw [← congrFun (b56_eval_of s) z] at hs
  exact hs

/-- Separation of tangent vectors by `L³` in the form used by the theta map. -/
theorem b56_tan_of (h : ∀ z v, v ≠ 0 →
      ∃ s : b5_sections Λ F hF Q 3, s.val z = 0 ∧ fderiv ℂ s.val z v ≠ 0) :
    ∀ z v, v ≠ 0 → ∃ s ∈ b5_grade Λ F hF Q 1, b5_eval Λ F hF Q z s = 0 ∧
      fderiv ℂ (fun w ↦ b5_eval Λ F hF Q w s) z v ≠ 0 := by
  intro z v hv
  obtain ⟨s, hs0, hsd⟩ := h z v hv
  refine ⟨DirectSum.of _ 1 s, ⟨s, rfl⟩, ?_, ?_⟩
  · rw [← congrFun (b56_eval_of s) z] at hs0
    exact hs0
  · rw [b56_eval_of s]
    exact hsd

/-- A descent identity on the quotient gives `θ ∘ cover = P`. -/
theorem b56_cover_of {Y : Type*} (θ : b2_torus Λ F → Y) (P : b5_V Λ F → Y)
    (h : ∀ v, θ (QuotientAddGroup.mk v) = P (b2_coord _ v)) (z : b5_V Λ F) :
    θ (b2_torusCover Λ F z) = P z := by
  change θ (QuotientAddGroup.mk ((b2_coordHomeomorph Λ F).symm z)) = _
  rw [h]
  congr 1
  exact (b2_coordHomeomorph Λ F).apply_symm_apply z

variable (hirr : ∀ z, (HomogeneousIdeal.irrelevant (b5_grade Λ F hF Q)).toIdeal.map
      (b5_evalGlobal Λ F hF Q z) = ⊤)
  (P : b5_V Λ F → ComplexPoint (b5_model Λ F hF Q))
  (hP : ∀ z, (P z).left =
    Proj.fromOfGlobalSections (b5_grade Λ F hF Q) (b5_evalGlobal Λ F hF Q z) (hirr z))
  (hbpf : ∀ z, ∃ t ∈ b5_grade Λ F hF Q 1, b5_eval Λ F hF Q z t ≠ 0)
  (htan : ∀ z v, v ≠ 0 → ∃ s ∈ b5_grade Λ F hF Q 1, b5_eval Λ F hF Q z s = 0 ∧
      fderiv ℂ (fun w ↦ b5_eval Λ F hF Q w s) z v ≠ 0)
  (θ : b2_torus Λ F → ComplexPoint (b5_model Λ F hF Q)) (hθ : IsHomeomorph θ)
  (hθP : ∀ z, θ (b2_torusCover Λ F z) = P z)
include hP hbpf htan hθ hθP

/-- Holomorphy of the theta map, of its inverse, and the description of holomorphic functions
by periodic holomorphic functions on the cover.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, Theorem 4.5.1 and §1.1; Mumford,
*Abelian Varieties*, §3. -/
theorem b56_holomorphicFunctions [Smooth (b5_model Λ F hF Q).hom]
    [IsProjective (b5_model Λ F hF Q).hom] [IsIntegral (b5_model Λ F hF Q).left]
    [DiscreteTopology (b2_latticeMap Λ F).range] :
    ContMDiff 𝓘(ℂ, b5_V Λ F) 𝓘(ℂ, Fin (TopologicalSpace.dim (b5_model Λ F hF Q).left) → ℂ)
        ω θ ∧
    ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim (b5_model Λ F hF Q).left) → ℂ) 𝓘(ℂ, b5_V Λ F)
        ω (hθ.homeomorph θ).symm ∧
    ∀ (U : TopologicalSpace.Opens (ComplexPoint (b5_model Λ F hF Q))) (f : U → ℂ),
      (f4_analytification (b5_model Λ F hF Q)).IsHolFun f ↔
        ∃ g : b5_V Λ F → ℂ,
          DifferentiableOn ℂ g (P ⁻¹' (U : Set (ComplexPoint (b5_model Λ F hF Q)))) ∧
          (∀ l z, P z ∈ U → g (z + b5_lattice Λ F l) = g z) ∧
          ∀ z : P ⁻¹' (U : Set (ComplexPoint (b5_model Λ F hF Q))),
            g z = f ⟨P z, z.property⟩ := by
  set d := TopologicalSpace.dim (b5_model Λ F hF Q).left
  haveI := b2_torus_isManifold F
  have hPc : ContMDiff 𝓘(ℂ, b5_V Λ F) 𝓘(ℂ, Fin d → ℂ) ω P :=
    b56_theta_contMDiff hirr P hP hbpf d
  have hcont : Continuous P := b56_continuous hirr P hP hbpf
  have hPopen : IsOpenMap P := by
    have h : P = θ ∘ b2_torusCover Λ F := funext fun z ↦ (hθP z).symm
    rw [h]
    exact hθ.isOpenMap.comp (b2t_torusCover_isCoveringMap (Λ := Λ) (F := F)).isOpenMap
  have hsec := b56_local_section hirr P hP hbpf d htan hPopen
  have hPsurj : ∀ x, ∃ z, P z = x := by
    intro x
    obtain ⟨t, rfl⟩ := hθ.surjective x
    obtain ⟨z, rfl⟩ := b56_torusCover_surjective (F := F) t
    exact ⟨z, (hθP z).symm⟩
  have hPper (z : b5_V Λ F) (l : Λ) : P (z + b5_lattice Λ F l) = P z := by
    rw [← hθP, ← hθP, b56_torusCover_add_lattice]
  have hsymm (z : b5_V Λ F) : (hθ.homeomorph θ).symm (P z) = b2_torusCover Λ F z := by
    rw [← hθP]
    exact (hθ.homeomorph θ).symm_apply_apply _
  refine ⟨?_, ?_, ?_⟩
  · intro t₀
    have hsrc : (chartAt (b5_V Λ F) t₀).source ∈ 𝓝 t₀ :=
      (chartAt (b5_V Λ F) t₀).open_source.mem_nhds (mem_chart_source _ _)
    have hch : ContMDiffAt 𝓘(ℂ, b5_V Λ F) 𝓘(ℂ, b5_V Λ F) ω (chartAt (b5_V Λ F) t₀) t₀ :=
      (contMDiffOn_chart (I := 𝓘(ℂ, b5_V Λ F)) (n := ω) (x := t₀)).contMDiffAt hsrc
    refine ((hPc _).comp t₀ hch).congr_of_eventuallyEq ?_
    filter_upwards [hsrc] with t ht
    simp only [Function.comp_apply]
    rw [← hθP, b55_torusCover_chart _ _ ht]
  · intro x₀
    obtain ⟨z₀, rfl⟩ := hPsurj x₀
    obtain ⟨ψ, hψ0, hψ, hψd⟩ := hsec z₀
    have hcov := b2t_torusCover_contMDiff (Λ := Λ) (F := F)
    refine ((hcov _).comp (P z₀) hψd).congr_of_eventuallyEq ?_
    filter_upwards [hψ] with x hx
    simp only [Function.comp_apply]
    rw [← hx, hsymm, hx]
  · intro U f
    classical
    let G : ComplexPoint (b5_model Λ F hF Q) → ℂ := fun x ↦ if h : x ∈ U then f ⟨x, h⟩ else 0
    have hfG : f = fun x : U ↦ G x := by
      funext x
      simp [G, x.property]
    refine Iff.trans (b := ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω G U) ?_ ?_
    · rw [hfG]
      exact f4_isHolFun_iff_contMDiffOn (b5_model Λ F hF Q) d G U.isOpen
    have hUopen : IsOpen (P ⁻¹' (U : Set (ComplexPoint (b5_model Λ F hF Q)))) :=
      U.isOpen.preimage hcont
    constructor
    · intro hG
      refine ⟨G ∘ P, ?_, ?_, ?_⟩
      · intro z hz
        have h1 : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω G (P z) :=
          (hG (P z) hz).contMDiffAt (U.isOpen.mem_nhds hz)
        have h2 := (h1.comp z (hPc z)).mdifferentiableAt (by simp)
        exact (mdifferentiableAt_iff_differentiableAt.mp h2).differentiableWithinAt
      · intro l z _
        simp only [Function.comp_apply, hPper]
      · intro z
        exact dif_pos z.2
    · rintro ⟨g, hg, -, hgf⟩
      have hgan := HodgeLean.Foundations.AnalyticDivisorAlgebraic2.spec_analyticOnNhd_of_differentiableOn
        hUopen hg
      intro x₀ hx₀
      obtain ⟨z₀, rfl⟩ := hPsurj x₀
      obtain ⟨ψ, hψ0, hψ, hψd⟩ := hsec z₀
      have hgd : ContMDiffAt 𝓘(ℂ, b5_V Λ F) 𝓘(ℂ, ℂ) ω g (ψ (P z₀)) := by
        rw [hψ0]
        exact (hgan z₀ hx₀).contDiffAt.contMDiffAt
      refine (((hgd.comp (P z₀) hψd)).congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [hψ, U.isOpen.mem_nhds hx₀] with x hx hxU
      have hzU : ψ x ∈ P ⁻¹' (U : Set (ComplexPoint (b5_model Λ F hF Q))) := by
        change P (ψ x) ∈ U
        rw [hx]
        exact hxU
      simp only [Function.comp_apply, G]
      rw [dif_pos (show x ∈ U from hxU), hgf ⟨ψ x, hzU⟩]
      congr 1
      exact Subtype.ext hx.symm

end HodgeLean.Foundations.Program
