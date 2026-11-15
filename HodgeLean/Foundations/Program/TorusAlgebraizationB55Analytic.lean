import HodgeLean.Foundations.Program.TorusAlgebraizationB55Graph
import HodgeLean.Foundations.Program.RelativeTorusTopology
import HodgeLean.Foundations.Program.RelativeTorusKernel
import HodgeLean.Adapters.ExpHolomorphic

/-! # Holomorphy of the transported group operations

Let `e : T ≃ₜ X(ℂ)` identify a complex torus with the complex points of a smooth integral complex
scheme, holomorphically in both directions. Inversion and addition transported through `e` are
holomorphic for the algebraic charts, and their graphs have Zariski closed carriers.
-/

noncomputable section
set_option maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open Filter Topology
open scoped MonoidalCategory Manifold ContDiff TensorProduct
open HodgeLean.Foundations HodgeLean.Adapters

namespace HodgeLean.Foundations.Program

variable {Λ : Type} [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
  {F : Submodule ℂ (ℂ ⊗[ℤ] Λ)}

/-- The torus cover is additive. -/
theorem b55_torusCover_add (v w : b5_V Λ F) :
    b2_torusCover Λ F (v + w) = b2_torusCover Λ F v + b2_torusCover Λ F w := by
  simp only [b2_torusCover]
  rw [← QuotientAddGroup.mk_add]
  congr 1
  exact map_add (b2_coord ((ℂ ⊗[ℤ] Λ) ⧸ F)).symm v w

/-- The torus cover commutes with negation. -/
theorem b55_torusCover_neg (v : b5_V Λ F) :
    b2_torusCover Λ F (-v) = -b2_torusCover Λ F v := by
  simp only [b2_torusCover]
  rw [← QuotientAddGroup.mk_neg]
  congr 1
  exact map_neg (b2_coord ((ℂ ⊗[ℤ] Λ) ⧸ F)).symm v

/-- The torus cover inverts each torus chart on its source. -/
theorem b55_torusCover_chart [DiscreteTopology (b2_latticeMap Λ F).range]
    (t x : b2_torus Λ F) (hx : x ∈ (chartAt (b5_V Λ F) t).source) :
    b2_torusCover Λ F (chartAt (b5_V Λ F) t x) = x := by
  obtain ⟨-, h₂⟩ := Classical.choose_spec (b2_isLocalHomeomorph_mk Λ F t.out)
  set σ := Classical.choose (b2_isLocalHomeomorph_mk Λ F t.out)
  have hx' : x ∈ σ.target := by
    have : x ∈ (b2_torusChart Λ F t).source := hx
    simpa [b2_torusChart] using this
  change QuotientAddGroup.mk ((b2_coordHomeomorph Λ F).symm
    ((b2_coordHomeomorph Λ F) (σ.symm x))) = x
  rw [Homeomorph.symm_apply_apply]
  have : (QuotientAddGroup.mk (σ.symm x) : b2_torus Λ F) = σ (σ.symm x) := by
    rw [← h₂]
  rw [this, σ.right_inv hx']

/-- Near any point, a holomorphic map into the torus is the torus cover of a holomorphic map into
the cover coordinates. -/
private theorem b55_local_lift [DiscreteTopology (b2_latticeMap Λ F).range]
    {M : Type} [TopologicalSpace M] {d : ℕ} [ChartedSpace (Fin d → ℂ) M]
    (g : M → b2_torus Λ F) (hg : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, b5_V Λ F) ω g) (p₀ : M) :
    ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, b5_V Λ F) ω (fun p ↦ chartAt (b5_V Λ F) (g p₀) (g p)) p₀ ∧
      ∀ᶠ p in 𝓝 p₀, b2_torusCover Λ F (chartAt (b5_V Λ F) (g p₀) (g p)) = g p := by
  haveI := b2_torus_isManifold F
  have hsrc : (chartAt (b5_V Λ F) (g p₀)).source ∈ 𝓝 (g p₀) :=
    (chartAt (b5_V Λ F) (g p₀)).open_source.mem_nhds (mem_chart_source _ _)
  have hev : ∀ᶠ p in 𝓝 p₀, g p ∈ (chartAt (b5_V Λ F) (g p₀)).source :=
    (hg p₀).continuousAt.preimage_mem_nhds hsrc
  refine ⟨?_, hev.mono fun p hp ↦ b55_torusCover_chart _ _ hp⟩
  exact ((contMDiffOn_chart (I := 𝓘(ℂ, b5_V Λ F)) (n := ω) (x := g p₀)).contMDiffAt hsrc).comp
    p₀ (hg p₀)

/-- The composite of a holomorphic map out of the torus with the torus cover is holomorphic. -/
private theorem b55_contMDiff_comp_cover [DiscreteTopology (b2_latticeMap Λ F).range]
    {N : Type} [TopologicalSpace N] {d : ℕ} [ChartedSpace (Fin d → ℂ) N]
    (h : b2_torus Λ F → N) (hh : ContMDiff 𝓘(ℂ, b5_V Λ F) 𝓘(ℂ, Fin d → ℂ) ω h) :
    ContMDiff 𝓘(ℂ, b5_V Λ F) 𝓘(ℂ, Fin d → ℂ) ω (h ∘ b2_torusCover Λ F) :=
  hh.comp (b2t_torusCover_contMDiff (Λ := Λ) (F := F))

/-- Inversion transported through `e` is holomorphic.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, §1.1. -/
theorem b55_neg_contMDiff (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [DiscreteTopology (b2_latticeMap Λ F).range]
    (e : b2_torus Λ F ≃ₜ ComplexPoint X)
    (he : ContMDiff 𝓘(ℂ, b5_V Λ F) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω e)
    (hes : ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, b5_V Λ F) ω e.symm) :
    ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω
      (fun p ↦ e (-(e.symm p))) := by
  intro p₀
  obtain ⟨hc, hev⟩ := b55_local_lift (F := F) e.symm hes p₀
  have hH := b55_contMDiff_comp_cover (F := F) e he
  refine ((hH _).comp p₀ hc.neg).congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  simp only [Function.comp_apply, b55_torusCover_neg, hp]

/-- Addition transported through `e`, read on two morphisms into `X`, is holomorphic.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, §1.1. -/
theorem b55_add_contMDiff (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsIntegral Y.left] [Smooth Y.hom]
    [DiscreteTopology (b2_latticeMap Λ F).range]
    (e : b2_torus Λ F ≃ₜ ComplexPoint X)
    (he : ContMDiff 𝓘(ℂ, b5_V Λ F) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω e)
    (hes : ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, b5_V Λ F) ω e.symm)
    (π₁ π₂ : Y ⟶ X) :
    ContMDiff 𝓘(ℂ, Fin (dim Y.left) → ℂ) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω
      (fun p ↦ e (e.symm (Point.map π₁ p) + e.symm (Point.map π₂ p))) := by
  intro p₀
  have h₁ := hes.comp (spec_contMDiff_pointMap Y X (dim Y.left) (dim X.left) π₁)
  have h₂ := hes.comp (spec_contMDiff_pointMap Y X (dim Y.left) (dim X.left) π₂)
  obtain ⟨hc₁, hev₁⟩ := b55_local_lift (F := F) _ h₁ p₀
  obtain ⟨hc₂, hev₂⟩ := b55_local_lift (F := F) _ h₂ p₀
  have hH := b55_contMDiff_comp_cover (F := F) e he
  refine ((hH _).comp p₀ (hc₁.add hc₂)).congr_of_eventuallyEq ?_
  filter_upwards [hev₁, hev₂] with p hp₁ hp₂
  simp only [Function.comp_apply] at hp₁ hp₂
  simp only [Function.comp_apply, Pi.add_apply, b55_torusCover_add]
  rw [hp₁, hp₂]

/-- The graph of transported inversion has a Zariski closed carrier.
Source: Chow (1949), via `gagam_graph_closed`. -/
theorem b55_neg_closed (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [DiscreteTopology (b2_latticeMap Λ F).range]
    (e : b2_torus Λ F ≃ₜ ComplexPoint X)
    (he : ContMDiff 𝓘(ℂ, b5_V Λ F) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω e)
    (hes : ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, b5_V Λ F) ω e.symm) :
    ∃ C : Set (X ⊗ X).left, IsClosed C ∧
      gagam_graph X X (fun p ↦ e (-(e.symm p))) =
        (Point.underlying : ComplexPoint (X ⊗ X) → (X ⊗ X).left) ⁻¹' C :=
  gagam_graph_closed X X _ (b55_neg_contMDiff X e he hes)

/-- The graph of transported addition on `X ⊗ X` has a Zariski closed carrier.
Source: Chow (1949), via `gagam_graph_closed`. -/
theorem b55_add_closed (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [DiscreteTopology (b2_latticeMap Λ F).range]
    (e : b2_torus Λ F ≃ₜ ComplexPoint X)
    (he : ContMDiff 𝓘(ℂ, b5_V Λ F) 𝓘(ℂ, Fin (dim X.left) → ℂ) ω e)
    (hes : ContMDiff 𝓘(ℂ, Fin (dim X.left) → ℂ) 𝓘(ℂ, b5_V Λ F) ω e.symm) :
    haveI : IsIntegral (X ⊗ X).left := gagam_product_isIntegral X X
    ∃ C : Set ((X ⊗ X) ⊗ X).left, IsClosed C ∧
      gagam_graph (X ⊗ X) X (fun p ↦ e (e.symm (Point.map (CartesianMonoidalCategory.fst X X) p) +
        e.symm (Point.map (CartesianMonoidalCategory.snd X X) p))) =
        (Point.underlying : ComplexPoint ((X ⊗ X) ⊗ X) → ((X ⊗ X) ⊗ X).left) ⁻¹' C := by
  haveI : IsIntegral (X ⊗ X).left := gagam_product_isIntegral X X
  haveI : Smooth (X ⊗ X).hom := gagam_product_smooth X X
  haveI : IsProjective (X ⊗ X).hom := gagam_product_projective X X
  exact gagam_graph_closed (X ⊗ X) X _ (b55_add_contMDiff X (X ⊗ X) e he hes _ _)

end HodgeLean.Foundations.Program
