import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeCharts
import HodgeLean.Adapters.NormalConeB4aClassHolomorphicCharts

/-! # Centered canonical source charts inside prescribed open sets

Restricting a centered manifold chart preserves its coordinate inverse.
The holomorphic certificate is obtained on a smaller open neighbourhood.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters HodgeLean.Foundations.Analytic
open scoped Manifold ContDiff
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem exists_centered_canonical_point_chart
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (x : ComplexPoint X) (W : Set (ComplexPoint X)) (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ e : OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin d → ℂ)),
      a3b4_IsHolChart X.hom e ∧ x ∈ (pointChart e).source ∧ pointChart e x = 0 ∧
        (pointChart e).source ⊆ W ∧
        (∀ v, (pointChart e).symm v = (chartAt (Fin d → ℂ) x).symm
          (v + (chartAt (Fin d → ℂ) x) x)) ∧
        ∀ v ∈ (pointChart e).target,
          v + (chartAt (Fin d → ℂ) x) x ∈ (chartAt (Fin d → ℂ) x).target := by
  letI : LocallyOfFiniteType (Over.mk X.hom).hom := ‹LocallyOfFiniteType X.hom›
  letI : QuasiCompact (Over.mk X.hom).hom := ‹QuasiCompact X.hom›
  letI : IsSeparated (Over.mk X.hom).hom := ‹IsSeparated X.hom›
  let χ := chartAt (Fin d → ℂ) x
  let c := χ x
  let a := χ.trans (Homeomorph.subRight c).toOpenPartialHomeomorph
  let H := (Homeomorph.uniqueProd (Fin 0 → ℂ) (Fin d → ℂ)).symm
  let E := a.trans H.toOpenPartialHomeomorph
  have hxχ : x ∈ χ.source := mem_chart_source _ x
  have hxE : x ∈ E.source := ⟨⟨hxχ, by trivial⟩, by trivial⟩
  have hχ : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω χ x :=
    (contMDiffOn_chart (I := 𝓘(ℂ, Fin d → ℂ)) (n := ω) (x := x)).contMDiffAt
      (χ.open_source.mem_nhds hxχ)
  have hE : ContMDiffAt 𝓘(ℂ, Fin d → ℂ)
      𝓘(ℂ, (Fin 0 → ℂ) × (Fin d → ℂ)) ω E x := by
    have ht : ContMDiffAt 𝓘(ℂ, Fin d → ℂ)
        𝓘(ℂ, (Fin 0 → ℂ) × (Fin d → ℂ)) ω
        (fun y => ((0 : Fin 0 → ℂ), χ y - c)) x :=
      (contMDiffAt_prod_module_iff _).mpr ⟨contMDiffAt_const, hχ.sub contMDiffAt_const⟩
    apply ht.congr_of_eventuallyEq
    filter_upwards [] with y
    exact Prod.ext (Subsingleton.elim _ _) rfl
  obtain ⟨N, hN, hxN, hhol⟩ := a3b4a_classLocal_exists_holomorphic_restriction X d 0 d E x hxE hE
  let e := E.restrOpen (N ∩ W) (hN.inter hW)
  have he : a3b4_IsHolChart X.hom e := by
    constructor
    · intro k
      exact Fin.elim0 k
    · intro k
      exact anrem_isHolFun_restrict (f4_analytification (Over.mk X.hom))
        (fun y (hy : y ∈ e.source) =>
          (show y ∈ (E.restrOpen N hN).source from ⟨hy.1, hy.2.1⟩)) (hhol.2 k)
  have hx : x ∈ (pointChart e).source := ⟨⟨hxE, hxN, hxW⟩, by trivial⟩
  have hinv (v : Fin d → ℂ) : (pointChart e).symm v = χ.symm (v + c) := rfl
  have hvalue (y : ComplexPoint X) : pointChart e y = χ y - c := rfl
  refine ⟨e, he, hx, ?_, ?_, hinv, ?_⟩
  · change χ x - c = 0
    exact sub_self _
  · intro y hy
    exact hy.1.2.2
  · intro v hv
    have hsrc : (pointChart e).symm v ∈ χ.source :=
      (((pointChart e).map_target hv).1.1).1.1
    have hcoord : χ ((pointChart e).symm v) = v + c :=
      (sub_eq_iff_eq_add).mp (by simpa only [hvalue] using (pointChart e).right_inv hv)
    exact hcoord ▸ χ.map_source hsrc

end AlgebraicGeometry.SingularCycles
