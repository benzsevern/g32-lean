import HodgeLean.Foundations.Program.RelativeFrameOperatorDefs
import HodgeLean.Foundations.Program.PrymVariationFramesDefs

/-! # Relative frames in atlas charts: definitions for C12
The family version of the plumbing datum over the moving polydisc: analytic moving values, one
fibre plumbing datum for each parameter whose outer identification is the coordinate of the
product fibre, stationary outer charts that are analytic on the total space, and disc
coordinates that are restrictions of analytic functions on the total space (B5, B6 and B8 on the
total space). The sector form on one inner piece, and the family of glued forms over a parameter
set.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- A plumbing datum of the whole family over `V ⊆ b6t_polydisc b`, over outer data `D` on the base
surface `C`: moving values `ε(t)`, analytic on `V`; for each `t ∈ V` a plumbing datum of the fibre
`b63l_parameterFibre b C V hV t` whose identification with `C` is the product coordinate
`x ↦ (t, x)`; outer piece charts `(t, x) ↦ u_i(x)` that are analytic on the total space
(stationary coordinates, B5–B6); and disc coordinates `w_x` of every fibre that are the
restrictions of one analytic function `wTot x` on an open set `wSrc x` of the total space (the
jointly analytic moving root, B8 on the total space). These fields are geometric; none concerns
forms, operators, kernels or dimensions.
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §4.1 (outer piece, root coordinates, items
1–3) and §4.4 (`w_t` is jointly analytic in the atlas charts); §5 stage B, B5, B6, B8. -/
structure rf5_FamilyPlumbing (b : Fin 10 → ℂ) (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} (D : rf4_OuterData C O)
    (V : Set (Fin 10 → ℂ)) (hV : V ⊆ b6t_polydisc b)
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)] where
  ε : (Fin 10 → ℂ) → Fin D.m → ℂ
  ε_analytic : AnalyticOnNhd ℂ ε V
  S : ∀ t : V, rf4_Plumbing D (ε t) (b63l_parameterFibre b C V hV t)
  h_eq : ∀ t : V, (S t).h = (b6m_coordinate b C ⟨t.val, hV t.property⟩).symm
  outer_analytic : ∀ i, ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω
    (fun q : b6t_polydisc b × C ↦ D.P.chart i q.2) {q | q.2 ∈ (D.P.chart i).source}
  wTot : Fin D.m → b6t_polydisc b × C → ℂ
  wSrc : Fin D.m → Set (b6t_polydisc b × C)
  wSrc_open : ∀ x, IsOpen (wSrc x)
  w_analytic : ∀ x, ContMDiffOn 𝓘(ℂ, (Fin 10 → ℂ) × ℂ) 𝓘(ℂ, ℂ) ω (wTot x) (wSrc x)
  w_source : ∀ (t : V) (x : Fin D.m) (y : b63l_parameterFibre b C V hV t),
    y ∈ ((S t).w x).source ↔ y.val ∈ wSrc x
  w_eq : ∀ (t : V) (x : Fin D.m) (y : b63l_parameterFibre b C V hV t),
    y ∈ ((S t).w x).source → (S t).w x y = wTot x y.val

/-- The sector form `n Σ_{j<n} wʲ g_j(c + ε + wⁿ) dw` of source data `k` on the inner piece of
disc `x`, in the disc coordinate `w = w_x` of the fibre, as a function on the tangent bundle. It is
the inner branch of `rf4_glue`, extended by the same formula over the whole chart domain.
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §4.2 (sector map `B_{t,x}`) and §4.4;
Forster, *Lectures on Riemann Surfaces*, §9. -/
def rf5_sectorForm {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (k : rf4_Src D) (x : Fin D.m) : TangentBundle 𝓘(ℂ, ℂ) X → ℂ :=
  fun q ↦ rf4_sectorCoeff (D.deg x) (fun j ↦ rf4_extendBdd (k.2 x j)) (D.c x + ε x) (S.w x q.1) *
    (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (S.w x) q.1 q.2)

example {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (x : Fin D.m) : rf5_sectorForm S 0 x = 0 := by
  funext q
  simp only [rf5_sectorForm, Prod.snd_zero, Pi.zero_apply, Pi.zero_apply]
  simp [rf4_sectorCoeff, rf4_extendBdd]
  exact zero_mul _

open Classical in
/-- The family of glued forms of a parameter family `e` of source data: at `t ∈ V ∩ W` the glued
function `rf4_glue (F.S t) (e t)` on the tangent bundle of the fibre, and zero at the other
parameters of `V`.
Source: `docs/specs/RelativeFrame.md` on `spec/relA`, §4.4 (each `e_k(t)` glues to a form on
`X_t`) and §5, C12. -/
def rf5_relGlue {b : Fin 10 → ℂ} {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O}
    {V : Set (Fin 10 → ℂ)} {hV : V ⊆ b6t_polydisc b}
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (F : rf5_FamilyPlumbing b C D V hV) (W : Set (Fin 10 → ℂ))
    (e : (Fin 10 → ℂ) → rf4_Src D) :
    (t : V) → TangentBundle 𝓘(ℂ, ℂ) (b63l_parameterFibre b C V hV t) → ℂ :=
  fun t ↦ if t.val ∈ W then rf4_glue (F.S t) (e t.val) else 0

example {b : Fin 10 → ℂ} {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O}
    {V : Set (Fin 10 → ℂ)} {hV : V ⊆ b6t_polydisc b}
    [ChartedSpace ((Fin 10 → ℂ) × ℂ) (b6t_polydisc b × C)]
    [∀ t : V, ChartedSpace ℂ (b63l_parameterFibre b C V hV t)]
    [∀ t : V, IsManifold 𝓘(ℂ, ℂ) ω (b63l_parameterFibre b C V hV t)]
    (F : rf5_FamilyPlumbing b C D V hV) (W : Set (Fin 10 → ℂ)) (e : (Fin 10 → ℂ) → rf4_Src D)
    (t : V) (ht : t.val ∈ W) : rf5_relGlue F W e t = rf4_glue (F.S t) (e t.val) := by
  simp [rf5_relGlue, ht]

end HodgeLean.Foundations.Program
