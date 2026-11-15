import HodgeLean.Foundations.Program.HurwitzPrym

/-! # B6-1: normalized configurations and selected covering fibres

Implication from an arbitrary finite-group Nielsen tuple to a family of individual
covering surfaces over the normalized configuration chart. The total set below has
no assigned analytic family structure. HC no distance; AV milestone no distance.
-/

noncomputable section

open scoped Manifold ContDiff

namespace HodgeLean.Foundations.Program

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- Ten moving points followed by the normalized points `0, 1, ∞`.
Source: Forster, *Lectures on Riemann Surfaces*, §1.3; G32 v0.16, §3.1. -/
def b6_branch (t : Fin 10 → ℂ) : Fin 13 → OnePoint ℂ :=
  Fin.append (fun i ↦ (t i : OnePoint ℂ))
    ![((0 : ℂ) : OnePoint ℂ), ((1 : ℂ) : OnePoint ℂ), OnePoint.infty]

example (t : Fin 10 → ℂ) : b6_branch t 0 = (t 0 : OnePoint ℂ) := rfl

/-- The ordered normalized configuration slice, with all thirteen points distinct.
Source: G32 v0.16, §3.1 and §5; normalization of three points on the sphere. -/
def b6_chart : Set (Fin 10 → ℂ) := {t | Function.Injective (b6_branch t)}

example (t : b6_chart) : Function.Injective (b6_branch t.val) := t.property

/-- An illustrative configuration; no identification with the Schlesinger initial point.
Source: The normalized slice `b6_chart`. -/
def b6_base : Fin 10 → ℂ := fun i ↦ (i.val : ℂ) + 2

example : b6_base 0 = 2 := by simp only [b6_base, Fin.val_zero, Nat.cast_zero, zero_add]

private theorem b6_sphere_genus : Module.finrank ℂ (b3_HolForm ℂ (OnePoint ℂ)) = 0 := by
  have h : b3_HolForm ℂ (OnePoint ℂ) = ⊥ :=
    (Submodule.eq_bot_iff _).2 fun θ hθ ↦ b4cov_sphere_form_eq_zero θ hθ
  rw [h, finrank_bot]

/-- The covering surface selected from B4 at the specified branch configuration.
Source: `b4_riemannExistence`; Forster, Theorem 8.4. -/
def b6_Cover (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) : Type :=
  (b4_riemannExistence (E := ℂ) (E' := ℂ) (Module.finrank_self ℂ)
    (Module.finrank_self ℂ) b6_sphere_genus g hg (b6_branch t.val) t.property).choose

example (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) : b6_Cover G g hg t =
    (b4_riemannExistence (E := ℂ) (E' := ℂ) (Module.finrank_self ℂ)
    (Module.finrank_self ℂ) b6_sphere_genus g hg (b6_branch t.val) t.property).choose := rfl

/-- The topology structure of the selected B4 surface.
Source: `b4_riemannExistence`. -/
instance b6_coverTopology (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) : TopologicalSpace (b6_Cover G g hg t) :=
  (b4_riemannExistence (E := ℂ) (E' := ℂ) (Module.finrank_self ℂ)
    (Module.finrank_self ℂ) b6_sphere_genus g hg (b6_branch t.val) t.property).choose_spec.choose

example (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) : TopologicalSpace (b6_Cover G g hg t) := inferInstance

/-- The charts structure of the selected B4 surface.
Source: `b4_riemannExistence`. -/
instance b6_coverCharts (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) : ChartedSpace ℂ (b6_Cover G g hg t) :=
  (b4_riemannExistence (E := ℂ) (E' := ℂ) (Module.finrank_self ℂ)
    (Module.finrank_self ℂ) b6_sphere_genus g hg (b6_branch t.val) t.property).choose_spec.choose_spec.choose

example (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) : ChartedSpace ℂ (b6_Cover G g hg t) := inferInstance

/-- The manifold structure of the selected B4 surface.
Source: `b4_riemannExistence`. -/
instance b6_coverManifold (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) : IsManifold 𝓘(ℂ, ℂ) ω (b6_Cover G g hg t) :=
  (b4_riemannExistence (E := ℂ) (E' := ℂ) (Module.finrank_self ℂ)
    (Module.finrank_self ℂ) b6_sphere_genus g hg (b6_branch t.val) t.property).choose_spec.choose_spec.choose_spec.choose

example (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) : IsManifold 𝓘(ℂ, ℂ) ω (b6_Cover G g hg t) := inferInstance

/-- The t2 structure of the selected B4 surface.
Source: `b4_riemannExistence`. -/
instance b6_coverT2 (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) : T2Space (b6_Cover G g hg t) :=
  (b4_riemannExistence (E := ℂ) (E' := ℂ) (Module.finrank_self ℂ)
    (Module.finrank_self ℂ) b6_sphere_genus g hg (b6_branch t.val) t.property).choose_spec.choose_spec.choose_spec.choose_spec.choose

example (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) : T2Space (b6_Cover G g hg t) := inferInstance

/-- The compact structure of the selected B4 surface.
Source: `b4_riemannExistence`. -/
instance b6_coverCompact (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) : CompactSpace (b6_Cover G g hg t) :=
  (b4_riemannExistence (E := ℂ) (E' := ℂ) (Module.finrank_self ℂ)
    (Module.finrank_self ℂ) b6_sphere_genus g hg (b6_branch t.val) t.property).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

example (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) : CompactSpace (b6_Cover G g hg t) := inferInstance

/-- The connected structure of the selected B4 surface.
Source: `b4_riemannExistence`. -/
instance b6_coverConnected (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) : ConnectedSpace (b6_Cover G g hg t) :=
  (b4_riemannExistence (E := ℂ) (E' := ℂ) (Module.finrank_self ℂ)
    (Module.finrank_self ℂ) b6_sphere_genus g hg (b6_branch t.val) t.property).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

example (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) : ConnectedSpace (b6_Cover G g hg t) := inferInstance

/-- The nonempty structure of the selected B4 surface.
Source: `b4_riemannExistence`. -/
instance b6_coverNonempty (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) : Nonempty (b6_Cover G g hg t) :=
  (b4_riemannExistence (E := ℂ) (E' := ℂ) (Module.finrank_self ℂ)
    (Module.finrank_self ℂ) b6_sphere_genus g hg (b6_branch t.val) t.property).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

example (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) : Nonempty (b6_Cover G g hg t) := inferInstance

/-- The action structure of the selected B4 surface.
Source: `b4_riemannExistence`. -/
instance b6_coverAction (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) : MulAction G (b6_Cover G g hg t) :=
  (b4_riemannExistence (E := ℂ) (E' := ℂ) (Module.finrank_self ℂ)
    (Module.finrank_self ℂ) b6_sphere_genus g hg (b6_branch t.val) t.property).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

example (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) : MulAction G (b6_Cover G g hg t) := inferInstance

/-- The faithful structure of the selected B4 surface.
Source: `b4_riemannExistence`. -/
instance b6_coverFaithful (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) : FaithfulSMul G (b6_Cover G g hg t) :=
  (b4_riemannExistence (E := ℂ) (E' := ℂ) (Module.finrank_self ℂ)
    (Module.finrank_self ℂ) b6_sphere_genus g hg (b6_branch t.val) t.property).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

example (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) : FaithfulSMul G (b6_Cover G g hg t) := inferInstance

/-- The map to the sphere selected together with the surface.
Source: `b4_riemannExistence`; Forster, Theorem 8.4. -/
def b6_coverMap (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) : b6_Cover G g hg t → OnePoint ℂ :=
  (b4_riemannExistence (E := ℂ) (E' := ℂ) (Module.finrank_self ℂ)
    (Module.finrank_self ℂ) b6_sphere_genus g hg (b6_branch t.val) t.property).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

example (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) : b6_coverMap G g hg t =
    (b4_riemannExistence (E := ℂ) (E' := ℂ) (Module.finrank_self ℂ)
    (Module.finrank_self ℂ) b6_sphere_genus g hg (b6_branch t.val) t.property).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose := rfl

/-- The dependent total set of the selected covering surfaces.
Source: The fibrewise construction `b6_Cover`. -/
def b6_Total (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) :=
  (t : b6_chart) × b6_Cover G g hg t

example (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) (x : b6_Cover G g hg t) : b6_Total G g hg := ⟨t, x⟩

/-- Projection to the configuration parameter.
Source: The dependent sum `b6_Total`. -/
def b6_projection (G : Type) [Group G] [Finite G] (g : Fin 13 → G)
    (hg : b4_Nielsen g) (x : b6_Total G g hg) : b6_chart := x.1

example (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) (x : b6_Cover G g hg t) :
    b6_projection G g hg ⟨t, x⟩ = t := rfl

/-- The family map to parameter times sphere, defined on the dependent total set.
Source: `b4_riemannExistence` and the dependent sum `b6_Total`. -/
def b6_familyMap (G : Type) [Group G] [Finite G] (g : Fin 13 → G)
    (hg : b4_Nielsen g) (x : b6_Total G g hg) : b6_chart × OnePoint ℂ :=
  ⟨x.1, b6_coverMap G g hg x.1 x.2⟩

example (G : Type) [Group G] [Finite G] (g : Fin 13 → G) (hg : b4_Nielsen g) (t : b6_chart) (x : b6_Cover G g hg t) :
    (b6_familyMap G g hg ⟨t, x⟩).2 = b6_coverMap G g hg t x := rfl

end HodgeLean.Foundations.Program
