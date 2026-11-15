import HodgeLean.Foundations.Program.HurwitzPrymRexFillMaps
import HodgeLean.Foundations.Program.HurwitzPrymDefs

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-rex`: filling the punctures of a Galois covering

A connected Galois `G`-covering of `Y ∖ B` (`Y` a compact Riemann surface, `B` finite) extends to a
compact Riemann surface `C` with a holomorphic `G`-action and a holomorphic Galois map `C → Y`,
containing the covering as the open complement of the fibres over `B`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Topology Metric Set Complex Manifold HodgeLean.Foundations.Program.HurwitzPrymRexPunct
open scoped ContDiff

namespace HodgeLean.Foundations.Program

namespace HurwitzPrymRexFill

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y]
variable {B : Set Y} {G U : Type} [Group G] [TopologicalSpace U] [MulAction G U]
variable {p : U → {y : Y // y ∉ B}}

/-- A complex-linear identification of a one-dimensional space with `ℂ`.
Source: Mathlib `LinearEquiv.ofFinrankEq`. -/
def κOf {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] (hF : Module.finrank ℂ F = 1) :
    F ≃L[ℂ] ℂ :=
  haveI : FiniteDimensional ℂ F := Module.finite_of_finrank_eq_succ hF
  (LinearEquiv.ofFinrankEq F ℂ (by rw [hF, Module.finrank_self])).toContinuousLinearEquiv

example : κOf (F := ℂ) (Module.finrank_self ℂ) 1 = κOf (F := ℂ) (Module.finrank_self ℂ) 1 := rfl

/-- **The choices exist**: disjoint coordinate discs around the finitely many punctures. -/
theorem exists_setup [T2Space Y] (hE' : Module.finrank ℂ E' = 1) (hB : B.Finite) (u₀ : U) :
    Nonempty (Setup E' p) := by
  set κ' := κOf hE'
  obtain ⟨O, hO, hOd⟩ := hB.t2_separation
  have hex : ∀ b : B, ∃ r > 0, ball (0 : ℂ) r ⊆ Tgt κ' b.1 ∧
      ∀ z ∈ ball (0 : ℂ) r, ξY κ' b.1 z ∈ O b.1 :=
    fun b ↦ exists_radius b.1 ((hO b.1).2.mem_nhds (hO b.1).1)
  choose r hr hTgt hO' using hex
  have hmemO : ∀ b b' : B, b'.1 ∈ O b.1 → b' = b := by
    intro b b' hb'
    by_contra hne
    exact Set.disjoint_left.1 (hOd b'.2 b.2 (fun h ↦ hne (Subtype.ext h))) (hO b'.1).1 hb'
  have havoid : ∀ b : B, ∀ z ∈ ball (0 : ℂ) (r b), ξY κ' b.1 z ∈ B → z = 0 := by
    intro b z hz hzB
    have h1 := hmemO b ⟨_, hzB⟩ (hO' b z hz)
    have h2 : ξY κ' b.1 z = ξY κ' b.1 0 := by rw [ξY_zero]; exact congrArg Subtype.val h1
    exact injOn_ξY b.1 (hTgt b hz) (zero_mem_Tgt b.1) h2
  have hdisj : ∀ b b' : B, b ≠ b' → ∀ z ∈ ball (0 : ℂ) (r b), ∀ z' ∈ ball (0 : ℂ) (r b'),
      ξY κ' b.1 z ≠ ξY κ' b'.1 z' := by
    intro b b' hbb' z hz z' hz' heq
    exact Set.disjoint_left.1 (hOd b.2 b'.2 (fun h ↦ hbb' (Subtype.ext h))) (hO' b z hz)
      (heq ▸ hO' b' z' hz')
  exact ⟨⟨κ', r, hr, hTgt, havoid, hdisj, u₀, hB.isClosed⟩⟩

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Filling the punctures** (Riemann existence, stage 2): a connected Galois `G`-covering of
`Y ∖ B` extends to a compact connected Riemann surface `C` with a holomorphic `G`-action and a
holomorphic Galois map `f : C → Y` with `f⁻¹(Y ∖ B) = U`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, Theorem 8.4. -/
theorem extend [IsManifold 𝓘(ℂ, E') ω Y] (hE : Module.finrank ℂ E = 1)
    [Nonempty Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] (hE' : Module.finrank ℂ E' = 1)
    (B : Set Y) (hB : B.Finite) {G : Type} [Group G] [Finite G]
    {U : Type} [TopologicalSpace U] [MulAction G U] [ConnectedSpace U]
    (p : U → {y : Y // y ∉ B}) (hp : IsQuotientCoveringMap p G) :
    ∃ (C : Type) (_ : TopologicalSpace C) (_ : ChartedSpace E C) (_ : IsManifold 𝓘(ℂ, E) ω C)
      (_ : T2Space C) (_ : CompactSpace C) (_ : ConnectedSpace C) (_ : Nonempty C)
      (_ : MulAction G C)
      (f : C → Y) (ι : U → C),
      (∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x)) ∧
      ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f ∧ b4_IsGaloisCover G f ∧
      Topology.IsOpenEmbedding ι ∧ Set.range ι = f ⁻¹' Bᶜ ∧
      (∀ u, f (ι u) = p u) ∧ ∀ (g : G) (u : U), ι (g • u) = g • ι u := by
  obtain ⟨u₀⟩ : Nonempty U := inferInstance
  obtain ⟨S⟩ := exists_setup (p := p) hE' hB u₀
  set κ : ℂ ≃L[ℂ] E := (κOf hE).symm
  haveI : FiniteDimensional ℂ E' := Module.finite_of_finrank_eq_succ hE'
  haveI : LocallyCompactSpace Y := ChartedSpace.locallyCompactSpace E' Y
  refine ⟨S.CC hp κ, inferInstance, inferInstance, S.isManifold hp κ, inferInstance,
    inferInstance, inferInstance, ⟨S.ι hp κ u₀⟩, inferInstance, S.f hp κ, S.ι hp κ,
    fun g ↦ S.contMDiff_smul hp κ g, S.contMDiff_f hp κ,
    ⟨S.f_smul hp κ, fun x x' h ↦ S.exists_smul_of_f_eq hp κ h⟩, S.isOpenEmbedding_ι hp κ, ?_,
    fun u ↦ rfl, fun g u ↦ rfl⟩
  ext x
  rcases x with u | c
  · exact ⟨fun _ ↦ (p u).2, fun _ ↦ ⟨u, rfl⟩⟩
  · refine ⟨?_, fun h ↦ absurd c.1.2 h⟩
    rintro ⟨u, hu⟩
    exact absurd hu Sum.inl_ne_inr

end HurwitzPrymRexFill

end HodgeLean.Foundations.Program
