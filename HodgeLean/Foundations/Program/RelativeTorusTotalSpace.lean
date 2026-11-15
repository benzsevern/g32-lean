import HodgeLean.Foundations.Program.RelativeTorusFamily

/-!
# Track B2, families of complex tori: charts of the total space

A frame of the family at `b₁` is a simply connected open `U ∋ b₁`, an open set `D` of the chart
at `b₁`, a holomorphic family `x ↦ Q_x : ℂ ⊗ Λ_{b₁} → ℂ^g` of projections whose kernel is the
transported `F`, a complement `J` with `Q_x ∘ J = id`, and a uniform bound separating the lattice
from `0` in `ℂ^g`. The parametrisation `(x, w) ↦ [[J w]]` over the point with coordinate `x` is
then continuous, open and injective on `D × ball(w₀, ε/2)`, so it has local inverses; any flat
trivialisation factors through it near each point by a map holomorphic in the base and affine in
the fibre (`b2f_Frame.glue`). Frames exist at every point (`b2f_frame_exists`); the local inverses
at the points of the total space form a charted space (`b2f_cs`) whose transitions are
holomorphic, on which the projection is a holomorphic submersion and the fibre inclusions and the
flat trivialisations are holomorphic.
-/

noncomputable section

open CategoryTheory Manifold
open scoped TensorProduct ContDiff

namespace HodgeLean.Foundations.Program

section Frame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]

variable (E) in
/-- **A holomorphic frame of a family of tori at `b₁`**: a simply connected open `U ∋ b₁`, an
open set `D` of the chart at `b₁`, holomorphic projections `Q_x : ℂ ⊗ Λ_{b₁} → ℂ^g` (`x ∈ D`)
along the transported filtration, a complement `J` with `Q_x ∘ J = id`, and a bound `ε` below
which `Q_x` of a lattice vector vanishes.
Source: Griffiths, *Periods of integrals on algebraic manifolds III*, Publ. Math. IHES 38 (1970),
§1; Huybrechts, *Complex Geometry*, §2.3. -/
structure b2f_Frame (L : b2_LatticeLocalSystem B) (F : ∀ b, Submodule ℂ (L.cFiber b)) (g : ℕ)
    (b₁ : B) where
  U : Set B
  hU : IsSimplyConnected U
  hUo : IsOpen U
  mem : b₁ ∈ U
  D : Set E
  hDo : IsOpen D
  memD : chartAt E b₁ b₁ ∈ D
  D_sub : D ⊆ (chartAt E b₁).target
  D_mem : ∀ x ∈ D, (chartAt E b₁).symm x ∈ U
  Q : E → ((Fin (Module.finrank ℂ (L.cFiber b₁)) → ℂ) →L[ℂ] (Fin g → ℂ))
  hQ : ContDiffOn ℂ ω Q D
  J : (Fin g → ℂ) →L[ℂ] (Fin (Module.finrank ℂ (L.cFiber b₁)) → ℂ)
  QJ : ∀ x ∈ D, ∀ w, Q x (J w) = w
  ker : ∀ x (hx : x ∈ D) (v : L.cFiber b₁), Q x (b2_coord _ v) = 0 ↔
    (L.flatTransport U hU ⟨(chartAt E b₁).symm x, D_mem x hx⟩ ⟨b₁, mem⟩).symm v ∈
      F ((chartAt E b₁).symm x)
  ε : ℝ
  ε_pos : 0 < ε
  sep : ∀ x ∈ D, ∀ l : L.fiber b₁, ‖Q x (b2_coord _ (b2_incl _ l))‖ < ε →
    Q x (b2_coord _ (b2_incl _ l)) = 0

namespace b2f_Frame
variable {L : b2_LatticeLocalSystem B} {F : ∀ b, Submodule ℂ (L.cFiber b)} {g : ℕ} {b₁ : B}
variable (fr : b2f_Frame E L F g b₁)

/-- The base point of the frame as a point of `U`.
Source: Voisin, *Hodge Theory I*, ch. 9 (flat frames). -/
abbrev pt : fr.U := ⟨b₁, fr.mem⟩

open scoped Classical in
/-- The local parametrisation `(x, w) ↦ [[J w]]` over the chart point `x`.
Source: Griffiths, Publ. Math. IHES 38, §1; Birkenhake–Lange, §1.1. -/
def Ψ (z : E × (Fin g → ℂ)) : b2_totalSpace L F :=
  if hz : z.1 ∈ fr.D then
    b2_flatTriv L F fr.U fr.hU fr.pt (⟨(chartAt E b₁).symm z.1, fr.D_mem _ hz⟩,
      (b2_coord _).symm (fr.J z.2))
  else b2_flatTriv L F fr.U fr.hU fr.pt (fr.pt, 0)

example : (fr.pt : B) = b₁ := rfl

example : 0 < fr.ε := fr.ε_pos

theorem Ψ_eq (z : E × (Fin g → ℂ)) (hz : z.1 ∈ fr.D) :
    fr.Ψ z = b2_flatTriv L F fr.U fr.hU fr.pt (⟨(chartAt E b₁).symm z.1, fr.D_mem _ hz⟩,
      (b2_coord _).symm (fr.J z.2)) :=
  dite_eq_left hz

example (z : E × (Fin g → ℂ)) (hz : z.1 ∈ fr.D) :
    b2_proj L F (fr.Ψ z) = (chartAt E b₁).symm z.1 := by
  rw [fr.Ψ_eq z hz]; rfl

/-- Changing the representative by `J ∘ Q` does not change the class. -/
theorem flatTriv_JQ (x : E) (hx : x ∈ fr.D) (v : L.cFiber b₁) :
    b2_flatTriv L F fr.U fr.hU fr.pt (⟨(chartAt E b₁).symm x, fr.D_mem x hx⟩,
      (b2_coord _).symm (fr.J (fr.Q x (b2_coord _ v)))) =
    b2_flatTriv L F fr.U fr.hU fr.pt (⟨(chartAt E b₁).symm x, fr.D_mem x hx⟩, v) := by
  refine (b2f_flatTriv_mk_eq L F fr.U fr.U fr.hU fr.hU fr.pt fr.pt _ _ _ _ _).2 ⟨0, ?_⟩
  rw [map_zero, add_zero, ← map_sub]
  refine (fr.ker x hx _).1 ?_
  rw [map_sub, LinearEquiv.apply_symm_apply, map_sub, fr.QJ x hx, sub_self]

theorem continuousOn_Ψ : ContinuousOn fr.Ψ (fr.D ×ˢ Set.univ) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous fun z : (fr.D ×ˢ (Set.univ : Set (Fin g → ℂ))) ↦
      b2_flatTriv L F fr.U fr.hU fr.pt (⟨(chartAt E b₁).symm z.1.1, fr.D_mem _ z.2.1⟩,
        (b2_coord _).symm (fr.J z.1.2)) := by
    refine (b2_flatTriv_continuous L F fr.U fr.hU fr.hUo fr.pt).comp (Continuous.prodMk ?_ ?_)
    · refine Continuous.subtype_mk ?_ _
      exact (chartAt E b₁).continuousOn_symm.comp_continuous
        (continuous_fst.comp continuous_subtype_val) fun z ↦ fr.D_sub z.2.1
    · exact (IsModuleTopology.continuous_of_linearMap
        (b2_coord (L.cFiber b₁)).symm.toLinearMap).comp
        (fr.J.continuous.comp (continuous_snd.comp continuous_subtype_val))
  convert hc using 1
  funext z
  exact fr.Ψ_eq z.1 z.2.1

theorem isOpen_image_Ψ (hhol : L.IsHolomorphicSubbundle E F) (O : Set (E × (Fin g → ℂ)))
    (hO : IsOpen O) (hOD : O ⊆ fr.D ×ˢ Set.univ) : IsOpen (fr.Ψ '' O) := by
  set c := chartAt E b₁
  let κ := b2_coord (L.cFiber b₁)
  let Θ : fr.U × L.cFiber b₁ → E × (Fin g → ℂ) := fun p ↦ (c p.1, fr.Q (c p.1) (κ p.2))
  let S : Set (fr.U × L.cFiber b₁) := {p | (p.1 : B) ∈ c.source ∧ c p.1 ∈ fr.D}
  have hS : IsOpen S := by
    have := c.continuousOn.isOpen_inter_preimage c.open_source fr.hDo
    exact (this.preimage (continuous_subtype_val.comp continuous_fst))
  have hΘ : ContinuousOn Θ S := by
    have h1 : ContinuousOn (fun p : fr.U × L.cFiber b₁ ↦ c p.1) S :=
      c.continuousOn.comp (continuous_subtype_val.comp continuous_fst).continuousOn
        fun p hp ↦ hp.1
    refine h1.prodMk ?_
    have h2 : ContinuousOn (fun p : fr.U × L.cFiber b₁ ↦ fr.Q (c p.1)) S :=
      fr.hQ.continuousOn.comp h1 fun p hp ↦ hp.2
    exact h2.clm_apply ((IsModuleTopology.continuous_of_linearMap
      κ.toLinearMap).comp continuous_snd).continuousOn
  have heq : fr.Ψ '' O = b2_flatTriv L F fr.U fr.hU fr.pt '' (S ∩ Θ ⁻¹' O) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzD := (hOD hz).1
      refine ⟨(⟨c.symm z.1, fr.D_mem _ hzD⟩, κ.symm (fr.J z.2)), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · exact c.map_target (fr.D_sub hzD)
      · simp only; rw [c.right_inv (fr.D_sub hzD)]; exact hzD
      · simp only [Set.mem_preimage, Θ, LinearEquiv.apply_symm_apply]
        rw [c.right_inv (fr.D_sub hzD), fr.QJ _ hzD]
        exact hz
      · exact (fr.Ψ_eq z hzD).symm
    · rintro ⟨⟨⟨b, hbU⟩, v⟩, ⟨⟨hbc, hbD⟩, hΘO⟩, rfl⟩
      refine ⟨Θ (⟨b, hbU⟩, v), hΘO, ?_⟩
      rw [fr.Ψ_eq _ hbD]
      have hb : c.symm (c b) = b := c.left_inv hbc
      have := fr.flatTriv_JQ (c b) hbD v
      exact this.trans (congrArg (fun u ↦ b2_flatTriv L F fr.U fr.hU fr.pt (u, v))
        (Subtype.ext hb))
  rw [heq]
  exact b2f_flatTriv_isOpenMap L F hhol fr.U fr.hU fr.hUo fr.pt _
    (hΘ.isOpen_inter_preimage hS hO)

theorem injOn_Ψ (w₀ : Fin g → ℂ) :
    Set.InjOn fr.Ψ (fr.D ×ˢ Metric.ball w₀ (fr.ε / 2)) := by
  rintro ⟨x, w⟩ ⟨hx, hw⟩ ⟨x', w'⟩ ⟨hx', hw'⟩ heq
  simp only at hx hw hx' hw'
  set c := chartAt E b₁
  rw [fr.Ψ_eq _ hx, fr.Ψ_eq _ hx'] at heq
  have hxx : c.symm x = c.symm x' := congrArg Sigma.fst heq
  have : x = x' := by
    rw [← c.right_inv (fr.D_sub hx), ← c.right_inv (fr.D_sub hx'), hxx]
  subst this
  obtain ⟨μ, hμ⟩ := (b2f_flatTriv_mk_eq L F fr.U fr.U fr.hU fr.hU fr.pt fr.pt _ _ _ _ _).1 heq
  set T := L.flatTransport fr.U fr.hU ⟨c.symm x, fr.D_mem x hx⟩ fr.pt
  have hl : T (b2_incl _ μ) =
      b2_incl _ (L.transport (b2_LatticeLocalSystem.classIn fr.U fr.hU
        ⟨c.symm x, fr.D_mem x hx⟩ fr.pt) μ) := rfl
  set l := L.transport (b2_LatticeLocalSystem.classIn fr.U fr.hU
        ⟨c.symm x, fr.D_mem x hx⟩ fr.pt) μ
  have hker := (fr.ker x hx ((b2_coord _).symm (fr.J w) - (b2_coord _).symm (fr.J w') +
    b2_incl _ l)).2 (by
      rw [map_add, map_sub, ← hl, LinearEquiv.symm_apply_apply]
      exact hμ)
  rw [map_add, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, map_add,
    map_sub, fr.QJ x hx, fr.QJ x hx] at hker
  have hQl : fr.Q x (b2_coord _ (b2_incl _ l)) = w' - w := by
    rw [← sub_eq_zero, ← hker]; abel
  have hsmall : ‖fr.Q x (b2_coord _ (b2_incl _ l))‖ < fr.ε := by
    rw [hQl, ← dist_eq_norm]
    have := dist_triangle w' w₀ w
    rw [Metric.mem_ball] at hw hw'
    rw [dist_comm w₀ w] at this
    linarith
  have := fr.sep x hx l hsmall
  rw [hQl, sub_eq_zero] at this
  rw [this]

/-- The local inverse of a chart: `Ψ` on `D × ball(w₀, ε/2)`, a homeomorphism onto an open
set.
Source: Griffiths, Publ. Math. IHES 38, §1; Mathlib
`OpenPartialHomeomorph.ofContinuousOpenRestrict`. -/
def lh (hhol : L.IsHolomorphicSubbundle E F) (w₀ : Fin g → ℂ) :
    OpenPartialHomeomorph (E × (Fin g → ℂ)) (b2_totalSpace L F) :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict
    ((fr.injOn_Ψ w₀).toPartialEquiv fr.Ψ _)
    (fr.continuousOn_Ψ.mono (Set.prod_mono le_rfl (Set.subset_univ _)))
    (by
      intro S hS
      change IsOpen (Set.domRestrict _ fr.Ψ '' S)
      rw [Set.domRestrict_eq, Set.image_comp]
      refine fr.isOpen_image_Ψ hhol _ ?_ ?_
      · exact (fr.hDo.prod Metric.isOpen_ball).isOpenMap_subtype_val S hS
      · rintro _ ⟨z, -, rfl⟩
        exact ⟨z.2.1, trivial⟩)
    (fr.hDo.prod Metric.isOpen_ball)

example (hhol : L.IsHolomorphicSubbundle E F) (w₀ : Fin g → ℂ) :
    IsOpen (fr.lh hhol w₀).target := (fr.lh hhol w₀).open_target

theorem lh_source (hhol : L.IsHolomorphicSubbundle E F) (w₀ : Fin g → ℂ) :
    (fr.lh hhol w₀).source = fr.D ×ˢ Metric.ball w₀ (fr.ε / 2) := rfl

theorem lh_coe (hhol : L.IsHolomorphicSubbundle E F) (w₀ : Fin g → ℂ) :
    ⇑(fr.lh hhol w₀) = fr.Ψ := rfl

theorem mem_U (b : B) (hbc : b ∈ (chartAt E b₁).source) (hbD : chartAt E b₁ b ∈ fr.D) :
    b ∈ fr.U := by
  have := fr.D_mem _ hbD
  rwa [(chartAt E b₁).left_inv hbc] at this

theorem Ψ_chart (b : B) (hbc : b ∈ (chartAt E b₁).source) (hbD : chartAt E b₁ b ∈ fr.D)
    (w : Fin g → ℂ) :
    fr.Ψ (chartAt E b₁ b, w) = b2_flatTriv L F fr.U fr.hU fr.pt
      (⟨b, fr.mem_U b hbc hbD⟩, (b2_coord _).symm (fr.J w)) := by
  rw [fr.Ψ_eq _ hbD]
  exact congrArg (fun u ↦ b2_flatTriv L F fr.U fr.hU fr.pt (u, _))
    (Subtype.ext ((chartAt E b₁).left_inv hbc))

theorem ker_chart (b : B) (hbc : b ∈ (chartAt E b₁).source) (hbD : chartAt E b₁ b ∈ fr.D)
    (v : L.cFiber b₁) :
    fr.Q (chartAt E b₁ b) (b2_coord _ v) = 0 ↔
      (L.flatTransport fr.U fr.hU ⟨b, fr.mem_U b hbc hbD⟩ fr.pt).symm v ∈ F b := by
  rw [fr.ker _ hbD]
  have key : ∀ b' (hb' : b' = b) (h' : b' ∈ fr.U),
      (L.flatTransport fr.U fr.hU ⟨b', h'⟩ fr.pt).symm v ∈ F b' ↔
      (L.flatTransport fr.U fr.hU ⟨b, fr.mem_U b hbc hbD⟩ fr.pt).symm v ∈ F b := by
    rintro _ rfl _; rfl
  exact key _ ((chartAt E b₁).left_inv hbc) _

/-- `J ∘ Q` changes a vector by an element of the transported `F`. -/
theorem JQ_sub_mem (b : B) (hbc : b ∈ (chartAt E b₁).source) (hbD : chartAt E b₁ b ∈ fr.D)
    (v : L.cFiber b₁) :
    (L.flatTransport fr.U fr.hU ⟨b, fr.mem_U b hbc hbD⟩ fr.pt).symm
      ((b2_coord _).symm (fr.J (fr.Q (chartAt E b₁ b) (b2_coord _ v)))) -
    (L.flatTransport fr.U fr.hU ⟨b, fr.mem_U b hbc hbD⟩ fr.pt).symm v ∈ F b := by
  rw [← map_sub]
  refine (fr.ker_chart b hbc hbD _).1 ?_
  rw [map_sub, LinearEquiv.apply_symm_apply, map_sub, fr.QJ _ hbD, sub_self]

/-- **Gluing.** If a flat trivialisation over `U` meets the frame's parametrisation at a point
over `b`, then near `b` it factors through the parametrisation by the map
`ṽ ↦ Q_{c b̃}(A ṽ + λ̂)`, with `A` linear and `λ̂` a fixed lattice vector. -/
theorem glue (U : Set B) (hU : IsSimplyConnected U) (hUo : IsOpen U) (b₀ : U) (b : B)
    (hbU : b ∈ U) (hbc : b ∈ (chartAt E b₁).source) (hbD : chartAt E b₁ b ∈ fr.D)
    (v : L.cFiber b₀) (w' : Fin g → ℂ)
    (h : b2_flatTriv L F U hU b₀ (⟨b, hbU⟩, v) = fr.Ψ (chartAt E b₁ b, w')) :
    ∃ (A : L.cFiber b₀ →ₗ[ℂ] (Fin (Module.finrank ℂ (L.cFiber b₁)) → ℂ))
      (lh : Fin (Module.finrank ℂ (L.cFiber b₁)) → ℂ),
      w' = fr.Q (chartAt E b₁ b) (A v + lh) ∧
      ∀ᶠ b' in nhds b, ∃ h1 : b' ∈ U, b' ∈ (chartAt E b₁).source ∧ chartAt E b₁ b' ∈ fr.D ∧
        ∀ v', b2_flatTriv L F U hU b₀ (⟨b', h1⟩, v') =
          fr.Ψ (chartAt E b₁ b', fr.Q (chartAt E b₁ b') (A v' + lh)) := by
  have := ChartedSpace.locallyPathConnectedSpace E B
  have hbq := fr.mem_U b hbc hbD
  rw [fr.Ψ_chart b hbc hbD] at h
  obtain ⟨μ, hμ⟩ := (b2f_flatTriv_mk_eq L F U fr.U hU fr.hU b₀ fr.pt b hbU hbq v _).1 h
  dsimp only [b2f_Frame.pt] at hμ
  let l₀ := L.transport (b2_LatticeLocalSystem.classIn fr.U fr.hU ⟨b, hbq⟩ fr.pt) μ
  have hl₀ : L.flatTransport fr.U fr.hU ⟨b, hbq⟩ fr.pt (b2_incl _ μ) = b2_incl _ l₀ := rfl
  let A : L.cFiber b₀ →ₗ[ℂ] (Fin (Module.finrank ℂ (L.cFiber b₁)) → ℂ) :=
    (b2_coord (L.cFiber b₁)).toLinearMap ∘ₗ
      (L.flatTransport fr.U fr.hU ⟨b, hbq⟩ fr.pt).toLinearMap ∘ₗ
      (L.flatTransport U hU ⟨b, hbU⟩ b₀).symm.toLinearMap
  have hA : ∀ v', A v' = b2_coord (L.cFiber b₁) (L.flatTransport fr.U fr.hU ⟨b, hbq⟩ fr.pt
      ((L.flatTransport U hU ⟨b, hbU⟩ b₀).symm v')) := fun _ ↦ rfl
  refine ⟨A, b2_coord (L.cFiber b₁) (b2_incl _ l₀), ?_, ?_⟩
  · have hk := (fr.ker_chart b hbc hbD (L.flatTransport fr.U fr.hU ⟨b, hbq⟩ fr.pt
        ((L.flatTransport U hU ⟨b, hbU⟩ b₀).symm v) -
        (b2_coord (L.cFiber b₁)).symm (fr.J w') + b2_incl _ l₀)).2 (by
      rw [map_add, map_sub, LinearEquiv.symm_apply_apply, ← hl₀, LinearEquiv.symm_apply_apply]
      exact hμ)
    rw [map_add, map_sub, LinearEquiv.apply_symm_apply, map_add, map_sub, fr.QJ _ hbD,
      ← hA] at hk
    rw [eq_comm, map_add, ← sub_eq_zero, ← hk]
    abel
  · have hSo : IsOpen (U ∩ fr.U ∩ ((chartAt E b₁).source ∩ chartAt E b₁ ⁻¹' fr.D)) :=
      (hUo.inter fr.hUo).inter ((chartAt E b₁).isOpen_inter_preimage fr.hDo)
    have hbS : b ∈ U ∩ fr.U ∩ ((chartAt E b₁).source ∩ chartAt E b₁ ⁻¹' fr.D) :=
      ⟨⟨hbU, hbq⟩, hbc, hbD⟩
    filter_upwards [(hSo.pathComponentIn b).mem_nhds (mem_pathComponentIn_self hbS)] with b' hb'
    have hJ : JoinedIn (U ∩ fr.U ∩ ((chartAt E b₁).source ∩ chartAt E b₁ ⁻¹' fr.D)) b b' := hb'
    obtain ⟨⟨hb'U, -⟩, hb'c, hb'D⟩ := hJ.mem.2
    refine ⟨hb'U, hb'c, hb'D, fun v' ↦ ?_⟩
    rw [fr.Ψ_chart b' hb'c hb'D]
    have htr := L.b2f_transfer_path U fr.U hU fr.hU b₀ fr.pt hbU hbq hb'U
      (fr.mem_U b' hb'c hb'D) hJ.somePath (fun t ↦ (hJ.somePath_mem t).1) v'
    have hy : (b2_coord (L.cFiber b₁)).symm (A v' + b2_coord (L.cFiber b₁) (b2_incl _ l₀)) =
        L.flatTransport fr.U fr.hU ⟨b', fr.mem_U b' hb'c hb'D⟩ fr.pt
          ((L.flatTransport U hU ⟨b', hb'U⟩ b₀).symm v') + b2_incl _ l₀ := by
      rw [map_add, hA, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
      exact congrArg (· + _) htr
    have hJQ := fr.JQ_sub_mem b' hb'c hb'D
      ((b2_coord (L.cFiber b₁)).symm (A v' + b2_coord (L.cFiber b₁) (b2_incl _ l₀)))
    rw [LinearEquiv.apply_symm_apply, hy,
      map_add (L.flatTransport fr.U fr.hU ⟨b', fr.mem_U b' hb'c hb'D⟩ fr.pt).symm,
      LinearEquiv.symm_apply_apply] at hJQ
    refine (b2f_flatTriv_mk_eq L F U fr.U hU fr.hU b₀ fr.pt b' hb'U _ v' _).2
      ⟨(L.transport (b2_LatticeLocalSystem.classIn fr.U fr.hU
        ⟨b', fr.mem_U b' hb'c hb'D⟩ fr.pt)).symm l₀, ?_⟩
    have hinc : (L.flatTransport fr.U fr.hU ⟨b', fr.mem_U b' hb'c hb'D⟩ fr.pt).symm
        (b2_incl _ l₀) = b2_incl _ ((L.transport (b2_LatticeLocalSystem.classIn fr.U fr.hU
          ⟨b', fr.mem_U b' hb'c hb'D⟩ fr.pt)).symm l₀) := rfl
    rw [hinc] at hJQ
    have := (F b').neg_mem hJQ
    convert this using 1
    abel

end b2f_Frame
end Frame

section FrameExists

/-- **Holomorphic projections along a moving frame.** Given holomorphic vectors `σ_k(x)`,
independent at `x₁`, in `ℂⁿ` with `n = 2g`, there are an open `D ∋ x₁`, a complement `J` of their
span at `x₁` and holomorphic `Q_x` (`x ∈ D`) with `Q_x ∘ J = id` and kernel the span of the
`σ_k(x)`: `Q_x` is the second component of the inverse of `(α, w) ↦ Σ α_k σ_k(x) + J w`. -/
theorem b2f_frame_core {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n g : ℕ}
    (hn : n = g + g) (D₀ : Set E) (hD₀ : IsOpen D₀) (x₁ : E) (hx₁ : x₁ ∈ D₀)
    (σ : Fin g → E → (Fin n → ℂ)) (hσ : ∀ k, ContDiffOn ℂ ω (σ k) D₀)
    (hli : LinearIndependent ℂ fun k ↦ σ k x₁) :
    ∃ (D : Set E) (Q : E → ((Fin n → ℂ) →L[ℂ] (Fin g → ℂ))) (J : (Fin g → ℂ) →L[ℂ] (Fin n → ℂ)),
      IsOpen D ∧ x₁ ∈ D ∧ D ⊆ D₀ ∧ ContDiffOn ℂ ω Q D ∧ (∀ x ∈ D, ∀ w, Q x (J w) = w) ∧
      (∀ x ∈ D, LinearIndependent ℂ fun k ↦ σ k x) ∧
      (∀ x ∈ D, ∀ y, Q x y = 0 ↔ y ∈ Submodule.span ℂ (Set.range fun k ↦ σ k x)) := by
  set S₁ := Submodule.span ℂ (Set.range fun k ↦ σ k x₁)
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl S₁
  have hS₁ : Module.finrank ℂ S₁ = g := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hWr : Module.finrank ℂ W = g := by
    have := Submodule.finrank_add_eq_of_isCompl hW
    rw [hS₁, Module.finrank_fin_fun] at this
    omega
  let eW := Module.finBasisOfFinrankEq ℂ W hWr
  let J : (Fin g → ℂ) →L[ℂ] (Fin n → ℂ) :=
    LinearMap.toContinuousLinearMap (W.subtype ∘ₗ eW.equivFun.symm.toLinearMap)
  have hJinj : Function.Injective J := by
    intro w w' h
    exact eW.equivFun.symm.injective (Subtype.ext h)
  have hJW : ∀ w, J w ∈ W := fun w ↦ (eW.equivFun.symm w).2
  let P := (Fin g → ℂ) × (Fin g → ℂ)
  let M : E → (P →L[ℂ] (Fin n → ℂ)) := fun x ↦
    ∑ k, ((ContinuousLinearMap.proj k).comp (ContinuousLinearMap.fst ℂ _ _)).smulRight (σ k x) +
      J.comp (ContinuousLinearMap.snd ℂ _ _)
  have hM : ∀ x (p : P), M x p = ∑ k, p.1 k • σ k x + J p.2 := by
    intro x p
    simp [M]
    rfl
  have hM₁inj : Function.Injective (M x₁) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨α, w⟩ h
    rw [hM] at h
    have h1 : ∑ k, α k • σ k x₁ ∈ S₁ :=
      Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    have h2 : ∑ k, α k • σ k x₁ ∈ W := by
      rw [eq_neg_of_add_eq_zero_left h]; exact W.neg_mem (hJW w)
    have h3 : ∑ k, α k • σ k x₁ = 0 := (Submodule.disjoint_def.1 hW.disjoint) _ h1 h2
    have hα : α = 0 := by
      have := (Fintype.linearIndependent_iff.1 hli) α h3
      funext k; exact this k
    rw [h3, zero_add] at h
    have hw : w = 0 := hJinj (h.trans J.map_zero.symm)
    rw [hα, hw]; rfl
  have hdim : Module.finrank ℂ P = Module.finrank ℂ (Fin n → ℂ) := by
    simp [P, Module.finrank_prod, hn]
  let e₁ : P ≃L[ℂ] (Fin n → ℂ) :=
    (LinearMap.linearEquivOfInjective (M x₁ : P →ₗ[ℂ] (Fin n → ℂ)) hM₁inj hdim).toContinuousLinearEquiv
  have he₁ : ∀ p, e₁ p = M x₁ p := fun _ ↦ rfl
  let N : E → ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) := fun x ↦ (M x).comp (e₁.symm : (Fin n → ℂ) →L[ℂ] P)
  have hMc : ContDiffOn ℂ ω M D₀ := by
    refine ContDiffOn.add ?_ contDiffOn_const
    refine ContDiffOn.sum fun k _ ↦ ?_
    exact ((ContinuousLinearMap.smulRightL ℂ P (Fin n → ℂ)
      ((ContinuousLinearMap.proj k).comp (ContinuousLinearMap.fst ℂ _ _))).contDiff.comp_contDiffOn
      (hσ k))
  have hNc : ContDiffOn ℂ ω N D₀ := hMc.clm_comp contDiffOn_const
  have hN₁ : N x₁ = 1 := by
    ext1 y
    change M x₁ (e₁.symm y) = y
    rw [← he₁, ContinuousLinearEquiv.apply_symm_apply]
  have hMN : ∀ x p, M x p = N x (e₁ p) := by
    intro x p
    change M x p = M x (e₁.symm (e₁ p))
    rw [ContinuousLinearEquiv.symm_apply_apply]
  set D := D₀ ∩ N ⁻¹' {u | IsUnit u} with hD
  have hDo : IsOpen D := hNc.continuousOn.isOpen_inter_preimage hD₀ Units.isOpen
  have hx₁D : x₁ ∈ D := ⟨hx₁, by simp only [Set.mem_preimage, Set.mem_ofPred_eq, hN₁, isUnit_one]⟩
  let Q : E → ((Fin n → ℂ) →L[ℂ] (Fin g → ℂ)) := fun x ↦
    ((ContinuousLinearMap.snd ℂ (Fin g → ℂ) (Fin g → ℂ)).comp
      (e₁.symm : (Fin n → ℂ) →L[ℂ] P)).comp (Ring.inverse (N x))
  have hQc : ContDiffOn ℂ ω Q D := by
    intro x hx
    obtain ⟨u, hu⟩ := hx.2
    have h1 : ContDiffAt ℂ ω (fun y ↦ Ring.inverse (N y)) x := by
      have := contDiffAt_ringInverse ℂ (n := ω) u
      rw [hu] at this
      exact this.comp x (hNc.contDiffAt (hD₀.mem_nhds hx.1))
    exact (contDiffAt_const.clm_comp h1).contDiffWithinAt
  have hinv : ∀ x ∈ D, ∀ y, N x (Ring.inverse (N x) y) = y ∧ Ring.inverse (N x) (N x y) = y := by
    intro x hx y
    have hu : IsUnit (N x) := hx.2
    constructor
    · rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel _ hu]; rfl
    · rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel _ hu]; rfl
  have hQM : ∀ x ∈ D, ∀ p, Q x (M x p) = p.2 := by
    intro x hx p
    rw [hMN]
    change (e₁.symm (Ring.inverse (N x) (N x (e₁ p)))).2 = p.2
    rw [(hinv x hx _).2, ContinuousLinearEquiv.symm_apply_apply]
  have hMsurj : ∀ x ∈ D, ∀ y, M x (e₁.symm (Ring.inverse (N x) y)) = y := by
    intro x hx y
    rw [hMN, ContinuousLinearEquiv.apply_symm_apply, (hinv x hx y).1]
  have hMinj : ∀ x ∈ D, Function.Injective (M x) := by
    intro x hx p q h
    rw [hMN, hMN] at h
    have := congrArg (fun y ↦ Ring.inverse (N x) y) h
    simp only [(hinv x hx _).2] at this
    exact e₁.injective this
  refine ⟨D, Q, J, hDo, hx₁D, Set.inter_subset_left, hQc, ?_, ?_, ?_⟩
  · intro x hx w
    have := hQM x hx (0, w)
    rwa [hM, Finset.sum_eq_zero (fun k _ ↦ by simp), zero_add] at this
  · intro x hx
    rw [Fintype.linearIndependent_iff]
    intro α hα
    have h0 : M x (α, 0) = M x 0 := by
      rw [map_zero, hM]
      simp only [hα, zero_add]
      exact J.map_zero
    have := congrArg Prod.fst (hMinj x hx h0)
    intro k
    exact congrFun this k
  · intro x hx y
    constructor
    · intro hy
      obtain ⟨⟨α, w⟩, rfl⟩ : ∃ p, M x p = y := ⟨_, hMsurj x hx y⟩
      rw [hQM x hx] at hy
      simp only at hy
      rw [hM, hy, J.map_zero, add_zero]
      exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · intro hy
      obtain ⟨α, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hy
      have : ∑ k, α k • σ k x = M x (α, 0) := by rw [hM, J.map_zero, add_zero]
      rw [this, hQM x hx]

/-- **Uniform separation of a lattice.** If `t ↦ Σ tᵢ Q_{x₁} uᵢ` is injective over `ℝ` and `Q` is
continuous at `x₁`, then near `x₁` the vectors `Σ mᵢ Q_x uᵢ`, `m ∈ ℤ^ι \ 0`, stay at distance at
least `ε` from `0`. -/
theorem b2f_sep_core {X K : Type*} [TopologicalSpace X] [NormedAddCommGroup K] [NormedSpace ℂ K]
    {g : ℕ} {ι : Type*} [Fintype ι] (Q : X → (K →L[ℂ] (Fin g → ℂ))) (x₁ : X)
    (hQ : ContinuousAt Q x₁) (u : ι → K)
    (hinj : Function.Injective (Fintype.linearCombination ℝ (fun i ↦ Q x₁ (u i)))) :
    ∃ ε > 0, ∀ᶠ x in nhds x₁, ∀ m : ι → ℤ, ‖∑ i, (m i : ℝ) • Q x (u i)‖ < ε → m = 0 := by
  obtain ⟨K₀, -, hanti⟩ := (Fintype.linearCombination ℝ (fun i ↦ Q x₁ (u i))).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.2 hinj)
  obtain ⟨c, hc, hle⟩ := antilipschitzWith_iff_exists_mul_le_norm.1 ⟨K₀, hanti⟩
  set S := ∑ i, ‖u i‖ + 1 with hS
  have hSpos : 0 < S := by positivity
  refine ⟨c / 2, by positivity, ?_⟩
  have hev : ∀ᶠ x in nhds x₁, ‖Q x - Q x₁‖ < c / (2 * S) := by
    have := hQ.eventually (Metric.ball_mem_nhds (Q x₁) (by positivity : 0 < c / (2 * S)))
    filter_upwards [this] with x hx
    rwa [dist_eq_norm] at hx
  filter_upwards [hev] with x hx m hm
  by_contra hm0
  obtain ⟨i₀, hi₀⟩ : ∃ i, m i ≠ 0 := by
    by_contra h; push Not at h; exact hm0 (funext h)
  set t : ι → ℝ := fun i ↦ (m i : ℝ)
  have ht1 : 1 ≤ ‖t‖ := by
    have h1 : (1 : ℝ) ≤ |(m i₀ : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hi₀
    exact h1.trans (by simpa [t, Real.norm_eq_abs] using norm_le_pi_norm t i₀)
  have hR : Fintype.linearCombination ℝ (fun i ↦ Q x₁ (u i)) t = ∑ i, t i • Q x₁ (u i) := by
    simp [Fintype.linearCombination_apply]
  have hdiff : ‖∑ i, t i • Q x₁ (u i) - ∑ i, t i • Q x (u i)‖ ≤ ‖t‖ * (c / 2) := by
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ i, (t i • Q x₁ (u i) - t i • Q x (u i))‖
        ≤ ∑ i, ‖t i • Q x₁ (u i) - t i • Q x (u i)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖t‖ * (c / (2 * S) * ‖u i‖) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rw [← smul_sub, norm_smul, ← sub_apply]
          gcongr
          · exact norm_le_pi_norm t i
          · calc ‖(Q x₁ - Q x) (u i)‖ ≤ ‖Q x₁ - Q x‖ * ‖u i‖ := (Q x₁ - Q x).le_opNorm _
              _ ≤ c / (2 * S) * ‖u i‖ := by
                gcongr; rw [norm_sub_rev]; exact hx.le
      _ = ‖t‖ * (c / (2 * S)) * (S - 1) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, hS]; ring
      _ ≤ ‖t‖ * (c / 2) := by
          rw [mul_assoc]
          gcongr
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  have h1 := hle t
  rw [hR] at h1
  have h2 : ‖∑ i, t i • Q x₁ (u i)‖ ≤ ‖∑ i, t i • Q x (u i)‖ + ‖t‖ * (c / 2) := by
    have := norm_le_insert' (∑ i, t i • Q x₁ (u i)) (∑ i, t i • Q x (u i))
    linarith [norm_sub_rev (∑ i, t i • Q x₁ (u i)) (∑ i, t i • Q x (u i))]
  have : c * ‖t‖ < c / 2 + ‖t‖ * (c / 2) := by
    have hm' : ‖∑ i, t i • Q x (u i)‖ < c / 2 := hm
    linarith
  nlinarith

section Exists
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]

theorem b2f_sigma_contDiffOn [IsManifold 𝓘(ℂ, E) ω B] {n : ℕ} (f : B → (Fin n → ℂ)) (U : Set B)
    (hf : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) ω f U) (b₁ : B) :
    ContDiffOn ℂ ω (f ∘ (chartAt E b₁).symm)
      ((chartAt E b₁).target ∩ (chartAt E b₁).symm ⁻¹' U) := by
  have := (contMDiffOn_iff.1 hf).2 b₁ (0 : Fin n → ℂ)
  simpa [mfld_simps] using this

/-- **Frames exist** at every point of a holomorphic weight-one family of rank `2g`. -/
theorem b2f_frame_exists [IsManifold 𝓘(ℂ, E) ω B] (L : b2_LatticeLocalSystem B)
    (F : ∀ b, Submodule ℂ (L.cFiber b)) (hhol : L.IsHolomorphicSubbundle E F) (g : ℕ)
    (hg : ∀ b, Module.finrank ℤ (L.fiber b) = 2 * g)
    (hrank : ∀ b, 2 * Module.finrank ℂ ((L.cFiber b) ⧸ F b) = Module.finrank ℤ (L.fiber b))
    (hbasis : ∀ b (β : Module.Basis (Module.Free.ChooseBasisIndex ℤ (L.fiber b)) ℤ (L.fiber b)),
      ∃ cb : Module.Basis (Module.Free.ChooseBasisIndex ℤ (L.fiber b)) ℝ ((L.cFiber b) ⧸ F b),
        ∀ i, cb i = b2_latticeMap (L.fiber b) (F b) (β i))
    (b₁ : B) : Nonempty (b2f_Frame E L F g b₁) := by
  obtain ⟨U, hU, h₁, hUo, r, s, hs, hspan⟩ := hhol b₁
  have hfinF : ∀ b, Module.finrank ℂ (F b) = g := by
    intro b
    have h1 := Submodule.finrank_quotient_add_finrank (F b)
    have h2 : Module.finrank ℂ (L.cFiber b) = 2 * g := by
      show Module.finrank ℂ (ℂ ⊗[ℤ] L.fiber b) = 2 * g
      rw [Module.finrank_baseChange, hg]
    have h3 := hrank b
    rw [hg] at h3
    omega
  have hn : Module.finrank ℂ (L.cFiber b₁) = g + g := by
    show Module.finrank ℂ (ℂ ⊗[ℤ] L.fiber b₁) = g + g
    rw [Module.finrank_baseChange, hg]; ring
  have hG : ∀ b (hb : b ∈ U), Submodule.span ℂ (Set.range fun i ↦
      L.flatCoord U hU ⟨b₁, h₁⟩ (s i) b) =
      (F b).map (L.flatTransport U hU ⟨b, hb⟩ ⟨b₁, h₁⟩).toLinearMap := by
    intro b hb
    have : (fun i ↦ L.flatCoord U hU ⟨b₁, h₁⟩ (s i) b) =
        (L.flatTransport U hU ⟨b, hb⟩ ⟨b₁, h₁⟩) ∘ fun i ↦ s i b := by
      funext i
      simp only [b2_LatticeLocalSystem.flatCoord, dite_eq_left hb, Function.comp_apply]
    rw [this, Set.range_comp, ← hspan b hb]
    exact (Submodule.map_span (L.flatTransport U hU ⟨b, hb⟩ ⟨b₁, h₁⟩).toLinearMap _).symm
  have hG₁ : Module.finrank ℂ ((F b₁).map
      (L.flatTransport U hU ⟨b₁, h₁⟩ ⟨b₁, h₁⟩).toLinearMap) = g := by
    rw [LinearEquiv.finrank_map_eq]; exact hfinF b₁
  let fb := Module.finBasisOfFinrankEq ℂ _ hG₁
  have hcoef : ∀ k, ∃ a : Fin r → ℂ,
      ∑ i, a i • L.flatCoord U hU ⟨b₁, h₁⟩ (s i) b₁ = (fb k : L.cFiber b₁) := by
    intro k
    have h' : (fb k : L.cFiber b₁) ∈ Submodule.span ℂ (Set.range fun i ↦
        L.flatCoord U hU ⟨b₁, h₁⟩ (s i) b₁) := by
      rw [hG b₁ h₁]; exact (fb k).2
    exact (Submodule.mem_span_range_iff_exists_fun ℂ).1 h'
  choose a ha using hcoef
  let κ := b2_coord (L.cFiber b₁)
  let σ : Fin g → E → (Fin (Module.finrank ℂ (L.cFiber b₁)) → ℂ) := fun k x ↦
    κ (∑ i, a k i • L.flatCoord U hU ⟨b₁, h₁⟩ (s i) ((chartAt E b₁).symm x))
  have hD₀ : IsOpen ((chartAt E b₁).target ∩ (chartAt E b₁).symm ⁻¹' U) :=
    (chartAt E b₁).isOpen_inter_preimage_symm hUo
  have hx₁ : chartAt E b₁ b₁ ∈ (chartAt E b₁).target ∩ (chartAt E b₁).symm ⁻¹' U :=
    ⟨mem_chart_target E b₁, by
      rw [Set.mem_preimage, (chartAt E b₁).left_inv (mem_chart_source E b₁)]; exact h₁⟩
  have hσ : ∀ k, ContDiffOn ℂ ω (σ k)
      ((chartAt E b₁).target ∩ (chartAt E b₁).symm ⁻¹' U) := by
    intro k
    have hi : ∀ i, ContDiffOn ℂ ω
        (fun x ↦ κ (L.flatCoord U hU ⟨b₁, h₁⟩ (s i) ((chartAt E b₁).symm x)))
        ((chartAt E b₁).target ∩ (chartAt E b₁).symm ⁻¹' U) := fun i ↦
      b2f_sigma_contDiffOn _ U (hs i) b₁
    have : σ k = fun x ↦ ∑ i, a k i •
        κ (L.flatCoord U hU ⟨b₁, h₁⟩ (s i) ((chartAt E b₁).symm x)) := by
      funext x; simp only [σ, map_sum, map_smul]
    rw [this]
    exact ContDiffOn.sum fun i _ ↦ (hi i).const_smul _
  have hσ₁ : ∀ k, σ k (chartAt E b₁ b₁) = κ (fb k) := by
    intro k
    simp only [σ, (chartAt E b₁).left_inv (mem_chart_source E b₁), ha]
  have hli : LinearIndependent ℂ fun k ↦ σ k (chartAt E b₁ b₁) := by
    simp only [hσ₁]
    have := fb.linearIndependent.map' (κ.toLinearMap ∘ₗ Submodule.subtype _) (LinearMap.ker_eq_bot.2 (κ.injective.comp Subtype.val_injective))
    exact this
  obtain ⟨D', Q, J, hD'o, hx₁D', hD'D₀, hQ, hQJ, hliD, hker⟩ :=
    b2f_frame_core hn _ hD₀ _ hx₁ σ hσ hli
  have hker' : ∀ x (hx : x ∈ D') (v : L.cFiber b₁), Q x (κ v) = 0 ↔
      (L.flatTransport U hU ⟨(chartAt E b₁).symm x, (hD'D₀ hx).2⟩ ⟨b₁, h₁⟩).symm v ∈
        F ((chartAt E b₁).symm x) := by
    intro x hx v
    have hb : (chartAt E b₁).symm x ∈ U := (hD'D₀ hx).2
    have hspanσ : Submodule.span ℂ (Set.range fun k ↦ σ k x) =
        (Submodule.span ℂ (Set.range fun i ↦
          L.flatCoord U hU ⟨b₁, h₁⟩ (s i) ((chartAt E b₁).symm x))).map κ.toLinearMap := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        refine Submodule.mem_map_of_mem (Submodule.sum_mem _ fun i _ ↦
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
      · rw [finrank_span_eq_card (hliD x hx), Fintype.card_fin, LinearEquiv.finrank_map_eq,
          hG _ hb, LinearEquiv.finrank_map_eq, hfinF]
    rw [hker x hx, hspanσ, hG _ hb, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply,
      Submodule.mem_map_equiv]
  let β := Module.Free.chooseBasis ℤ (L.fiber b₁)
  let u : Module.Free.ChooseBasisIndex ℤ (L.fiber b₁) → (Fin (Module.finrank ℂ (L.cFiber b₁)) → ℂ) :=
    fun i ↦ κ (b2_incl _ (β i))
  have hQl : ∀ x (l : L.fiber b₁), Q x (κ (b2_incl _ l)) =
      ∑ i, ((β.repr l i : ℤ) : ℝ) • Q x (u i) := by
    intro x l
    conv_lhs => rw [← β.sum_repr l]
    rw [map_sum (b2_incl _), map_sum κ, map_sum (Q x)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_zsmul, map_zsmul, map_zsmul, Int.cast_smul_eq_zsmul]
  have hinj : Function.Injective (Fintype.linearCombination ℝ (fun i ↦ Q (chartAt E b₁ b₁) (u i))) := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    rw [Fintype.linearCombination_apply] at ht
    have h1 : Q (chartAt E b₁ b₁) (κ (∑ i, (t i : ℂ) • b2_incl _ (β i))) = 0 := by
      rw [← ht, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_smul, map_smul, Complex.coe_smul]
    rw [hker' _ hx₁D'] at h1
    have key : ∀ (w : L.cFiber b₁) b' (hb' : b' = b₁) (h' : b' ∈ U),
        (L.flatTransport U hU ⟨b', h'⟩ ⟨b₁, h₁⟩).symm w ∈ F b' →
        (L.flatTransport U hU ⟨b₁, h₁⟩ ⟨b₁, h₁⟩).symm w ∈ F b₁ := by
      rintro _ _ rfl _ h; exact h
    have h2 := key _ _ ((chartAt E b₁).left_inv (mem_chart_source E b₁)) _ h1
    let τ := L.transport (b2_LatticeLocalSystem.classIn U hU ⟨b₁, h₁⟩ ⟨b₁, h₁⟩)
    let β' := β.map τ.symm.toIntLinearEquiv
    have hT : ∀ y, (L.flatTransport U hU ⟨b₁, h₁⟩ ⟨b₁, h₁⟩).symm (b2_incl _ y) =
        b2_incl _ (τ.symm y) := fun _ ↦ rfl
    have hβ' : ∀ i, β' i = τ.symm (β i) := fun i ↦ rfl
    have h3 : ∑ i, (t i : ℂ) • b2_incl _ (β' i) ∈ F b₁ := by
      rw [map_sum] at h2
      simpa only [map_smul, hT, hβ'] using h2
    obtain ⟨cb, hcb⟩ := hbasis b₁ β'
    have h4 : ∑ i, t i • cb i = 0 := by
      have := (Submodule.Quotient.mk_eq_zero (F b₁)).2 h3
      rw [← Submodule.mkQ_apply, map_sum] at this
      simp only [hcb]
      convert this using 2 with i
      rw [map_smul, Complex.coe_smul]
      rfl
    exact funext (Fintype.linearIndependent_iff.1 cb.linearIndependent t h4)
  obtain ⟨ε, hε, hev⟩ := b2f_sep_core Q _ (hQ.continuousOn.continuousAt (hD'o.mem_nhds hx₁D'))
    u hinj
  obtain ⟨O, hOP, hOo, hx₁O⟩ := eventually_nhds_iff.1 hev
  refine ⟨⟨U, hU, hUo, h₁, D' ∩ O, hD'o.inter hOo, ⟨hx₁D', hx₁O⟩,
    fun x hx ↦ (hD'D₀ hx.1).1, fun x hx ↦ (hD'D₀ hx.1).2, Q, hQ.mono Set.inter_subset_left, J,
    fun x hx ↦ hQJ x hx.1, fun x hx v ↦ hker' x hx.1 v, ε, hε, ?_⟩⟩
  intro x hx l hl
  rw [hQl] at hl ⊢
  rw [hOP x hx.2 _ hl]
  simp
end Exists

end FrameExists

section Charts
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]

/-- Transition maps between charts of a complex manifold are holomorphic at each point of their
domain. -/
theorem b2f_chart_trans_contDiffAt [IsManifold 𝓘(ℂ, E) ω B] (b b' : B) (x : E)
    (hx : x ∈ (chartAt E b).target) (hx' : (chartAt E b).symm x ∈ (chartAt E b').source) :
    ContDiffAt ℂ ω (fun y ↦ chartAt E b' ((chartAt E b).symm y)) x := by
  have h := (StructureGroupoid.compatible (contDiffGroupoid ω 𝓘(ℂ, E)) (chart_mem_atlas E b)
    (chart_mem_atlas E b'))
  have h2 := (mem_groupoid_of_pregroupoid.1 h).1
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Set.range_id, Set.preimage_id, Set.inter_univ, Function.id_comp, Function.comp_id] at h2
  have hmem : x ∈ ((chartAt E b).symm ≫ₕ chartAt E b').source := by
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨hx, hx'⟩
  exact (h2 x hmem).contDiffAt
    (((chartAt E b).symm ≫ₕ chartAt E b').open_source.mem_nhds hmem)
end Charts

section Charts2
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]
variable {L : b2_LatticeLocalSystem B} {F : ∀ b, Submodule ℂ (L.cFiber b)} {g : ℕ}

namespace b2f_Frame
variable {b₁ : B} (fr : b2f_Frame E L F g b₁)

theorem Ψ_chart_JQ (b : B) (hbc : b ∈ (chartAt E b₁).source) (hbD : chartAt E b₁ b ∈ fr.D)
    (v : L.cFiber b₁) :
    fr.Ψ (chartAt E b₁ b, fr.Q (chartAt E b₁ b) (b2_coord _ v)) =
      b2_flatTriv L F fr.U fr.hU fr.pt (⟨b, fr.mem_U b hbc hbD⟩, v) := by
  rw [fr.Ψ_chart b hbc hbD]
  refine (b2f_flatTriv_mk_eq L F fr.U fr.U fr.hU fr.hU fr.pt fr.pt b _ _ _ _).2 ⟨0, ?_⟩
  rw [map_zero, add_zero]
  exact fr.JQ_sub_mem b hbc hbD v

theorem exists_Ψ_eq (t : b2_fiberTorus L F b₁) :
    ∃ w, fr.Ψ (chartAt E b₁ b₁, w) = ⟨b₁, t⟩ := by
  obtain ⟨t', rfl⟩ := QuotientAddGroup.mk_surjective t
  obtain ⟨v₀, rfl⟩ := Submodule.Quotient.mk_surjective _ t'
  have hbc := mem_chart_source E b₁
  have hbD : chartAt E b₁ b₁ ∈ fr.D := fr.memD
  refine ⟨fr.Q (chartAt E b₁ b₁) (b2_coord _ (L.flatTransport fr.U fr.hU
    ⟨b₁, fr.mem_U b₁ hbc hbD⟩ fr.pt v₀)), ?_⟩
  rw [fr.Ψ_chart_JQ b₁ hbc hbD]
  simp only [b2_flatTriv, LinearEquiv.symm_apply_apply]
  rfl

end b2f_Frame

variable (hhol : L.IsHolomorphicSubbundle E F) (fr : ∀ b, b2f_Frame E L F g b)

/-- The fibre coordinate of the centre of the chart at `p`.
Source: Griffiths, Publ. Math. IHES 38, §1. -/
def b2f_wpt (p : b2_totalSpace L F) : Fin g → ℂ :=
  Classical.choose ((fr p.1).exists_Ψ_eq p.2)

theorem b2f_wpt_spec (p : b2_totalSpace L F) :
    (fr p.1).Ψ (chartAt E p.1 p.1, b2f_wpt fr p) = p :=
  Classical.choose_spec ((fr p.1).exists_Ψ_eq p.2)

/-- The local inverse of the chart at `p`.
Source: Griffiths, Publ. Math. IHES 38, §1; Huybrechts, *Complex Geometry*, §2.3. -/
def b2f_lhAt (p : b2_totalSpace L F) :
    OpenPartialHomeomorph (E × (Fin g → ℂ)) (b2_totalSpace L F) :=
  (fr p.1).lh hhol (b2f_wpt fr p)

example (p : b2_totalSpace L F) : (b2f_lhAt hhol fr p) (chartAt E p.1 p.1, b2f_wpt fr p) = p :=
  b2f_wpt_spec fr p

theorem b2f_center_mem (p : b2_totalSpace L F) :
    (chartAt E p.1 p.1, b2f_wpt fr p) ∈ (b2f_lhAt hhol fr p).source :=
  ⟨(fr p.1).memD, Metric.mem_ball_self (half_pos (fr p.1).ε_pos)⟩

/-- **The charted space of the total space**, modelled on `E × ℂ^g`: the chart at `p` is the
inverse of the frame parametrisation at `p.1` near the point over `p`.
Source: Griffiths, Publ. Math. IHES 38, §1; Huybrechts, *Complex Geometry*, §2.3; Mathlib
`ChartedSpace`. -/
@[instance_reducible]
def b2f_cs : ChartedSpace (E × (Fin g → ℂ)) (b2_totalSpace L F) where
  atlas := Set.range fun p ↦ (b2f_lhAt hhol fr p).symm
  chartAt p := (b2f_lhAt hhol fr p).symm
  mem_chart_source p := by
    rw [OpenPartialHomeomorph.symm_source]
    have := (b2f_lhAt hhol fr p).map_source (b2f_center_mem hhol fr p)
    rwa [b2f_lhAt, b2f_Frame.lh_coe, ← b2f_lhAt, b2f_wpt_spec] at this
  chart_mem_atlas p := ⟨p, rfl⟩

example (p : b2_totalSpace L F) :
    (b2f_cs hhol fr).chartAt p = (b2f_lhAt hhol fr p).symm := rfl


theorem b2f_trans_contDiffAt [IsManifold 𝓘(ℂ, E) ω B] (p q : b2_totalSpace L F)
    (z : E × (Fin g → ℂ)) (hz : z ∈ (b2f_lhAt hhol fr p ≫ₕ (b2f_lhAt hhol fr q).symm).source) :
    ContDiffAt ℂ ω (b2f_lhAt hhol fr p ≫ₕ (b2f_lhAt hhol fr q).symm) z := by
  have := ChartedSpace.locallyPathConnectedSpace E B
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hz
  obtain ⟨hzs, hzt⟩ := hz
  have hz1 : z.1 ∈ (fr p.1).D := hzs.1
  set z' := (b2f_lhAt hhol fr q).symm (b2f_lhAt hhol fr p z) with hz'
  have hz's : z' ∈ (b2f_lhAt hhol fr q).source := (b2f_lhAt hhol fr q).map_target hzt
  have hz'1 : z'.1 ∈ (fr q.1).D := hz's.1
  have hy : (fr q.1).Ψ z' = (fr p.1).Ψ z := (b2f_lhAt hhol fr q).right_inv hzt
  rw [(fr q.1).Ψ_eq _ hz'1, (fr p.1).Ψ_eq _ hz1] at hy
  have hbb : (chartAt E q.1).symm z'.1 = (chartAt E p.1).symm z.1 := congrArg Sigma.fst hy
  set b := (chartAt E p.1).symm z.1 with hb
  have hbq : b ∈ (chartAt E q.1).source := by
    rw [← hbb]; exact (chartAt E q.1).map_target ((fr q.1).D_sub hz'1)
  have hcqb : chartAt E q.1 b = z'.1 := by
    rw [← hbb]; exact (chartAt E q.1).right_inv ((fr q.1).D_sub hz'1)
  have hbD : chartAt E q.1 b ∈ (fr q.1).D := hcqb ▸ hz'1
  have hbU : b ∈ (fr p.1).U := (fr p.1).D_mem _ hz1
  have hglue : b2_flatTriv L F (fr p.1).U (fr p.1).hU (fr p.1).pt (⟨b, hbU⟩,
      (b2_coord _).symm ((fr p.1).J z.2)) = (fr q.1).Ψ (chartAt E q.1 b, z'.2) := by
    rw [← (fr p.1).Ψ_eq _ hz1, hcqb]
    have : (z'.1, z'.2) = z' := rfl
    rw [this]
    exact ((b2f_lhAt hhol fr q).right_inv hzt).symm
  obtain ⟨A, lh, hw', hev⟩ := (fr q.1).glue (fr p.1).U (fr p.1).hU (fr p.1).hUo (fr p.1).pt b hbU
    hbq hbD _ z'.2 hglue
  let lin : (Fin g → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ (L.cFiber q.1)) → ℂ) :=
    A ∘ₗ (b2_coord (L.cFiber p.1)).symm.toLinearMap ∘ₗ ((fr p.1).J : (Fin g → ℂ) →ₗ[ℂ] _)
  let τ : E × (Fin g → ℂ) → E × (Fin g → ℂ) := fun x ↦
    (chartAt E q.1 ((chartAt E p.1).symm x.1),
      (fr q.1).Q (chartAt E q.1 ((chartAt E p.1).symm x.1)) (lin x.2 + lh))
  have hτz : τ z = z' := Prod.ext hcqb hw'.symm
  have h1 : ContDiffAt ℂ ω (fun x ↦ chartAt E q.1 ((chartAt E p.1).symm x)) z.1 :=
    b2f_chart_trans_contDiffAt p.1 q.1 z.1 ((fr p.1).D_sub hz1) hbq
  have hQ' : ContDiffAt ℂ ω (fr q.1).Q (chartAt E q.1 b) :=
    (fr q.1).hQ.contDiffAt ((fr q.1).hDo.mem_nhds hbD)
  have h2 : ContDiffAt ℂ ω (fun x ↦ (fr q.1).Q (chartAt E q.1 ((chartAt E p.1).symm x))) z.1 :=
    hQ'.comp z.1 h1
  have hτ : ContDiffAt ℂ ω τ z := by
    refine (h1.comp z contDiffAt_fst).prodMk ((h2.comp z contDiffAt_fst).clm_apply ?_)
    exact ((LinearMap.toContinuousLinearMap lin).contDiff.contDiffAt.add
      contDiffAt_const).comp z contDiffAt_snd
  refine hτ.congr_of_eventuallyEq ?_
  have e1 : ∀ᶠ x in nhds z, x ∈ (b2f_lhAt hhol fr p).source :=
    (b2f_lhAt hhol fr p).open_source.mem_nhds hzs
  have e2 := ((((chartAt E p.1).continuousAt_symm ((fr p.1).D_sub hz1)).comp
    continuousAt_fst).eventually hev)
  have e3 : ∀ᶠ x in nhds z, τ x ∈ (b2f_lhAt hhol fr q).source :=
    hτ.continuousAt.preimage_mem_nhds ((b2f_lhAt hhol fr q).open_source.mem_nhds (hτz ▸ hz's))
  filter_upwards [e1, e2, e3] with x hx1 ⟨hb'U, hb'c, hb'D, hφ⟩ hx3
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  have hxD : x.1 ∈ (fr p.1).D := hx1.1
  have : b2f_lhAt hhol fr p x = b2f_lhAt hhol fr q (τ x) := by
    show (fr p.1).Ψ x = (fr q.1).Ψ (τ x)
    rw [(fr p.1).Ψ_eq _ hxD]
    exact hφ _
  rw [this, (b2f_lhAt hhol fr q).left_inv hx3]

theorem b2f_isManifold [IsManifold 𝓘(ℂ, E) ω B] :
    letI := b2f_cs hhol fr
    IsManifold 𝓘(ℂ, E × (Fin g → ℂ)) ω (b2_totalSpace L F) := by
  let := b2f_cs hhol fr
  apply isManifold_of_contDiffOn
  rintro e e' ⟨p, rfl⟩ ⟨q, rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
    Set.preimage_id, Set.inter_univ, Function.id_comp, Function.comp_id,
    OpenPartialHomeomorph.symm_symm]
  intro z hz
  exact (b2f_trans_contDiffAt hhol fr p q z hz).contDiffWithinAt

end Charts2

section Structure

/-- The inverse of a torus chart is the quotient map in linear coordinates. -/
theorem b2f_torusChart_symm_apply {Λ : Type*} [AddCommGroup Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) [DiscreteTopology (b2_latticeMap Λ F).range]
    (t : b2_torus Λ F) (u : Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) :
    (b2_torusChart Λ F t).symm u = QuotientAddGroup.mk ((b2_coordHomeomorph Λ F).symm u) := by
  have h := (Classical.choose_spec (b2_isLocalHomeomorph_mk Λ F t.out)).2
  simp only [b2_torusChart, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    Homeomorph.toOpenPartialHomeomorph_symm_apply]
  rw [← h]

namespace b2f_Frame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]
variable {L : b2_LatticeLocalSystem B} {F : ∀ b, Submodule ℂ (L.cFiber b)} {g : ℕ} {b₁ : B}
variable (fr : b2f_Frame E L F g b₁)

theorem Ψ_add (b : B) (hbc : b ∈ (chartAt E b₁).source) (hbD : chartAt E b₁ b ∈ fr.D)
    (u : L.cFiber b₁) (w : Fin g → ℂ) :
    fr.Ψ (chartAt E b₁ b, fr.Q (chartAt E b₁ b) (b2_coord _ u) + w) =
      ⟨b, QuotientAddGroup.mk (Submodule.Quotient.mk
        ((L.flatTransport fr.U fr.hU ⟨b, fr.mem_U b hbc hbD⟩ fr.pt).symm u)) +
        QuotientAddGroup.mk (Submodule.Quotient.mk
        ((L.flatTransport fr.U fr.hU ⟨b, fr.mem_U b hbc hbD⟩ fr.pt).symm
          ((b2_coord _).symm (fr.J w))))⟩ := by
  rw [fr.Ψ_chart b hbc hbD]
  show Sigma.mk b _ = Sigma.mk b _
  congr 1
  rw [map_add, map_add, map_add, Submodule.Quotient.mk_add, QuotientAddGroup.mk_add]
  congr 1
  refine (b2f_torus_mk_eq_iff _ _ _).2 ⟨0, ?_⟩
  rw [map_zero, add_zero]
  exact fr.JQ_sub_mem b hbc hbD u

end b2f_Frame

section Clauses
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]
variable {L : b2_LatticeLocalSystem B} {F : ∀ b, Submodule ℂ (L.cFiber b)} {g : ℕ}
variable (hhol : L.IsHolomorphicSubbundle E F) (fr : ∀ b, b2f_Frame E L F g b)

theorem b2f_proj_lhAt (p : b2_totalSpace L F) (z : E × (Fin g → ℂ))
    (hz : z ∈ (b2f_lhAt hhol fr p).source) :
    b2_proj L F (b2f_lhAt hhol fr p z) = (chartAt E p.1).symm z.1 := by
  show b2_proj L F ((fr p.1).Ψ z) = _
  rw [(fr p.1).Ψ_eq z hz.1]
  rfl

theorem b2f_chart_center (p : b2_totalSpace L F) :
    (b2f_lhAt hhol fr p).symm p = (chartAt E p.1 p.1, b2f_wpt fr p) := by
  have h := (b2f_lhAt hhol fr p).left_inv (b2f_center_mem hhol fr p)
  have h2 : b2f_lhAt hhol fr p (chartAt E p.1 p.1, b2f_wpt fr p) = p := b2f_wpt_spec fr p
  rw [h2] at h
  exact h

theorem b2f_proj_contMDiff [IsManifold 𝓘(ℂ, E) ω B] :
    letI := b2f_cs hhol fr
    ContMDiff 𝓘(ℂ, E × (Fin g → ℂ)) 𝓘(ℂ, E) ω (b2_proj L F) := by
  let := b2f_cs hhol fr
  have := b2f_isManifold hhol fr
  intro p
  have hsrc : p ∈ (b2f_lhAt hhol fr p).target := by
    have := (b2f_lhAt hhol fr p).map_source (b2f_center_mem hhol fr p)
    rwa [show b2f_lhAt hhol fr p (chartAt E p.1 p.1, b2f_wpt fr p) = p from b2f_wpt_spec fr p]
      at this
  have hev : b2_proj L F =ᶠ[nhds p]
      (fun y ↦ (chartAt E p.1).symm (((b2f_lhAt hhol fr p).symm y).1)) := by
    filter_upwards [(b2f_lhAt hhol fr p).open_target.mem_nhds hsrc] with y hy
    have := b2f_proj_lhAt hhol fr p _ ((b2f_lhAt hhol fr p).map_target hy)
    rwa [(b2f_lhAt hhol fr p).right_inv hy] at this
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hev
  have hc : ContMDiffAt 𝓘(ℂ, E × (Fin g → ℂ)) 𝓘(ℂ, E × (Fin g → ℂ)) ω
      (b2f_lhAt hhol fr p).symm p :=
    (contMDiffOn_chart (I := 𝓘(ℂ, E × (Fin g → ℂ))) (x := p)).contMDiffAt
      ((chartAt (E × (Fin g → ℂ)) p).open_source.mem_nhds (mem_chart_source _ p))
  have hfst : ContMDiffAt 𝓘(ℂ, E × (Fin g → ℂ)) 𝓘(ℂ, E) ω (fun z : E × (Fin g → ℂ) ↦ z.1)
      ((b2f_lhAt hhol fr p).symm p) := contDiff_fst.contMDiff.contMDiffAt
  have hcs : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (chartAt E p.1).symm
      ((b2f_lhAt hhol fr p).symm p).1 := by
    rw [b2f_chart_center]
    exact (contMDiffOn_chart_symm (I := 𝓘(ℂ, E)) (x := p.1)).contMDiffAt
      ((chartAt E p.1).open_target.mem_nhds (mem_chart_target E p.1))
  exact hcs.comp p (hfst.comp p hc)


theorem b2f_proj_mfderiv_surjective [IsManifold 𝓘(ℂ, E) ω B] :
    letI := b2f_cs hhol fr
    ∀ p, Function.Surjective (mfderiv 𝓘(ℂ, E × (Fin g → ℂ)) 𝓘(ℂ, E) (b2_proj L F) p) := by
  let := b2f_cs hhol fr
  have := b2f_isManifold hhol fr
  intro p
  have hmd : MDifferentiableAt 𝓘(ℂ, E × (Fin g → ℂ)) 𝓘(ℂ, E) (b2_proj L F) p :=
    (b2f_proj_contMDiff hhol fr p).mdifferentiableAt (by simp)
  rw [hmd.mfderiv]
  have hw : writtenInExtChartAt 𝓘(ℂ, E × (Fin g → ℂ)) 𝓘(ℂ, E) p (b2_proj L F) =ᶠ[nhds
      (extChartAt 𝓘(ℂ, E × (Fin g → ℂ)) p p)] Prod.fst := by
    have hc : extChartAt 𝓘(ℂ, E × (Fin g → ℂ)) p p = (chartAt E p.1 p.1, b2f_wpt fr p) := by
      rw [extChartAt_coe]
      exact b2f_chart_center hhol fr p
    rw [hc]
    filter_upwards [(b2f_lhAt hhol fr p).open_source.mem_nhds (b2f_center_mem hhol fr p)]
      with z hz
    simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm, Function.comp_apply,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id]
    change chartAt E p.1 (b2_proj L F (b2f_lhAt hhol fr p z)) = z.1
    rw [b2f_proj_lhAt hhol fr p z hz]
    exact (chartAt E p.1).right_inv ((fr p.1).D_sub hz.1)
  rw [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ, hw.fderiv_eq, fderiv_fst]
  intro v
  refine ⟨(tangentSpaceCastModel _ p).symm (v, 0), ?_⟩
  simp
  rfl

theorem b2f_fiberIncl_contMDiff [IsManifold 𝓘(ℂ, E) ω B] (b : B)
    [DiscreteTopology (b2_latticeMap (L.fiber b) (F b)).range]
    [IsManifold 𝓘(ℂ, Fin (Module.finrank ℂ ((L.cFiber b) ⧸ F b)) → ℂ) ω
      (b2_torus (L.fiber b) (F b))] :
    letI := b2f_cs hhol fr
    ContMDiff 𝓘(ℂ, Fin (Module.finrank ℂ ((L.cFiber b) ⧸ F b)) → ℂ) 𝓘(ℂ, E × (Fin g → ℂ)) ω
      (b2_fiberIncl L F b) := by
  let := b2f_cs hhol fr
  have := b2f_isManifold hhol fr
  intro t
  have hbc : b ∈ (chartAt E b).source := mem_chart_source E b
  have hbD : chartAt E b b ∈ (fr b).D := (fr b).memD
  let T := L.flatTransport (fr b).U (fr b).hU ⟨b, (fr b).mem_U b hbc hbD⟩ (fr b).pt
  let κ := b2_coord (L.cFiber b)
  have hle : F b ≤ LinearMap.ker (((fr b).Q (chartAt E b b) : _ →ₗ[ℂ] (Fin g → ℂ)) ∘ₗ
      κ.toLinearMap ∘ₗ T.toLinearMap) := by
    intro v hv
    rw [LinearMap.mem_ker]
    refine ((fr b).ker_chart b hbc hbD (T v)).2 ?_
    rw [LinearEquiv.symm_apply_apply]; exact hv
  let Qb := (F b).liftQ _ hle
  let τc := b2_torusChart (L.fiber b) (F b) t
  let coordH := b2_coordHomeomorph (L.fiber b) (F b)
  let w := b2f_wpt fr (b2_fiberIncl L F b t)
  let τ : (Fin (Module.finrank ℂ ((L.cFiber b) ⧸ F b)) → ℂ) → E × (Fin g → ℂ) := fun u ↦
    (chartAt E b b, Qb (coordH.symm u) - Qb (coordH.symm (τc t)) + w)
  have hwt : (fr b).Ψ (chartAt E b b, w) = ⟨b, t⟩ := b2f_wpt_spec fr (b2_fiberIncl L F b t)
  rw [(fr b).Ψ_chart b hbc hbD] at hwt
  have hwt' : QuotientAddGroup.mk (Submodule.Quotient.mk (T.symm (κ.symm ((fr b).J w)))) = t :=
    @sigma_mk_injective B (b2_fiberTorus L F) b _ _ hwt
  have key : ∀ u, b2f_lhAt hhol fr (b2_fiberIncl L F b t) (τ u) =
      ⟨b, QuotientAddGroup.mk (coordH.symm u)⟩ := by
    intro u
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (coordH.symm u)
    obtain ⟨v₀, hv₀⟩ := Submodule.Quotient.mk_surjective _ (coordH.symm (τc t))
    have hlin : Qb (coordH.symm u) - Qb (coordH.symm (τc t)) =
        (fr b).Q (chartAt E b b) (κ (T (v - v₀))) := by
      rw [← hv, ← hv₀, ← map_sub, ← Submodule.Quotient.mk_sub]
      rfl
    show (fr b).Ψ (chartAt E b b, _) = _
    rw [hlin, (fr b).Ψ_add b hbc hbD]
    show Sigma.mk b _ = Sigma.mk b _
    congr 1
    change _ + QuotientAddGroup.mk (Submodule.Quotient.mk (T.symm (κ.symm ((fr b).J w)))) = _
    rw [hwt', LinearEquiv.symm_apply_apply, ← hv]
    have ht : t = QuotientAddGroup.mk (Submodule.Quotient.mk v₀) := by
      rw [hv₀, ← b2f_torusChart_symm_apply]
      exact (τc.left_inv (b2_mem_torusChart_source _ _ t)).symm
    rw [ht, Submodule.Quotient.mk_sub, QuotientAddGroup.mk_sub, sub_add_cancel]
  have hev : b2_fiberIncl L F b =ᶠ[nhds t] (b2f_lhAt hhol fr (b2_fiberIncl L F b t)) ∘ τ ∘ τc := by
    filter_upwards [τc.open_source.mem_nhds (b2_mem_torusChart_source _ _ t)] with t' ht'
    simp only [Function.comp_apply]
    rw [key, ← b2f_torusChart_symm_apply (t := t), τc.left_inv ht']
    rfl
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hev
  have hτt : τ (τc t) = (chartAt E b b, w) := by
    simp only [τ, sub_self, zero_add]
  have h1 : ContMDiffAt 𝓘(ℂ, E × (Fin g → ℂ)) 𝓘(ℂ, E × (Fin g → ℂ)) ω
      (b2f_lhAt hhol fr (b2_fiberIncl L F b t)) (τ (τc t)) := by
    rw [hτt]
    have hmem : (chartAt E b b, w) ∈ (chartAt (E × (Fin g → ℂ)) (b2_fiberIncl L F b t)).target :=
      by
        have h := mem_chart_target (E × (Fin g → ℂ)) (b2_fiberIncl L F b t)
        rwa [show chartAt (E × (Fin g → ℂ)) (b2_fiberIncl L F b t) (b2_fiberIncl L F b t) =
          (chartAt E b b, w) from b2f_chart_center hhol fr _] at h
    exact (contMDiffOn_chart_symm (I := 𝓘(ℂ, E × (Fin g → ℂ)))).contMDiffAt
      ((chartAt (E × (Fin g → ℂ)) (b2_fiberIncl L F b t)).open_target.mem_nhds hmem)
  have h2 : ContMDiff 𝓘(ℂ, Fin (Module.finrank ℂ ((L.cFiber b) ⧸ F b)) → ℂ)
      𝓘(ℂ, E × (Fin g → ℂ)) ω τ := by
    refine ContDiff.contMDiff ?_
    refine contDiff_const.prodMk ?_
    refine ContDiff.add (ContDiff.sub ?_ contDiff_const) contDiff_const
    exact (LinearMap.toContinuousLinearMap
      (Qb ∘ₗ (b2_coord ((L.cFiber b) ⧸ F b)).symm.toLinearMap)).contDiff
  have h3 : ContMDiffAt 𝓘(ℂ, Fin (Module.finrank ℂ ((L.cFiber b) ⧸ F b)) → ℂ)
      𝓘(ℂ, Fin (Module.finrank ℂ ((L.cFiber b) ⧸ F b)) → ℂ) ω τc t :=
    (contMDiffOn_chart (I := 𝓘(ℂ, Fin (Module.finrank ℂ ((L.cFiber b) ⧸ F b)) → ℂ))
      (x := t)).contMDiffAt (τc.open_source.mem_nhds (b2_mem_torusChart_source _ _ t))
  exact h1.comp t ((h2 _).comp t h3)

theorem b2f_flatTriv_contMDiff [IsManifold 𝓘(ℂ, E) ω B] (U : TopologicalSpace.Opens B)
    (hU : IsSimplyConnected (U : Set B)) (b₀ : U) :
    letI := b2f_cs hhol fr
    ContMDiff (𝓘(ℂ, E).prod 𝓘(ℂ, Fin (Module.finrank ℂ (L.cFiber b₀)) → ℂ))
      𝓘(ℂ, E × (Fin g → ℂ)) ω
      (fun p : U × (Fin (Module.finrank ℂ (L.cFiber b₀)) → ℂ) ↦
        b2_flatTriv L F U hU b₀ (p.1, (b2_coord (L.cFiber b₀)).symm p.2)) := by
  let := b2f_cs hhol fr
  have := b2f_isManifold hhol fr
  rintro ⟨b, a⟩
  set P := b2_flatTriv L F U hU b₀ (b, (b2_coord (L.cFiber b₀)).symm a) with hP
  have hbc : (b : B) ∈ (chartAt E (b : B)).source := mem_chart_source E (b : B)
  have hbD : chartAt E (b : B) b ∈ (fr b).D := (fr b).memD
  have hspec : b2_flatTriv L F U hU b₀ (⟨b, b.2⟩, (b2_coord (L.cFiber b₀)).symm a) =
      (fr b).Ψ (chartAt E (b : B) b, b2f_wpt fr P) := (b2f_wpt_spec fr P).symm
  obtain ⟨A, lh, hw', hev⟩ := (fr b).glue U hU U.isOpen b₀ b b.2 hbc hbD _ _ hspec
  let lin : (Fin (Module.finrank ℂ (L.cFiber b₀)) → ℂ) →ₗ[ℂ]
      (Fin (Module.finrank ℂ (L.cFiber b)) → ℂ) :=
    A ∘ₗ (b2_coord (L.cFiber b₀)).symm.toLinearMap
  let τ : U × (Fin (Module.finrank ℂ (L.cFiber b₀)) → ℂ) → E × (Fin g → ℂ) := fun x ↦
    (chartAt E (b : B) x.1, (fr b).Q (chartAt E (b : B) x.1) (lin x.2 + lh))
  have hτ0 : τ (b, a) = (chartAt E (b : B) b, b2f_wpt fr P) := Prod.ext rfl hw'.symm
  have hev' : (fun p : U × (Fin (Module.finrank ℂ (L.cFiber b₀)) → ℂ) ↦
      b2_flatTriv L F U hU b₀ (p.1, (b2_coord (L.cFiber b₀)).symm p.2)) =ᶠ[nhds (b, a)]
      (b2f_lhAt hhol fr P) ∘ τ := by
    have := ((continuous_subtype_val.comp continuous_fst).continuousAt
      (x := ((b, a) : U × (Fin (Module.finrank ℂ (L.cFiber b₀)) → ℂ)))).eventually hev
    filter_upwards [this] with x ⟨_, _, _, hφ⟩
    exact hφ _
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hev'
  have h1 : ContMDiffAt 𝓘(ℂ, E × (Fin g → ℂ)) 𝓘(ℂ, E × (Fin g → ℂ)) ω
      (b2f_lhAt hhol fr P) (τ (b, a)) := by
    rw [hτ0]
    have hmem : (chartAt E (b : B) b, b2f_wpt fr P) ∈ (chartAt (E × (Fin g → ℂ)) P).target := by
      have h := mem_chart_target (E × (Fin g → ℂ)) P
      rwa [show chartAt (E × (Fin g → ℂ)) P P = (chartAt E (b : B) b, b2f_wpt fr P) from
        b2f_chart_center hhol fr _] at h
    exact (contMDiffOn_chart_symm (I := 𝓘(ℂ, E × (Fin g → ℂ)))).contMDiffAt
      ((chartAt (E × (Fin g → ℂ)) P).open_target.mem_nhds hmem)
  have hval : ContMDiffAt (𝓘(ℂ, E).prod 𝓘(ℂ, Fin (Module.finrank ℂ (L.cFiber b₀)) → ℂ))
      𝓘(ℂ, E) ω (fun x : U × (Fin (Module.finrank ℂ (L.cFiber b₀)) → ℂ) ↦ (x.1 : B)) (b, a) :=
    (contMDiff_subtype_val.comp contMDiff_fst).contMDiffAt
  have hc : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω (chartAt E (b : B)) (b : B) :=
    (contMDiffOn_chart (I := 𝓘(ℂ, E)) (x := (b : B))).contMDiffAt
      ((chartAt E (b : B)).open_source.mem_nhds hbc)
  have hcx := hc.comp (b, a) hval
  have hQ : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, (Fin (Module.finrank ℂ (L.cFiber b)) → ℂ) →L[ℂ]
      (Fin g → ℂ)) ω (fr b).Q (chartAt E (b : B) b) :=
    ((fr b).hQ.contDiffAt ((fr b).hDo.mem_nhds hbD)).contMDiffAt
  have hlin : ContMDiffAt (𝓘(ℂ, E).prod 𝓘(ℂ, Fin (Module.finrank ℂ (L.cFiber b₀)) → ℂ))
      𝓘(ℂ, Fin (Module.finrank ℂ (L.cFiber b)) → ℂ) ω
      (fun x : U × (Fin (Module.finrank ℂ (L.cFiber b₀)) → ℂ) ↦ lin x.2 + lh) (b, a) :=
    (((LinearMap.toContinuousLinearMap lin).contDiff.add contDiff_const).contMDiff.comp
      contMDiff_snd).contMDiffAt
  exact h1.comp (b, a) (hcx.prodMk_space ((hQ.comp (b, a) hcx).clm_apply hlin))

end Clauses

end Structure

end HodgeLean.Foundations.Program
