import HodgeLean.Foundations.Program.RelativeFrameOperatorGeometry

set_option maxHeartbeats 400000

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

theorem rf4_chartForm_transition {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (e d : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (hd : d ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (p : X) (hpe : p ∈ e.source) (hpd : p ∈ d.source)
    (v : TangentSpace 𝓘(ℂ, ℂ) p) (a b : ℂ)
    (hab : a = b * deriv (d ∘ e.symm) (e p)) :
    a * (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e p v) =
      b * (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) d p v) := by
  have hi := (contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hpe)).mdifferentiableAt
    (by simp)
  have hd' : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) d (e.symm (e p)) := by
    rw [e.left_inv hpe]
    exact (contMDiffAt_of_mem_maximalAtlas hd hpd).mdifferentiableAt (by simp)
  have hc := mfderiv_comp (e p) hd' hi
  rw [e.left_inv hpe] at hc
  let t : ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e p v
  have hv := congrArg (fun L : ℂ →L[ℂ] ℂ ↦ L t) hc
  rw [mfderiv_eq_fderiv] at hv
  change fderiv ℂ (d ∘ e.symm) (e p) t =
    mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) d p
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e.symm (e p)
        t) at hv
  have hinv : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e.symm (e p) t = v :=
    rf4_chart_inverse_mfderiv e he p hpe v
  rw [fderiv_eq_deriv_mul, hinv] at hv
  rw [hab]
  change (b * deriv (d ∘ e.symm) (e p)) * t = b * _
  rw [mul_assoc, hv]

theorem rf4_outerForm_agree {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (α : rf2_bddForm D.P) (p : X) (i j : Fin D.P.n)
    (hi : S.h.symm p ∈ (D.P.chart i).source ∧ D.P.chart i (S.h.symm p) ∈ D.P.piece i)
    (hj : S.h.symm p ∈ (D.P.chart j).source ∧ D.P.chart j (S.h.symm p) ∈ D.P.piece j)
    (v : TangentSpace 𝓘(ℂ, ℂ) p) :
    rf4_extendBdd (α.val i) (D.P.chart i (S.h.symm p)) *
        (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
          (fun q : X ↦ D.P.chart i (S.h.symm q)) p v) =
      rf4_extendBdd (α.val j) (D.P.chart j (S.h.symm p)) *
        (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
          (fun q : X ↦ D.P.chart j (S.h.symm q)) p v) := by
  let e := S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart i
  let d := S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart j
  have he : p ∈ e.source := by
    change p ∈ Set.univ ∩ _
    exact ⟨Set.mem_univ _, hi.1⟩
  have hd : p ∈ d.source := by
    change p ∈ Set.univ ∩ _
    exact ⟨Set.mem_univ _, hj.1⟩
  have hα := α.property i j ⟨D.P.chart i (S.h.symm p), hi.2⟩
    ⟨D.P.chart j (S.h.symm p), hj.2⟩ (by
      rw [(D.P.chart i).left_inv hi.1, (D.P.chart j).left_inv hj.1])
  have hfun : d ∘ e.symm = (D.P.chart j) ∘ (D.P.chart i).symm := by
    funext z
    change D.P.chart j (S.h.symm (S.h ((D.P.chart i).symm z))) =
      D.P.chart j ((D.P.chart i).symm z)
    rw [S.h.symm_apply_apply]
  apply rf4_chartForm_transition e d (S.stationary i) (S.stationary j) p he hd v
  change rf4_extendBdd (α.val i) (D.P.chart i (S.h.symm p)) =
    rf4_extendBdd (α.val j) (D.P.chart j (S.h.symm p)) *
      deriv (d ∘ e.symm) (D.P.chart i (S.h.symm p))
  rw [hfun]
  simpa only [rf4_extendBdd, dite_eq_left hi.2, dite_eq_left hj.2] using hα

theorem rf4_glue_outer {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (k : rf4_Src D) (p : X) (i : Fin D.P.n)
    (hi : S.h.symm p ∈ (D.P.chart i).source ∧ D.P.chart i (S.h.symm p) ∈ D.P.piece i)
    (v : TangentSpace 𝓘(ℂ, ℂ) p) :
    rf4_glue S k ⟨p, v⟩ = rf4_extendBdd (k.1.val i) (D.P.chart i (S.h.symm p)) *
      (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (fun q : X ↦ D.P.chart i (S.h.symm q)) p v) := by
  have hO : ∃ j, S.h.symm p ∈ (D.P.chart j).source ∧
      D.P.chart j (S.h.symm p) ∈ D.P.piece j := ⟨i, hi⟩
  rw [rf4_glue, dite_eq_left hO]
  exact rf4_outerForm_agree S k.1 p (Classical.choose hO) i (Classical.choose_spec hO) hi v

theorem rf4_glue_contMDiffAt_outer {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (k : rf4_Src D) (q : TangentBundle 𝓘(ℂ, ℂ) X)
    (i : Fin D.P.n)
    (hi : S.h.symm q.1 ∈ (D.P.chart i).source ∧
      D.P.chart i (S.h.symm q.1) ∈ D.P.piece i) :
    ContMDiffAt (𝓘(ℂ, ℂ)).tangent 𝓘(ℂ, ℂ) ω (rf4_glue S k) q := by
  let e := S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart i
  have hsrc : q.1 ∈ e.source := by
    change q.1 ∈ Set.univ ∩ _
    exact ⟨Set.mem_univ _, hi.1⟩
  have hf : DifferentiableOn ℂ (rf4_extendBdd (k.1.val i)) (D.P.piece i) :=
    (b63r_mem_bddHol_iff (D.P.isOpen i) _).mp (k.1.val i).property
  have hlocal := rf4_chartForm_contMDiffAt e (S.stationary i) (D.P.piece i) (D.P.isOpen i)
    (rf4_extendBdd (k.1.val i)) hf q hsrc hi.2
  have hN : ∀ᶠ p in 𝓝 q.1, S.h.symm p ∈ (D.P.chart i).source ∧
      D.P.chart i (S.h.symm p) ∈ D.P.piece i := by
    have hNP : ∀ᶠ p in 𝓝 q.1, e p ∈ D.P.piece i :=
      (e.continuousAt hsrc).tendsto.eventually ((D.P.isOpen i).mem_nhds hi.2)
    filter_upwards [e.open_source.mem_nhds hsrc, hNP] with p hp hp'
    exact ⟨hp.2, hp'⟩
  have hproj0 : ContMDiff (𝓘(ℂ, ℂ)).tangent 𝓘(ℂ, ℂ) ω
      (fun p : TangentBundle 𝓘(ℂ, ℂ) X ↦ p.1) :=
    Bundle.contMDiff_proj (TangentSpace 𝓘(ℂ, ℂ))
  have hproj : ContinuousAt (fun p : TangentBundle 𝓘(ℂ, ℂ) X ↦ p.1) q :=
    hproj0.continuous.continuousAt
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [hproj.tendsto.eventually hN] with p hp
  exact rf4_glue_outer S k p.1 i hp p.2

theorem rf4_sectorCoeff_differentiableOn (n : ℕ) (r : ℝ) (c ε : ℂ)
    (g : Fin n → b63r_bddHol (Metric.ball c (2 * r))) :
    DifferentiableOn ℂ (rf4_sectorCoeff n (fun j ↦ rf4_extendBdd (g j)) (c + ε))
      (rf4_innerDisc n r ε) := by
  have harg : DifferentiableOn ℂ (fun w : ℂ ↦ c + ε + w ^ n) (rf4_innerDisc n r ε) :=
    ((differentiable_const (c + ε)).add (differentiable_pow n)).differentiableOn
  have hmaps : MapsTo (fun w : ℂ ↦ c + ε + w ^ n) (rf4_innerDisc n r ε)
      (Metric.ball c (2 * r)) := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm]
    rw [show c + ε + w ^ n - c = w ^ n + ε by ring]
    exact hw
  have hsum : DifferentiableOn ℂ (fun w : ℂ ↦ ∑ j : Fin n,
      w ^ (j : ℕ) * rf4_extendBdd (g j) (c + ε + w ^ n)) (rf4_innerDisc n r ε) := by
    apply DifferentiableOn.fun_sum
    intro j _
    have hg : DifferentiableOn ℂ (rf4_extendBdd (g j)) (Metric.ball c (2 * r)) :=
      (b63r_mem_bddHol_iff Metric.isOpen_ball _).mp (g j).property
    exact (differentiable_pow (j : ℕ)).differentiableOn.mul (hg.comp harg hmaps)
  exact hsum.const_mul (n : ℂ)

theorem rf4_kernel_annulus_coeff {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (k : (rf4_delta D ε).ker) (x : Fin D.m)
    (u : b63r_annulus (D.deg x) D.r) :
    rf4_extendBdd (k.val.1.val (D.ann x)) u =
      rf4_sectorCoeff (D.deg x) (fun j ↦ rf4_extendBdd (k.val.2 x j)) (D.c x + ε x)
        (rf4_rootMap (D.deg x) (ε x) u) * deriv (rf4_rootMap (D.deg x) (ε x)) u := by
  have hk : rf4_delta D ε k.val = 0 := k.property
  have hv := congrArg (fun t : rf4_Tgt D ↦ (t x : b63r_annulus (D.deg x) D.r →ᵇ ℂ) u) hk
  change (k.val.1.val (D.ann x) : D.P.piece (D.ann x) →ᵇ ℂ)
    ⟨u, (D.hann x).ge u.property⟩ -
    ((rf4_sectorOp (D.deg x) (D.hdeg x) D.r D.hr (D.c x) (ε x) (k.val.2 x) :
      b63r_bddHol (b63r_annulus (D.deg x) D.r)) :
        b63r_annulus (D.deg x) D.r →ᵇ ℂ) u = 0 at hv
  rw [rf4_extendBdd, dite_eq_left ((D.hann x).ge u.property)]
  exact (sub_eq_zero.mp hv).trans (rf4_sectorOp_pullback (D.deg x) (D.hdeg x) D.r D.hr
    (D.c x) (ε x) (S.small x) (k.val.2 x) u).symm

theorem rf4_plumbing_transition_deriv {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (x : Fin D.m) (u : b63r_annulus (D.deg x) D.r) :
    deriv ((S.w x) ∘ (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)).symm) u =
      deriv (rf4_rootMap (D.deg x) (ε x)) u := by
  have hev : (S.w x) ∘ (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)).symm
      =ᶠ[𝓝 (u : ℂ)] rf4_rootMap (D.deg x) (ε x) := by
    filter_upwards [(rf4_annulus_isOpen (D.deg x) D.r).mem_nhds u.property] with z hz
    exact (S.glue x z hz).2
  exact hev.deriv_eq

theorem rf4_kernel_annulus_form {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (k : (rf4_delta D ε).ker) (x : Fin D.m)
    (u : b63r_annulus (D.deg x) D.r)
    (v : TangentSpace 𝓘(ℂ, ℂ) (S.h ((D.P.chart (D.ann x)).symm u))) :
    rf4_glue S k.val ⟨S.h ((D.P.chart (D.ann x)).symm u), v⟩ =
      rf4_sectorCoeff (D.deg x) (fun j ↦ rf4_extendBdd (k.val.2 x j)) (D.c x + ε x)
        (S.w x (S.h ((D.P.chart (D.ann x)).symm u))) *
      (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (S.w x)
        (S.h ((D.P.chart (D.ann x)).symm u)) v) := by
  let p := S.h ((D.P.chart (D.ann x)).symm u)
  let e := S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)
  have hpiece : (u : ℂ) ∈ D.P.piece (D.ann x) := (D.hann x).ge u.property
  have ht := D.P.contained (D.ann x) (subset_closure hpiece)
  have hp : S.h.symm p ∈ (D.P.chart (D.ann x)).source := by
    dsimp only [p]
    rw [S.h.symm_apply_apply]
    exact (D.P.chart (D.ann x)).map_target ht
  have heval : D.P.chart (D.ann x) (S.h.symm p) = (u : ℂ) := by
    dsimp only [p]
    rw [S.h.symm_apply_apply, (D.P.chart (D.ann x)).right_inv ht]
  have hi : S.h.symm p ∈ (D.P.chart (D.ann x)).source ∧
      D.P.chart (D.ann x) (S.h.symm p) ∈ D.P.piece (D.ann x) :=
    ⟨hp, heval.symm ▸ hpiece⟩
  have hsrc : p ∈ e.source := by
    change p ∈ Set.univ ∩ _
    exact ⟨Set.mem_univ _, hp⟩
  have hglue := S.glue x u u.property
  rw [rf4_glue_outer S k.val p (D.ann x) hi v]
  apply rf4_chartForm_transition e (S.w x) (S.stationary (D.ann x)) (S.w_mem x)
    p hsrc hglue.1 v
  change rf4_extendBdd (k.val.1.val (D.ann x)) (e p) =
    rf4_sectorCoeff (D.deg x) (fun j ↦ rf4_extendBdd (k.val.2 x j)) (D.c x + ε x)
      (S.w x p) * deriv ((S.w x) ∘ e.symm) (e p)
  rw [show e p = (u : ℂ) from heval, show S.w x p = rf4_rootMap (D.deg x) (ε x) u from hglue.2,
    rf4_plumbing_transition_deriv S x u]
  exact rf4_kernel_annulus_coeff S k x u

theorem rf4_glue_inner {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (k : (rf4_delta D ε).ker) (x : Fin D.m) (p : X)
    (hx : p ∈ (S.w x).source ∧ S.w x p ∈ rf4_innerDisc (D.deg x) D.r (ε x))
    (v : TangentSpace 𝓘(ℂ, ℂ) p) :
    rf4_glue S k.val ⟨p, v⟩ =
      rf4_sectorCoeff (D.deg x) (fun j ↦ rf4_extendBdd (k.val.2 x j)) (D.c x + ε x) (S.w x p) *
        (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (S.w x) p v) := by
  classical
  by_cases hO : ∃ i, S.h.symm p ∈ (D.P.chart i).source ∧
      D.P.chart i (S.h.symm p) ∈ D.P.piece i
  · obtain ⟨i, hi⟩ := hO
    have hOm : S.h.symm p ∈ O := by
      apply (Set.ext_iff.mp D.P.covers (S.h.symm p)).mpr
      apply Set.mem_iUnion.mpr
      exact ⟨i, D.P.chart i (S.h.symm p), hi.2, (D.P.chart i).left_inv hi.1⟩
    have hOuter : p ∈ S.h '' O := ⟨S.h.symm p, hOm, S.h.apply_symm_apply p⟩
    have hInner : p ∈ (S.w x).symm '' rf4_innerDisc (D.deg x) D.r (ε x) :=
      ⟨S.w x p, hx.2, (S.w x).left_inv hx.1⟩
    have hann := (Set.ext_iff.mp (S.overlap x) p).mp ⟨hOuter, hInner⟩
    obtain ⟨t, ⟨u, hu, hut⟩, htp⟩ := hann
    subst t
    subst p
    exact rf4_kernel_annulus_form S k x ⟨u, hu⟩ v
  · have hD : ∃ y, p ∈ (S.w y).source ∧
        S.w y p ∈ rf4_innerDisc (D.deg y) D.r (ε y) := ⟨x, hx⟩
    let y := Classical.choose hD
    have hy := Classical.choose_spec hD
    have hyx : y = x := by
      by_contra hne
      have hd := S.disjoint hne
      exact (Set.disjoint_left.mp hd)
        (show p ∈ (S.w y).symm '' rf4_innerDisc (D.deg y) D.r (ε y) from
          ⟨S.w y p, hy.2, (S.w y).left_inv hy.1⟩)
        (show p ∈ (S.w x).symm '' rf4_innerDisc (D.deg x) D.r (ε x) from
          ⟨S.w x p, hx.2, (S.w x).left_inv hx.1⟩)
    rw [rf4_glue, dite_eq_right hO, dite_eq_left hD]
    change rf4_sectorCoeff (D.deg y) (fun j ↦ rf4_extendBdd (k.val.2 y j))
      (D.c y + ε y) (S.w y p) *
        (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (S.w y) p v) = _
    rw [hyx]

theorem rf4_glue_contMDiffAt_inner {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (k : (rf4_delta D ε).ker) (q : TangentBundle 𝓘(ℂ, ℂ) X)
    (x : Fin D.m) (hx : q.1 ∈ (S.w x).source ∧
      S.w x q.1 ∈ rf4_innerDisc (D.deg x) D.r (ε x)) :
    ContMDiffAt (𝓘(ℂ, ℂ)).tangent 𝓘(ℂ, ℂ) ω (rf4_glue S k.val) q := by
  have hU : IsOpen (rf4_innerDisc (D.deg x) D.r (ε x)) :=
    isOpen_lt (((continuous_pow (D.deg x)).add continuous_const).norm) continuous_const
  have hf := rf4_sectorCoeff_differentiableOn (D.deg x) D.r (D.c x) (ε x) (k.val.2 x)
  have hlocal := rf4_chartForm_contMDiffAt (S.w x) (S.w_mem x)
    (rf4_innerDisc (D.deg x) D.r (ε x)) hU
    (rf4_sectorCoeff (D.deg x) (fun j ↦ rf4_extendBdd (k.val.2 x j)) (D.c x + ε x))
    hf q hx.1 hx.2
  have hN : ∀ᶠ p in 𝓝 q.1, p ∈ (S.w x).source ∧
      S.w x p ∈ rf4_innerDisc (D.deg x) D.r (ε x) := by
    have hNP : ∀ᶠ p in 𝓝 q.1, S.w x p ∈ rf4_innerDisc (D.deg x) D.r (ε x) :=
      ((S.w x).continuousAt hx.1).tendsto.eventually (hU.mem_nhds hx.2)
    filter_upwards [(S.w x).open_source.mem_nhds hx.1, hNP] with p hp hp'
    exact ⟨hp, hp'⟩
  have hproj0 : ContMDiff (𝓘(ℂ, ℂ)).tangent 𝓘(ℂ, ℂ) ω
      (fun p : TangentBundle 𝓘(ℂ, ℂ) X ↦ p.1) :=
    Bundle.contMDiff_proj (TangentSpace 𝓘(ℂ, ℂ))
  have hproj : ContinuousAt (fun p : TangentBundle 𝓘(ℂ, ℂ) X ↦ p.1) q :=
    hproj0.continuous.continuousAt
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [hproj.tendsto.eventually hN] with p hp
  exact rf4_glue_inner S k x p.1 hp p.2

theorem rf4_plumbing_cover_coordinates {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (p : X) :
    (∃ i, S.h.symm p ∈ (D.P.chart i).source ∧ D.P.chart i (S.h.symm p) ∈ D.P.piece i) ∨
      ∃ x, p ∈ (S.w x).source ∧ S.w x p ∈ rf4_innerDisc (D.deg x) D.r (ε x) := by
  rcases S.cover p with ho | ⟨x, hx⟩
  · left
    have ho' := (Set.ext_iff.mp D.P.covers (S.h.symm p)).mp ho
    obtain ⟨i, z, hz, heq⟩ := Set.mem_iUnion.mp ho'
    have ht := D.P.contained i (subset_closure hz)
    refine ⟨i, ?_, ?_⟩
    · rw [← heq]
      exact (D.P.chart i).map_target ht
    · rw [← heq, (D.P.chart i).right_inv ht]
      exact hz
  · right
    obtain ⟨z, hz, heq⟩ := hx
    have ht := S.w_target x (subset_closure hz)
    refine ⟨x, ?_, ?_⟩
    · rw [← heq]
      exact (S.w x).map_target ht
    · rw [← heq, (S.w x).right_inv ht]
      exact hz

theorem rf4_glue_contMDiff {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (k : (rf4_delta D ε).ker) :
    ContMDiff (𝓘(ℂ, ℂ)).tangent 𝓘(ℂ, ℂ) ω (rf4_glue S k.val) := by
  intro q
  rcases rf4_plumbing_cover_coordinates S q.1 with ⟨i, hi⟩ | ⟨x, hx⟩
  · exact rf4_glue_contMDiffAt_outer S k.val q i hi
  · exact rf4_glue_contMDiffAt_inner S k q x hx

theorem rf4_glue_fibre {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (k : rf4_Src D) (p : X) (a : ℂ)
    (v w : TangentSpace 𝓘(ℂ, ℂ) p) :
    rf4_glue S k ⟨p, a • v + w⟩ = a * rf4_glue S k ⟨p, v⟩ + rf4_glue S k ⟨p, w⟩ := by
  classical
  have hlin (A : ℂ →L[ℂ] ℂ) (c a u t : ℂ) :
      c * A (a * u + t) = a * (c * A u) + c * A t := by
    rw [map_add]
    have hs := A.map_smul a u
    change A (a * u) = a * A u at hs
    rw [hs]
    ring
  unfold rf4_glue
  split_ifs with hO hD
  · exact hlin (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (fun q : X ↦ D.P.chart (Classical.choose hO) (S.h.symm q)) p)
      (rf4_extendBdd (k.1.val (Classical.choose hO))
        (D.P.chart (Classical.choose hO) (S.h.symm p))) a (show ℂ from v) (show ℂ from w)
  · exact hlin (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (S.w (Classical.choose hD)) p)
      (rf4_sectorCoeff (D.deg (Classical.choose hD))
        (fun j ↦ rf4_extendBdd (k.2 (Classical.choose hD) j))
        (D.c (Classical.choose hD) + ε (Classical.choose hD)) (S.w (Classical.choose hD) p)) a (show ℂ from v) (show ℂ from w)
  · simp only [mul_zero, add_zero]

theorem rf4_glue_mem_holForm {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (k : (rf4_delta D ε).ker) :
    rf4_glue S k.val ∈ b3_HolForm ℂ X :=
  ⟨rf4_glue_contMDiff S k, rf4_glue_fibre S k.val⟩

theorem rf4_chart_mfderiv_inverse {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (e : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X) (z : ℂ) (hz : z ∈ e.target) (v : ℂ) :
    (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e (e.symm z)
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e.symm z v)) = v := by
  have hd := (contMDiffAt_of_mem_maximalAtlas he (e.map_target hz)).mdifferentiableAt (by simp)
  have hi := (contMDiffAt_symm_of_mem_maximalAtlas he hz).mdifferentiableAt (by simp)
  have hc := mfderiv_comp z hd hi
  have hev : e ∘ e.symm =ᶠ[𝓝 z] id := by
    filter_upwards [e.open_target.mem_nhds hz] with u hu
    exact e.right_inv hu
  rw [hev.mfderiv_eq, mfderiv_id] at hc
  have hv := congrArg (fun L : ℂ →L[ℂ] ℂ ↦ L v) hc
  change v = mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e (e.symm z)
    (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e.symm z v) at hv
  exact hv.symm

theorem rf4_glue_eq_zero {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (k : (rf4_delta D ε).ker) (hzero : rf4_glue S k.val = 0) :
    k = 0 := by
  have hα : k.val.1 = 0 := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    apply BoundedContinuousFunction.ext
    intro z
    change (k.val.1.val i : D.P.piece i →ᵇ ℂ) z = 0
    let e := S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart i
    have ht : (z : ℂ) ∈ e.target := by
      dsimp only [e]
      rw [rf4_stationaryChart_target]
      exact D.P.contained i (subset_closure z.property)
    let p := e.symm z
    let v : TangentSpace 𝓘(ℂ, ℂ) p := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e.symm z (1 : ℂ)
    have hp : p ∈ e.source := e.map_target ht
    have hcoord : e p = (z : ℂ) := e.right_inv ht
    have hi : S.h.symm p ∈ (D.P.chart i).source ∧
        D.P.chart i (S.h.symm p) ∈ D.P.piece i := ⟨hp.2, hcoord.symm ▸ z.property⟩
    have hz0 := congrFun hzero ⟨p, v⟩
    rw [rf4_glue_outer S k.val p i hi v] at hz0
    change rf4_extendBdd (k.val.1.val i) (e p) *
      (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e p v) = 0 at hz0
    have hunit : (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e p v) = 1 :=
      rf4_chart_mfderiv_inverse e (S.stationary i) z ht 1
    rw [hunit, mul_one, hcoord, rf4_extendBdd, dite_eq_left z.property] at hz0
    exact hz0
  have hg : k.val.2 = 0 := by
    funext x
    apply rf4_sector_injective_core (D.deg x) (D.hdeg x) D.r D.hr (D.c x) (ε x)
      (S.small x) (k.val.2 x)
    intro z hz
    have ht := S.w_target x (subset_closure hz)
    let p := (S.w x).symm z
    let v : TangentSpace 𝓘(ℂ, ℂ) p := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (S.w x).symm z (1 : ℂ)
    have hx : p ∈ (S.w x).source ∧ S.w x p ∈ rf4_innerDisc (D.deg x) D.r (ε x) :=
      ⟨(S.w x).map_target ht, ((S.w x).right_inv ht).symm ▸ hz⟩
    have hz0 := congrFun hzero ⟨p, v⟩
    rw [rf4_glue_inner S k x p hx v] at hz0
    have hunit : (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (S.w x) p v) = 1 :=
      rf4_chart_mfderiv_inverse (S.w x) (S.w_mem x) z ht 1
    rw [hunit, mul_one, (S.w x).right_inv ht] at hz0
    exact hz0
  apply Subtype.ext
  exact Prod.ext hα hg

theorem rf4_extendBdd_add {U : Set ℂ} (f g : b63r_bddHol U) (z : ℂ) :
    rf4_extendBdd (f + g) z = rf4_extendBdd f z + rf4_extendBdd g z := by
  classical
  by_cases hz : z ∈ U <;> simp [rf4_extendBdd, hz]

theorem rf4_extendBdd_smul {U : Set ℂ} (c : ℂ) (f : b63r_bddHol U) (z : ℂ) :
    rf4_extendBdd (c • f) z = c * rf4_extendBdd f z := by
  classical
  by_cases hz : z ∈ U <;> simp [rf4_extendBdd, hz, smul_eq_mul]

theorem rf4_sectorCoeff_smul {U : Set ℂ} (n : ℕ) (g : Fin n → b63r_bddHol U)
    (c τ w : ℂ) :
    rf4_sectorCoeff n (fun j ↦ rf4_extendBdd (c • g j)) τ w =
      c * rf4_sectorCoeff n (fun j ↦ rf4_extendBdd (g j)) τ w := by
  simp only [rf4_sectorCoeff, rf4_extendBdd_smul]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem rf4_sectorCoeff_add {U : Set ℂ} (n : ℕ) (f g : Fin n → b63r_bddHol U)
    (τ w : ℂ) :
    rf4_sectorCoeff n (fun j ↦ rf4_extendBdd (f j + g j)) τ w =
      rf4_sectorCoeff n (fun j ↦ rf4_extendBdd (f j)) τ w +
        rf4_sectorCoeff n (fun j ↦ rf4_extendBdd (g j)) τ w := by
  simp only [rf4_sectorCoeff, rf4_extendBdd_add, mul_add, Finset.sum_add_distrib]

def rf4_glueLinear {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) : rf4_Src D →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) X → ℂ) where
  toFun := rf4_glue S
  map_add' := by
    intro a b
    funext q
    change rf4_glue S (a + b) q = rf4_glue S a q + rf4_glue S b q
    unfold rf4_glue
    split_ifs with hO hD
    · let i := Classical.choose hO
      let z := D.P.chart i (S.h.symm q.1)
      let t : ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun p : X ↦ D.P.chart i (S.h.symm p)) q.1 q.2
      change rf4_extendBdd (a.1.val i + b.1.val i) z * t =
        rf4_extendBdd (a.1.val i) z * t + rf4_extendBdd (b.1.val i) z * t
      rw [rf4_extendBdd_add]
      exact add_mul _ _ _
    · let x := Classical.choose hD
      let w := S.w x q.1
      let τ := D.c x + ε x
      let t : ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (S.w x) q.1 q.2
      change rf4_sectorCoeff (D.deg x) (fun j ↦ rf4_extendBdd (a.2 x j + b.2 x j)) τ w * t =
        rf4_sectorCoeff (D.deg x) (fun j ↦ rf4_extendBdd (a.2 x j)) τ w * t +
          rf4_sectorCoeff (D.deg x) (fun j ↦ rf4_extendBdd (b.2 x j)) τ w * t
      rw [rf4_sectorCoeff_add]
      exact add_mul _ _ _
    · simp only [add_zero]
  map_smul' := by
    intro c a
    funext q
    change rf4_glue S (c • a) q = c * rf4_glue S a q
    unfold rf4_glue
    split_ifs with hO hD
    · let i := Classical.choose hO
      let z := D.P.chart i (S.h.symm q.1)
      let t : ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun p : X ↦ D.P.chart i (S.h.symm p)) q.1 q.2
      change rf4_extendBdd (c • a.1.val i) z * t = c * (rf4_extendBdd (a.1.val i) z * t)
      rw [rf4_extendBdd_smul]
      exact mul_assoc _ _ _
    · let x := Classical.choose hD
      let w := S.w x q.1
      let τ := D.c x + ε x
      let t : ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (S.w x) q.1 q.2
      change rf4_sectorCoeff (D.deg x) (fun j ↦ rf4_extendBdd (c • a.2 x j)) τ w * t =
        c * (rf4_sectorCoeff (D.deg x) (fun j ↦ rf4_extendBdd (a.2 x j)) τ w * t)
      rw [rf4_sectorCoeff_smul]
      exact mul_assoc _ _ _
    · simp only [mul_zero]

theorem rf4_kernel_equiv_core {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) :
    ∃ e : (rf4_delta D ε).ker ≃ₗ[ℂ] b3_HolForm ℂ X,
      ∀ k : (rf4_delta D ε).ker, (e k : TangentBundle 𝓘(ℂ, ℂ) X → ℂ) = rf4_glue S k.val := by
  let L : (rf4_delta D ε).ker →ₗ[ℂ] b3_HolForm ℂ X :=
    ((rf4_glueLinear S).comp (rf4_delta D ε).ker.subtype).codRestrict
      (b3_HolForm ℂ X) (fun k ↦ rf4_glue_mem_holForm S k)
  have hi : Function.Injective L := by
    intro k l hkl
    have hd : L (k - l) = 0 := by rw [map_sub, hkl, sub_self]
    have hz : rf4_glue S (k - l).val = 0 :=
      congrArg (fun θ : b3_HolForm ℂ X ↦ θ.val) hd
    exact sub_eq_zero.mp (rf4_glue_eq_zero S (k - l) hz)
  have hs : Function.Surjective L := by
    intro θ
    obtain ⟨k, hk⟩ := rf4_holForm_glue_preimage S θ
    refine ⟨k, ?_⟩
    apply Subtype.ext
    exact hk
  exact ⟨LinearEquiv.ofBijective L ⟨hi, hs⟩, fun _ ↦ rfl⟩

end HodgeLean.Foundations.Program
