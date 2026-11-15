import HodgeLean.Foundations.AutomorphyLineBundleDefs
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Sheaves.Sheaf
import HodgeLean.Foundations.AppellHumbertSections

/-! Proofs of the frozen factor-of-automorphy line bundle spec. All twelve `_aux` theorems are
proved; three parallel provers wrote them (statements 1-3 and 6; 4, 5 and 7; 8-12). -/

noncomputable section

namespace HodgeLean.Foundations.AutomorphyLineBundle

open AppellHumbert

universe u

section General

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℂ V] (L : Submodule ℤ V)

theorem spec_presheaf_isSheaf_aux (a : L → V → ℂ) :
    TopCat.Presheaf.IsSheaf (presheaf L a) := by
  refine TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types _ fun ι U sf hsf ↦ ?_
  let f : ∀ i, proj L ⁻¹' (U i : Set (Torus L)) → ℂ := fun i ↦
    (show sectionsOn L a (U i : Set (Torus L)) from sf i).1
  have hf : ∀ i, f i ∈ sectionsOn L a (U i : Set (Torus L)) := fun i ↦ (show sectionsOn L a (U i : Set (Torus L)) from sf i).2
  have hcompat : ∀ i j (x : V) (hi : proj L x ∈ (U i : Set (Torus L)))
      (hj : proj L x ∈ (U j : Set (Torus L))), f i ⟨x, hi⟩ = f j ⟨x, hj⟩ := fun i j x hi hj ↦
    congrArg (fun t : sectionsOn L a ((U i ⊓ U j : TopologicalSpace.Opens _) : Set (Torus L)) ↦
      (t : proj L ⁻¹' ((U i ⊓ U j : TopologicalSpace.Opens _) : Set (Torus L)) → ℂ) ⟨x, ⟨hi, hj⟩⟩) (hsf i j)
  have hcov : ∀ x : proj L ⁻¹' ((iSup U : TopologicalSpace.Opens _) : Set (Torus L)),
      ∃ i, proj L x ∈ (U i : Set (Torus L)) := fun x ↦ TopologicalSpace.Opens.mem_iSup.mp x.2
  let s : proj L ⁻¹' ((iSup U : TopologicalSpace.Opens _) : Set (Torus L)) → ℂ := fun x ↦
    f (hcov x).choose ⟨x, (hcov x).choose_spec⟩
  have hs : ∀ i (x : proj L ⁻¹' ((iSup U : TopologicalSpace.Opens _) : Set (Torus L)))
      (hx : proj L x ∈ (U i : Set (Torus L))), s x = f i ⟨x, hx⟩ :=
    fun i x hx ↦ hcompat _ _ _ _ _
  have hmem : ∀ i (x : V), proj L x ∈ (U i : Set (Torus L)) →
      proj L x ∈ ((iSup U : TopologicalSpace.Opens _) : Set (Torus L)) := fun i x hx ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx⟩
  have hsec : s ∈ sectionsOn L a ((iSup U : TopologicalSpace.Opens _) : Set (Torus L)) := by
    classical
    refine ⟨⟨fun v ↦ if h : proj L v ∈ ((iSup U : TopologicalSpace.Opens _) : Set (Torus L)) then s ⟨v, h⟩ else 0,
      fun x hx ↦ ?_, fun x ↦ by
        beta_reduce
        split_ifs with h
        · rfl
        · exact absurd x.2 h⟩, fun l x ↦ ?_⟩
    · obtain ⟨i, hi⟩ := hcov ⟨x, hx⟩
      obtain ⟨⟨F, hF, hfF⟩, -⟩ := hf i
      have hO : IsOpen (proj L ⁻¹' (U i : Set (Torus L))) :=
        (U i).isOpen.preimage continuous_quot_mk
      have hnhds := hO.mem_nhds hi
      refine ((hF.differentiableAt hnhds).congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hnhds] with y hy
      split_ifs with h
      · rw [hs i ⟨y, h⟩ hy]; exact hfF ⟨y, hy⟩
      · exact absurd (hmem i y hy) h
    · obtain ⟨i, hi⟩ := hcov x
      have hi' : proj L (shift L l x : V) ∈ (U i : Set (Torus L)) := by
        change proj L ((x : V) + l) ∈ _; rw [proj_add]; exact hi
      rw [hs i _ hi', hs i x hi]
      exact (hf i).2 l ⟨x, hi⟩
  refine ⟨⟨s, hsec⟩, fun i ↦ Subtype.ext (funext fun x ↦ hs i ⟨x, hmem i x x.2⟩ x.2), fun t ht ↦
    Subtype.ext (funext fun x ↦ ?_)⟩
  obtain ⟨i, hi⟩ := hcov x
  refine (congrArg (fun t : sectionsOn L a (U i : Set (Torus L)) ↦
    (t : proj L ⁻¹' (U i : Set (Torus L)) → ℂ) ⟨x, hi⟩) (ht i)).trans ?_
  exact (hs i x hi).symm

theorem spec_sectionsOn_mul_aux (a b : L → V → ℂ) (U : Set (Torus L))
    (f g : proj L ⁻¹' U → ℂ) (hf : f ∈ sectionsOn L a U) (hg : g ∈ sectionsOn L b U) :
    f * g ∈ sectionsOn L (a * b) U := by
  obtain ⟨⟨F, hF, hfF⟩, hfe⟩ := hf
  obtain ⟨⟨G, hG, hgG⟩, hge⟩ := hg
  refine ⟨⟨F * G, hF.mul hG, fun x ↦ by simp [hfF x, hgG x]⟩, fun l x ↦ ?_⟩
  simp only [Pi.mul_apply, hfe l x, hge l x]
  ring

theorem spec_mulEquiv_of_ne_zero_aux (a b : L → V → ℂ) (U : Set (Torus L))
    (s : proj L ⁻¹' U → ℂ) (hs : s ∈ sectionsOn L a U) (hs₀ : ∀ x, s x ≠ 0) :
    ∃ e : sectionsOn L b U ≃ₗ[ℂ] sectionsOn L (a * b) U,
      ∀ g x, (e g : proj L ⁻¹' U → ℂ) x = s x * (g : proj L ⁻¹' U → ℂ) x := by
  have hinv : ∀ h : sectionsOn L (a * b) U, (h : proj L ⁻¹' U → ℂ) / s ∈ sectionsOn L b U := by
    rintro ⟨h, ⟨H, hH, hhH⟩, hhe⟩
    obtain ⟨⟨S, hS, hsS⟩, hse⟩ := hs
    refine ⟨⟨fun v ↦ H v * (S v)⁻¹, hH.mul (hS.inv fun x hx ↦ ?_), fun x ↦ ?_⟩, fun l x ↦ ?_⟩
    · rw [← hsS ⟨x, hx⟩]; exact hs₀ _
    · simp [hhH x, hsS x, div_eq_mul_inv]
    · have hal : a l x ≠ 0 := by
        intro h0; apply hs₀ (shift L l x); rw [hse l x, h0, zero_mul]
      have := hs₀ x
      simp only [Pi.div_apply, Pi.mul_apply] at hhe ⊢
      rw [hhe l x, hse l x]
      field_simp
  refine ⟨
    { toFun := fun g ↦ ⟨s * g, spec_sectionsOn_mul_aux L a b U s g hs g.2⟩
      map_add' := fun g g' ↦ by ext x; simp [mul_add]
      map_smul' := fun c g ↦ by ext x; simp; ring
      invFun := fun h ↦ ⟨h / s, hinv h⟩
      left_inv := fun g ↦ by ext x; have := hs₀ x; simp; field_simp
      right_inv := fun h ↦ by ext x; have := hs₀ x; simp; field_simp }, fun g x ↦ rfl⟩

theorem spec_exists_disjoint_nhds_aux [DiscreteTopology L] (v : V) :
    ∃ W : Set V, IsOpen W ∧ v ∈ W ∧
      ∀ l : L, ((· + (l : V)) '' W ∩ W).Nonempty → l = 0 := by
  have hd : IsDiscrete (L : Set V) := isDiscrete_iff_discreteTopology.mpr ‹_›
  obtain ⟨ε, hε, hball⟩ := Metric.exists_ball_inter_eq_singleton_of_mem_discrete hd L.zero_mem
  refine ⟨Metric.ball v (ε / 2), Metric.isOpen_ball, Metric.mem_ball_self (by positivity), ?_⟩
  rintro l ⟨_, ⟨w, hw, rfl⟩, hwl⟩
  have hl : (l : V) ∈ Metric.ball (0 : V) ε ∩ L := by
    refine ⟨?_, l.2⟩
    rw [Metric.mem_ball, dist_zero_right]
    rw [Metric.mem_ball] at hw hwl
    calc ‖(l : V)‖ = dist (w + l) w := by rw [dist_eq_norm, add_sub_cancel_left]
      _ ≤ dist (w + l) v + dist w v := dist_triangle_right _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hwl hw
      _ = ε := add_halves ε
  rw [hball] at hl
  exact Subtype.ext hl

omit [NormedSpace ℂ V] in
private theorem exists_translate_decomp {W : Set V} {x : V} (hx : x ∈ proj L ⁻¹' (proj L '' W)) :
    ∃ p : V × L, p.1 ∈ W ∧ p.1 + (p.2 : V) = x := by
  obtain ⟨w, hw, hwx⟩ := hx
  exact ⟨⟨w, ⟨-w + x, QuotientAddGroup.eq.1 hwx⟩⟩, hw, by simp⟩

omit [NormedSpace ℂ V] in
private theorem translate_decomp_unique {W : Set V}
    (hdisj : ∀ l : L, ((· + (l : V)) '' W ∩ W).Nonempty → l = 0) {w w' : V} (hw : w ∈ W)
    (hw' : w' ∈ W) {l l' : L} (h : w + l = w' + l') : l = l' ∧ w = w' := by
  have hsub : w + ((l - l' : L) : V) = w' := by
    rw [Submodule.coe_sub, ← add_sub_assoc, h, add_sub_cancel_right]
  have hl : l - l' = 0 := hdisj (l - l') ⟨w', ⟨w, hw, hsub⟩, hw'⟩
  have hl' : l = l' := sub_eq_zero.1 hl
  subst hl'
  exact ⟨rfl, add_right_cancel h⟩

open Classical in
/-- The extension of `G` from `W` to the translates of `W` by the factor `a`. -/
private def translateExt (a : L → V → ℂ) (W : Set V) (G : V → ℂ) (y : V) : ℂ :=
  if hy : y ∈ proj L ⁻¹' (proj L '' W) then
    a (exists_translate_decomp L hy).choose.2 (exists_translate_decomp L hy).choose.1 *
      G (exists_translate_decomp L hy).choose.1
  else 0

omit [NormedSpace ℂ V] in
private theorem translateExt_eq (a : L → V → ℂ) {W : Set V}
    (hdisj : ∀ l : L, ((· + (l : V)) '' W ∩ W).Nonempty → l = 0) (G : V → ℂ) {w : V}
    (hw : w ∈ W) (l : L) : translateExt L a W G (w + l) = a l w * G w := by
  have hy : w + (l : V) ∈ proj L ⁻¹' (proj L '' W) := by
    show proj L (w + l) ∈ proj L '' W
    rw [proj_add]; exact Set.mem_image_of_mem _ hw
  rw [translateExt, dite_eq_left_of_eq_true (eq_true hy)]
  obtain ⟨hp, hpe⟩ := (exists_translate_decomp L hy).choose_spec
  obtain ⟨h1, h2⟩ := translate_decomp_unique L hdisj hp hw hpe
  rw [h1, h2]

theorem spec_restrictEquiv_of_disjoint_aux (a : L → V → ℂ)
    (hcoc : ∀ (l m : L) (v : V), a (l + m) v = a l (v + m) * a m v)
    (ha₀ : ∀ v, a 0 v = 1)
    (hhol : ∀ l, Differentiable ℂ (a l)) (W : Set V) (hW : IsOpen W)
    (hdisj : ∀ l : L, ((· + (l : V)) '' W ∩ W).Nonempty → l = 0) :
    ∃ e : sectionsOn L a (proj L '' W) ≃ₗ[ℂ] holomorphicOn W,
      ∀ f (w : W), (e f : W → ℂ) w =
        (f : proj L ⁻¹' (proj L '' W) → ℂ) ⟨w, Set.mem_image_of_mem _ w.2⟩ := by
  set P := proj L ⁻¹' (proj L '' W) with hP
  have hWP : ∀ w ∈ W, w ∈ P := fun w hw ↦ Set.mem_image_of_mem _ hw
  let r : sectionsOn L a (proj L '' W) →ₗ[ℂ] holomorphicOn W :=
    { toFun := fun f ↦ ⟨fun w ↦ (f : P → ℂ) ⟨w, hWP w w.2⟩, by
        obtain ⟨⟨F, hF, hfF⟩, -⟩ := f.2
        exact ⟨F, hF.mono hWP, fun w ↦ hfF _⟩⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  refine ⟨LinearEquiv.ofBijective r ⟨?_, ?_⟩, fun f w ↦ rfl⟩
  · intro f₁ f₂ hr
    apply Subtype.ext
    funext x
    obtain ⟨⟨w, l⟩, hw, hwx⟩ := exists_translate_decomp L x.2
    have hx : x = shift L l ⟨w, hWP w hw⟩ := Subtype.ext hwx.symm
    have hrw := congrArg (fun g : holomorphicOn W ↦ (g : W → ℂ) ⟨w, hw⟩) hr
    simp only [r, LinearMap.coe_mk, AddHom.coe_mk] at hrw
    rw [hx, f₁.2.2, f₂.2.2]
    exact congrArg _ hrw
  · rintro ⟨g, G, hG, hgG⟩
    refine ⟨⟨fun x ↦ translateExt L a W G x, ⟨fun y ↦ translateExt L a W G y, ?_, fun _ ↦ rfl⟩,
      fun m x ↦ ?_⟩, ?_⟩
    · intro x hx
      obtain ⟨⟨w, l⟩, hw, hwx⟩ := exists_translate_decomp L hx
      dsimp only at hw hwx
      have hev : (fun y ↦ translateExt L a W G y) =ᶠ[nhds x]
          fun y ↦ a l (y - l) * G (y - l) := by
        have hopen : IsOpen ((fun y ↦ y - (l : V)) ⁻¹' W) :=
          hW.preimage (continuous_id.sub continuous_const)
        have hmem : x ∈ (fun y ↦ y - (l : V)) ⁻¹' W := by
          change x - (l : V) ∈ W; rw [← hwx, add_sub_cancel_right]; exact hw
        filter_upwards [hopen.mem_nhds hmem] with y hy
        have := translateExt_eq L a hdisj G hy l
        rwa [sub_add_cancel] at this
      have hxl : x - (l : V) = w := by rw [← hwx, add_sub_cancel_right]
      have hd : DifferentiableAt ℂ (fun y ↦ a l (y - l) * G (y - l)) x := by
        have hs : DifferentiableAt ℂ (fun y : V ↦ y - (l : V)) x :=
          differentiableAt_id.sub_const _
        refine DifferentiableAt.mul ?_ ?_
        · exact (hhol l).differentiableAt.comp x hs
        · refine DifferentiableAt.comp x ?_ hs
          rw [hxl]; exact hG.differentiableAt (hW.mem_nhds hw)
      exact (hd.congr_of_eventuallyEq hev).differentiableWithinAt
    · obtain ⟨⟨w, l⟩, hw, hwx⟩ := exists_translate_decomp L x.2
      dsimp only at hw hwx
      change translateExt L a W G ((x : V) + m) = a m x * translateExt L a W G x
      rw [← hwx, add_assoc, ← Submodule.coe_add, translateExt_eq L a hdisj G hw,
        translateExt_eq L a hdisj G hw, add_comm l m, hcoc]
      ring
    · apply Subtype.ext
      funext w
      change translateExt L a W G w = g w
      have := translateExt_eq L a hdisj G w.2 0
      rw [Submodule.coe_zero, add_zero, ha₀, one_mul] at this
      rw [this, hgG]

theorem spec_one_equiv_structureSheaf_aux (U : Set (Torus L)) :
    ∃ e : sectionsOn L 1 U ≃ₗ[ℂ] structureSheafOn L U,
      ∀ f (x : proj L ⁻¹' U), (e f : U → ℂ) ⟨proj L x, x.2⟩ = (f : proj L ⁻¹' U → ℂ) x := by
  -- the chosen preimage of a point of `U`
  let lift : U → proj L ⁻¹' U := fun u ↦ ⟨Quotient.out (u : Torus L), by
    change proj L _ ∈ U; rw [proj, QuotientAddGroup.out_eq']; exact u.2⟩
  have hlift : ∀ (f : sectionsOn L 1 U) (x : proj L ⁻¹' U),
      (f : proj L ⁻¹' U → ℂ) (lift ⟨proj L x, x.2⟩) = (f : proj L ⁻¹' U → ℂ) x := by
    intro f x
    obtain ⟨l, hl⟩ := QuotientAddGroup.mk_out_eq_add L.toAddSubgroup (x : V)
    have hx : lift ⟨proj L x, x.2⟩ = shift L ⟨l, l.2⟩ x := Subtype.ext hl
    rw [hx, f.2.2 ⟨l, l.2⟩ x, Pi.one_apply, Pi.one_apply, one_mul]
  have hdesc : ∀ f : sectionsOn L 1 U,
      pullback L U (fun u ↦ (f : proj L ⁻¹' U → ℂ) (lift u)) = f := by
    intro f; funext x; exact hlift f x
  refine ⟨
    { toFun := fun f ↦ ⟨fun u ↦ (f : proj L ⁻¹' U → ℂ) (lift u), 
        Submodule.mem_comap.mpr (by rw [hdesc f]; exact f.2.1)⟩
      map_add' := fun f g ↦ rfl
      map_smul' := fun c f ↦ rfl
      invFun := fun g ↦ ⟨pullback L U g, g.2, fun l x ↦ by
        simp only [pullback, LinearMap.funLeft_apply, Pi.one_apply, one_mul]
        exact congrArg _ (Subtype.ext (proj_add L x l))⟩
      left_inv := fun f ↦ Subtype.ext (hdesc f)
      right_inv := fun g ↦ by
        ext u
        simp only [pullback, LinearMap.funLeft_apply]
        exact congrArg _ (Subtype.ext (QuotientAddGroup.out_eq' _)) }, fun f x ↦ hlift f x⟩

theorem spec_coboundary_equiv_one_aux (a : L → V → ℂ) (h : V → ℂ) (hh : Differentiable ℂ h)
    (hh₀ : ∀ v, h v ≠ 0) (ha : ∀ (l : L) (v : V), a l v = h (v + l) / h v)
    (U : Set (Torus L)) :
    ∃ e : sectionsOn L 1 U ≃ₗ[ℂ] sectionsOn L a U,
      ∀ f (x : proj L ⁻¹' U), (e f : proj L ⁻¹' U → ℂ) x = h x * (f : proj L ⁻¹' U → ℂ) x := by
  refine ⟨
    { toFun := fun f ↦ ⟨fun x ↦ h x * (f : proj L ⁻¹' U → ℂ) x, ?_⟩
      map_add' := fun f g ↦ Subtype.ext (funext fun x ↦ by simp [mul_add])
      map_smul' := fun c f ↦ Subtype.ext (funext fun x ↦ by simp; ring)
      invFun := fun f ↦ ⟨fun x ↦ (f : proj L ⁻¹' U → ℂ) x / h x, ?_⟩
      left_inv := fun f ↦ Subtype.ext (funext fun x ↦ by simp [hh₀ x])
      right_inv := fun f ↦ Subtype.ext (funext fun x ↦ mul_div_cancel₀ _ (hh₀ x)) }, fun f x ↦ rfl⟩
  · obtain ⟨⟨F, hF, hfF⟩, heq⟩ := f.2
    refine ⟨⟨h * F, hh.differentiableOn.mul hF, fun x ↦ by simp [hfF x]⟩, fun l x ↦ ?_⟩
    have := heq l x
    simp only [Pi.one_apply, one_mul] at this
    change h ((x : V) + l) * (f : proj L ⁻¹' U → ℂ) (shift L l x) = _
    rw [this, ha l x]
    field_simp [hh₀ x]
  · obtain ⟨⟨F, hF, hfF⟩, heq⟩ := f.2
    refine ⟨⟨F * fun v ↦ (h v)⁻¹, hF.mul (hh.differentiableOn.inv fun x _ ↦ hh₀ x),
      fun x ↦ by simp [hfF x, div_eq_mul_inv]⟩, fun l x ↦ ?_⟩
    change (f : proj L ⁻¹' U → ℂ) (shift L l x) / h ((x : V) + l) = _
    simp only [heq l x, Pi.one_apply, one_mul, ha l x]
    field_simp [hh₀ x, hh₀ ((x : V) + l)]

theorem spec_section_eq_zero_of_cocycle_failure_aux (a : L → V → ℂ) (U : Set (Torus L))
    (f : proj L ⁻¹' U → ℂ) (hf : f ∈ sectionsOn L a U) (l m : L) (x : proj L ⁻¹' U)
    (hfail : a (l + m) x ≠ a l ((x : V) + m) * a m x) : f x = 0 := by
  have h1 := hf.2 (l + m) x
  have h2 := hf.2 l (shift L m x)
  have h3 := hf.2 m x
  have e : shift L l (shift L m x) = shift L (l + m) x := by
    apply Subtype.ext
    simp only [shift, Submodule.coe_add]
    abel
  rw [e, h1, h3] at h2
  have h4 : (a (l + m) x - a l ((x : V) + m) * a m x) * f x = 0 := by
    change (a (l + m) x - a l ((shift L m x : V)) * a m x) * f x = 0
    linear_combination h2
  exact (mul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hfail)

theorem spec_sectionsOn_eq_bot_of_cocycle_failure_aux (a : L → V → ℂ)
    (hhol : ∀ l, Differentiable ℂ (a l))
    (hfail : ∃ (l m : L) (v : V), a (l + m) v ≠ a l (v + m) * a m v)
    (U : Set (Torus L)) (hU : IsOpen U) : sectionsOn L a U = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  obtain ⟨l, m, v₀, hv₀⟩ := hfail
  have hS : IsOpen (proj L ⁻¹' U) := hU.preimage QuotientAddGroup.continuous_mk
  obtain ⟨F, hF, hfF⟩ := hf.1
  funext x
  by_contra hx
  have hFx : F x ≠ 0 := by rw [← hfF]; exact hx
  have hcont : ContinuousAt F x := (hF.differentiableAt (hS.mem_nhds x.2)).continuousAt
  have hev : ∀ᶠ y in nhds (x : V), y ∈ proj L ⁻¹' U ∧ F y ≠ 0 :=
    Filter.Eventually.and (hS.mem_nhds x.2) (hcont.eventually_ne hFx)
  let δ : V → ℂ := fun w ↦ a (l + m) w - a l (w + m) * a m w
  have hδ : ∀ᶠ y in nhds (x : V), δ y = 0 := hev.mono fun y ⟨hyS, hy⟩ ↦ by
    by_contra h
    apply hy
    rw [← hfF ⟨y, hyS⟩]
    exact spec_section_eq_zero_of_cocycle_failure_aux L a U f hf l m ⟨y, hyS⟩ (sub_ne_zero.mp h)
  let g : ℂ → ℂ := fun z ↦ δ ((x : V) + z • (v₀ - x))
  have hd : Differentiable ℂ δ :=
    (hhol _).sub (((hhol l).comp (differentiable_id.add_const _)).mul (hhol m))
  have hg : Differentiable ℂ g :=
    hd.comp ((differentiable_const _).add (differentiable_id.smul_const _))
  have hg0 : g =ᶠ[nhds (0 : ℂ)] 0 := by
    have hc : Continuous (fun z : ℂ ↦ (x : V) + z • (v₀ - x)) := by fun_prop
    have ht : Filter.Tendsto (fun z : ℂ ↦ (x : V) + z • (v₀ - x)) (nhds 0) (nhds (x : V)) := by
      simpa using hc.tendsto 0
    exact ht.eventually hδ
  have hzero := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (fun z _ ↦ hg.analyticAt z) isPreconnected_univ (Set.mem_univ 0) hg0 (Set.mem_univ 1)
  have e : (x : V) + (1 : ℂ) • (v₀ - x) = v₀ := by simp
  have : δ v₀ = 0 := by simpa [g, e] using hzero
  exact hv₀ (sub_eq_zero.mp this)

theorem spec_constTwo_sections_eq_bot_aux (U : Set (Torus L)) :
    sectionsOn L (fun _ _ ↦ 2) U = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  funext x
  exact spec_section_eq_zero_of_cocycle_failure_aux L _ U f hf 0 0 x (by norm_num)

end General

section AppellHumbert

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
theorem spec_appellHumbert_globalSections_aux (D : Datum (V := V)) :
    ∃ e : sectionsOn D.lattice (holFactor D) Set.univ ≃ₗ[ℂ] sections D,
      ∀ f (v : V), (e f : V → ℂ) v =
        (f : proj D.lattice ⁻¹' Set.univ → ℂ) ⟨v, Set.mem_univ _⟩ := by
  refine ⟨
    { toFun := fun f ↦ ⟨fun v ↦ (f : proj D.lattice ⁻¹' Set.univ → ℂ) ⟨v, Set.mem_univ _⟩, ?_⟩
      invFun := fun θ ↦ ⟨fun x ↦ (θ : V → ℂ) x, ?_⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }, fun _ _ ↦ rfl⟩
  · obtain ⟨⟨F, hF, hfF⟩, heq⟩ := f.2
    refine ⟨?_, fun l v ↦ heq l ⟨v, Set.mem_univ _⟩⟩
    have e : (fun v ↦ (f : proj D.lattice ⁻¹' Set.univ → ℂ) ⟨v, Set.mem_univ _⟩) = F :=
      funext fun v ↦ hfF ⟨v, Set.mem_univ _⟩
    rw [e, ← differentiableOn_univ]
    exact hF
  · exact ⟨⟨θ, θ.2.1.differentiableOn, fun _ ↦ rfl⟩, fun l x ↦ θ.2.2 l x⟩

theorem holFactor_differentiable (D : Datum (V := V)) (l : D.lattice) :
    Differentiable ℂ (holFactor D l) := by
  let f : V →ₗ[ℂ] ℂ :=
    { toFun := D.hermitian.toFun l
      map_add' := D.hermitian.add_right l
      map_smul' := fun c x ↦ D.hermitian.smul_right c l x }
  have hf : Differentiable ℂ (fun v ↦ D.hermitian.toFun l v) :=
    (LinearMap.toContinuousLinearMap f).differentiable
  exact ((hf.const_mul _).add_const _).cexp.const_mul _

theorem spec_appellHumbert_restrictEquiv_aux (D : Datum (V := V)) (W : Set V) (hW : IsOpen W)
    (hdisj : ∀ l : D.lattice, ((· + (l : V)) '' W ∩ W).Nonempty → l = 0) :
    ∃ e : sectionsOn D.lattice (holFactor D) (proj D.lattice '' W) ≃ₗ[ℂ] holomorphicOn W,
      ∀ f (w : W), (e f : W → ℂ) w =
        (f : proj D.lattice ⁻¹' (proj D.lattice '' W) → ℂ) ⟨w, Set.mem_image_of_mem _ w.2⟩ := by
  exact spec_restrictEquiv_of_disjoint_aux D.lattice (holFactor D) (spec_holFactor_cocycle D)
    (spec_holFactor_zero D) (holFactor_differentiable D) W hW hdisj

end AppellHumbert

end HodgeLean.Foundations.AutomorphyLineBundle
