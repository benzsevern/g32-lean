import HodgeLean.Foundations.Program.SchoenCycleDivisorSymmetric

/-! # Equal differential divisors and constant ratios
Local orders of equal divisors control the actual meromorphic ratio.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Manifold Filter Topology
open TauCeti.Contour
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Equal differential divisors give order zero for the quotient of every local germ. -/
theorem s2e_equal_divisors_ratio_order
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (v w : b4c_MeroForm E C hE)
    (hgv : ∃ p, meromorphicOrderAt (HurwitzPrymRR_loc hE v p) 0 ≠ ⊤)
    (hgw : ∃ p, meromorphicOrderAt (HurwitzPrymRR_loc hE w p) 0 ≠ ⊤)
    (hd : b4c_divForm (hE := hE) v = b4c_divForm (hE := hE) w) (p : C) :
    meromorphicOrderAt
      (fun z => HurwitzPrymRR_loc hE v p z / HurwitzPrymRR_loc hE w p z) 0 = 0 := by
  have hv := RiemannRochAna_coe_divForm_apply hE v
    (b4c_meroForm_orderSupport_finite_aux hE v) p (b4c_meroForm_order_ne_top hE v hgv p)
  have hw := RiemannRochAna_coe_divForm_apply hE w
    (b4c_meroForm_orderSupport_finite_aux hE w) p (b4c_meroForm_order_ne_top hE w hgw p)
  change meromorphicOrderAt (HurwitzPrymRR_loc hE v p / HurwitzPrymRR_loc hE w p) 0 = 0
  rw [meromorphicOrderAt_div (v.property.2 p) (w.property.2 p), ← hv, ← hw, hd]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Equal differential divisors have a constant actual meromorphic ratio. -/
theorem s2e_equal_divisors_ratio_constant
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (v w : b4c_MeroForm E C hE)
    (hv : (v : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0)
    (hw : (w : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0)
    (hgv : ∃ p, meromorphicOrderAt (HurwitzPrymRR_loc hE v p) 0 ≠ ⊤)
    (hgw : ∃ p, meromorphicOrderAt (HurwitzPrymRR_loc hE w p) 0 ≠ ⊤)
    (hd : b4c_divForm (hE := hE) v = b4c_divForm (hE := hE) w) :
    ∀ p q, b4c_formRatio (hE := hE) v w p = b4c_formRatio (hE := hE) v w q := by
  let F : b4c_MeroFun E C := ⟨b4c_formRatio (hE := hE) v w,
    b4c_formRatio_isMeroFun_aux hE v w hv hw hgv hgw⟩
  have hfinite (p : C) : F p ≠ OnePoint.infty := by
    change b4c_formRatio (hE := hE) v w p ≠ OnePoint.infty
    simp [b4c_formRatio, s2e_equal_divisors_ratio_order hE v w hgv hgw hd p]
  intro p q
  by_contra hpq
  obtain ⟨x, hx⟩ := b4cov_surjective (by simp : Module.finrank ℂ ℂ = 1)
    F F.property.1 ⟨p, q, hpq⟩ OnePoint.infty
  exact hfinite x hx

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The constant ratio of two nonzero differential germs with equal divisors is nonzero. -/
theorem s2e_equal_divisors_ratio_nonzero_constant
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (v w : b4c_MeroForm E C hE)
    (hv : (v : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0)
    (hw : (w : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0)
    (hgv : ∃ p, meromorphicOrderAt (HurwitzPrymRR_loc hE v p) 0 ≠ ⊤)
    (hgw : ∃ p, meromorphicOrderAt (HurwitzPrymRR_loc hE w p) 0 ≠ ⊤)
    (hd : b4c_divForm (hE := hE) v = b4c_divForm (hE := hE) w) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ p, b4c_formRatio (hE := hE) v w p = (c : OnePoint ℂ) := by
  let p : C := Classical.choice inferInstance
  let q : ℂ → ℂ := fun z => HurwitzPrymRR_loc hE v p z / HurwitzPrymRR_loc hE w p z
  have hq : MeromorphicAt q 0 := (v.property.2 p).div (w.property.2 p)
  have ho : meromorphicOrderAt q 0 = 0 := s2e_equal_divisors_ratio_order hE v w hgv hgw hd p
  refine ⟨meromorphicTrailingCoeffAt q 0,
    hq.meromorphicTrailingCoeffAt_ne_zero (by rw [ho]; simp), ?_⟩
  intro x
  rw [s2e_equal_divisors_ratio_constant hE v w hv hw hgv hgw hd x p]
  change (if meromorphicOrderAt q 0 < 0 then OnePoint.infty
    else if meromorphicOrderAt q 0 = 0 then ((meromorphicTrailingCoeffAt q 0 : ℂ) : OnePoint ℂ)
    else (0 : ℂ)) = _
  simp only [ho, lt_self_iff_false, ite_false, ite_true]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A constant meromorphic ratio identifies the punctured local differential germs. -/
theorem s2e_constant_formRatio_germ
    [ConnectedSpace C] (hE : Module.finrank ℂ E = 1) (v w : b4c_MeroForm E C hE)
    (hgv : ∃ p, meromorphicOrderAt (HurwitzPrymRR_loc hE v p) 0 ≠ ⊤)
    (hgw : ∃ p, meromorphicOrderAt (HurwitzPrymRR_loc hE w p) 0 ≠ ⊤)
    (c : ℂ) (hratio : ∀ p, b4c_formRatio (hE := hE) v w p = (c : OnePoint ℂ))
    (p : C) :
    HurwitzPrymRR_loc hE v p =ᶠ[𝓝[≠] 0] (fun z => c * HurwitzPrymRR_loc hE w p z) := by
  have hp := b4c_inverse_centeredCoordinate_punctured hE p
    (b4c_formRatio_punctured_chart hE v w
      (b4c_meroForm_order_ne_top hE v hgv) (b4c_meroForm_order_ne_top hE w hgw) p)
  have hc := (b4c_centeredCoordinate_inverse_eventuallyEq hE p).filter_mono
    (nhdsWithin_le_nhds (s := {0}ᶜ))
  have hn := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (w.property.2 p)).mp
    (b4c_meroForm_order_ne_top hE w hgw p)
  filter_upwards [hp, hc, hn] with z hz hcz hnz
  let y := (extChartAt 𝓘(ℂ, E) p).symm
    (extChartAt 𝓘(ℂ, E) p p + b4cov_lineEquiv hE z)
  change b4c_formRatio (hE := hE) v w y =
    ((HurwitzPrymRR_loc hE v p (b4c_centeredCoordinate hE p y) /
      HurwitzPrymRR_loc hE w p (b4c_centeredCoordinate hE p y) : ℂ) : OnePoint ℂ) at hz
  change b4c_centeredCoordinate hE p y = z at hcz
  rw [hratio, hcz] at hz
  have hdiv : HurwitzPrymRR_loc hE v p z / HurwitzPrymRR_loc hE w p z = c :=
    OnePoint.coe_injective hz.symm
  exact (div_eq_iff hnz).mp hdiv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Zero punctured germs force every parameter of the paired differential family to vanish. -/
theorem s2e_pairedDifferential_germ_zero
    (hE : Module.finrank ℂ E = 1) {r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (θ : b3_HolForm E C) (a : Fin r → ℂ)
    (hzero : ∀ p, HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w (θ, a)) p
      =ᶠ[𝓝[≠] 0] (fun _ => (0 : ℂ))) : (θ, a) = 0 := by
  have ha : a = 0 := by
    funext j
    have hr := residue_congr_nhdsNE (hzero (x j))
    have hr0 : residue (fun _ : ℂ => (0 : ℂ)) 0 = 0 :=
      residue_eq_zero_of_analyticAt analyticAt_const
    rw [hr0] at hr
    change b4c_res (hE := hE) (s2e_pairedDifferentialLinear hE w (θ, a)) (x j) = 0 at hr
    rw [s2e_pairedDifferentialLinear_residue_coordinate hE w x 1 hres, mul_one] at hr
    exact hr
  subst a
  have hθ : θ = 0 := by
    apply RiemannRochEichler_holForm_germ_ext hE
    intro p
    change HurwitzPrymRR_loc hE θ p =ᶠ[𝓝[≠] 0] (fun _ => (0 : ℂ))
    have hp := hzero p
    rw [s2e_pairedDifferentialLinear_loc] at hp
    simpa only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] using hp
  exact Prod.ext hθ rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Equal divisors of nonzero paired family members give proportional parameters. -/
theorem s2e_equal_family_divisors_proportional
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (u v : b3_HolForm E C × (Fin r → ℂ)) (hu : u ≠ 0) (hv : v ≠ 0)
    (hd : b4c_divForm (hE := hE) (s2e_pairedDifferentialLinear hE w u) =
      b4c_divForm (hE := hE) (s2e_pairedDifferentialLinear hE w v)) :
    ∃ c : ℂ, c ≠ 0 ∧ u = c • v := by
  let F := s2e_pairedDifferentialLinear hE w
  let U : b4c_MeroForm E C hE := ⟨F u, s2e_pairedDifferentialLinear_isMeroForm hE w u.1 u.2⟩
  let V : b4c_MeroForm E C hE := ⟨F v, s2e_pairedDifferentialLinear_isMeroForm hE w v.1 v.2⟩
  have hU : (U : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0 := by
    intro hz
    apply hu
    apply s2e_pairedDifferentialLinear_injective hE w x hres
    simpa only [map_zero] using hz
  have hV : (V : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0 := by
    intro hz
    apply hv
    apply s2e_pairedDifferentialLinear_injective hE w x hres
    simpa only [map_zero] using hz
  have hgU := s2e_pairedDifferentialLinear_exists_finite_order hE w x hres u.1 u.2 hu
  have hgV := s2e_pairedDifferentialLinear_exists_finite_order hE w x hres v.1 v.2 hv
  obtain ⟨c, hc, hratio⟩ := s2e_equal_divisors_ratio_nonzero_constant hE U V hU hV hgU hgV hd
  refine ⟨c, hc, sub_eq_zero.mp ?_⟩
  apply s2e_pairedDifferential_germ_zero hE w x hres (u - c • v).1 (u - c • v).2
  intro p
  have hp := s2e_constant_formRatio_germ hE U V hgU hgV c hratio p
  change HurwitzPrymRR_loc hE (F (u - c • v)) p =ᶠ[𝓝[≠] 0] (fun _ => (0 : ℂ))
  have he : HurwitzPrymRR_loc hE (F (u - c • v)) p =
      (fun z => HurwitzPrymRR_loc hE (F u) p z - c * HurwitzPrymRR_loc hE (F v) p z) := by
    rw [map_sub, map_smul]
    rfl
  rw [he]
  filter_upwards [hp] with z hz
  exact sub_eq_zero.mpr hz

/-- The actual adjusted differential divisor distinguishes projective parameters. -/
theorem s2e_projectiveDifferentialDivisor_injective
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (y : Fin (2 * r) → C) :
    Function.Injective (s2e_projectiveDifferentialDivisor hE w y) := by
  intro z t h
  induction z using Projectivization.ind with
  | h u hu =>
    induction t using Projectivization.ind with
    | h v hv =>
      change b4c_divForm (hE := hE) (s2e_pairedDifferentialLinear hE w u) +
          s2e_markedPoleDivisor y =
        b4c_divForm (hE := hE) (s2e_pairedDifferentialLinear hE w v) +
          s2e_markedPoleDivisor y at h
      obtain ⟨c, _, hc⟩ := s2e_equal_family_divisors_proportional hE w x hres u v hu hv
        (add_right_cancel h)
      exact (Projectivization.mk_eq_mk_iff' ℂ u v hu hv).mpr ⟨c, hc.symm⟩

/-- The unordered zero tuple distinguishes every projective differential parameter. -/
theorem s2e_projectiveDifferentialSymmetricPower_injective
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {k r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (y : Fin (2 * r) → C) (hy : Function.Injective y)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ (HurwitzPrymRR_loc hE (w i) p) 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C) + 2 * r) :
    Function.Injective
      (s2e_projectiveDifferentialSymmetricPower hE w x hres y hy horder hout hgenus) := by
  classical
  intro z t h
  apply s2e_projectiveDifferentialDivisor_injective hE w x hres y
  have hd := congrArg (fun s : Sym C (2 * k) =>
    (s : Multiset C).toFinsupp.mapRange (fun m : ℕ => (m : ℤ)) rfl) h
  simpa only [s2e_projectiveDifferentialSymmetricPower_recover] using hd

end HodgeLean.Foundations.Program
