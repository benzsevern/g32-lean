import HodgeLean.Foundations.BundleResolution.ChernDefs

/-! # Quotient maps for fibrewise projectivization

The nonzero-vector quotient carries the fixed projective topology.
HC no distance; AV milestone no distance. -/

noncomputable section
open Bundle TopologicalSpace Topology
namespace HodgeLean.Foundations.BundleResolution

variable {B : Type} [TopologicalSpace B] {k : ℕ} (E : I1ComplexBundle B k)
private local instance : TopologicalSpace (i1_projectiveBundle E) := i1_projectiveTopology E

theorem i1_projectiveQuotient_surjective :
    Function.Surjective (i1_projectiveQuotient E) := by
  rintro ⟨b, z⟩
  refine ⟨⟨⟨b, z.rep⟩, z.rep_nonzero⟩, ?_⟩
  exact congrArg (Sigma.mk b) z.mk_rep

theorem i1_projectiveQuotient_isQuotientMap :
    IsQuotientMap (i1_projectiveQuotient E) where
  surjective := i1_projectiveQuotient_surjective E
  eq_coinduced := rfl

theorem i1_projectiveProjection_continuous :
    Continuous (fun z : i1_projectiveBundle E => z.1) := by
  apply continuous_coinduced_dom.mpr
  exact (FiberBundle.continuous_proj (Fin k → ℂ) E.fibre).comp continuous_subtype_val

theorem i1_totalSpace_smul_continuous :
    Continuous (fun p : ℂ × TotalSpace (Fin k → ℂ) E.fibre =>
      (⟨p.2.proj, p.1 • p.2.2⟩ : TotalSpace (Fin k → ℂ) E.fibre)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let e := trivializationAt (Fin k → ℂ) E.fibre p.2.proj
  have hb : p.2.proj ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
  have hp : ContinuousAt (fun q : ℂ × TotalSpace (Fin k → ℂ) E.fibre =>
      q.2.proj) p :=
    (FiberBundle.continuous_proj (Fin k → ℂ) E.fibre).continuousAt.comp
      continuous_snd.continuousAt
  apply e.continuousAt_of_comp_left (f := fun q : ℂ × TotalSpace (Fin k → ℂ) E.fibre =>
    (⟨q.2.proj, q.1 • q.2.2⟩ : TotalSpace (Fin k → ℂ) E.fibre)) hp hb
  have he : ContinuousAt (fun q : ℂ × TotalSpace (Fin k → ℂ) E.fibre => e q.2) p :=
    (e.continuousAt (e.mem_source.mpr hb)).comp continuous_snd.continuousAt
  have hcoords := hp.prodMk (continuous_fst.continuousAt.smul he.snd)
  apply hcoords.congr_of_eventuallyEq
  filter_upwards [hp.eventually (e.open_baseSet.mem_nhds hb)] with q hq
  change e ⟨q.2.proj, q.1 • q.2.2⟩ = (q.2.proj, q.1 • (e q.2).2)
  rw [e.apply_eq_prod_continuousLinearEquivAt ℂ _ hq,
    e.apply_eq_prod_continuousLinearEquivAt ℂ _ hq, map_smul]


def i1_nonzeroScale (a : ℂˣ)
    (v : {v : TotalSpace (Fin k → ℂ) E.fibre // v.2 ≠ 0}) :
    {v : TotalSpace (Fin k → ℂ) E.fibre // v.2 ≠ 0} :=
  ⟨⟨v.1.proj, a • v.1.2⟩, by exact smul_ne_zero a.ne_zero v.2⟩

theorem i1_nonzeroScale_continuous (a : ℂˣ) : Continuous (i1_nonzeroScale E a) := by
  apply Continuous.subtype_mk
  exact (i1_totalSpace_smul_continuous E).comp
    (continuous_const.prodMk continuous_subtype_val)

theorem i1_projectiveQuotient_scale (a : ℂˣ)
    (v : {v : TotalSpace (Fin k → ℂ) E.fibre // v.2 ≠ 0}) :
    i1_projectiveQuotient E (i1_nonzeroScale E a v) = i1_projectiveQuotient E v := by
  apply congrArg (Sigma.mk v.1.proj)
  exact (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr ⟨a, rfl⟩

theorem i1_projectiveQuotient_saturation
    (s : Set {v : TotalSpace (Fin k → ℂ) E.fibre // v.2 ≠ 0}) :
    (i1_projectiveQuotient E) ⁻¹' (i1_projectiveQuotient E '' s) =
      ⋃ a : ℂˣ, (i1_nonzeroScale E a) ⁻¹' s := by
  ext v
  constructor
  · rintro ⟨⟨⟨b, w⟩, hw⟩, hws, heq⟩
    obtain rfl : b = v.1.proj := congrArg Sigma.fst heq
    have hp : Projectivization.mk ℂ w hw = Projectivization.mk ℂ v.1.2 v.2 :=
      (Sigma.mk.inj_iff.mp heq).2 |> eq_of_heq
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp hp
    apply Set.mem_iUnion.mpr
    refine ⟨a, ?_⟩
    change i1_nonzeroScale E a v ∈ s
    simpa only [i1_nonzeroScale, ha] using hws
  · intro hv
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hv
    exact ⟨i1_nonzeroScale E a v, ha, i1_projectiveQuotient_scale E a v⟩

theorem i1_projectiveQuotient_isOpenMap : IsOpenMap (i1_projectiveQuotient E) := by
  intro s hs
  apply (i1_projectiveQuotient_isQuotientMap E).isOpen_preimage.mp
  rw [i1_projectiveQuotient_saturation]
  exact isOpen_iUnion fun a => hs.preimage (i1_nonzeroScale_continuous E a)

end HodgeLean.Foundations.BundleResolution
