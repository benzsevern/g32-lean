import HodgeLean.Foundations.Program.TorusAlgebraizationB54Incidence
import HodgeLean.Foundations.Program.TorusAlgebraizationB54AnalyticCoordinates
import HodgeLean.Foundations.Program.RelativeTorusTopology

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))

variable {ι : Type} [Fintype ι]

def b54_coverIncidence (f : b5_V Λ F → ι → ℂ) :
    Set (b2_torus Λ F × (ι → ℂ)) :=
  Prod.map (b2_torusCover Λ F) id ''
    b54_vectorIncidence (f)

theorem b54_coverIncidence_preimage
    (f : b5_V Λ F → ι → ℂ)
    (hcover : ∀ z w, b2_torusCover Λ F z = b2_torusCover Λ F w →
      ∃ c : ℂ, c ≠ 0 ∧ f z = c • f w) :
    Prod.map (b2_torusCover Λ F) id ⁻¹' b54_coverIncidence Λ F f =
      b54_vectorIncidence (f) := by
  ext p
  constructor
  · rintro ⟨⟨z, v⟩, hz, he⟩
    have hv : v = p.2 := congrArg Prod.snd he
    subst v
    obtain ⟨c, hc, hcoord⟩ := hcover z p.1
      (congrArg Prod.fst he)
    intro i j
    have hh := hz i j
    change f z i * p.2 j -
      f z j * p.2 i = 0 at hh
    rw [hcoord] at hh
    simp only [Pi.smul_apply, smul_eq_mul] at hh
    apply (mul_eq_zero.mp ?_).resolve_left hc
    convert hh using 1 <;> ring
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem b54_coverIncidence_isClosed
    (f : b5_V Λ F → ι → ℂ)
    (hf : ∀ i, Differentiable ℂ (fun z => f z i))
    (hcover : ∀ z w, b2_torusCover Λ F z = b2_torusCover Λ F w →
      ∃ c : ℂ, c ≠ 0 ∧ f z = c • f w) :
    IsClosed (b54_coverIncidence Λ F f) := by
  have hq : IsOpenQuotientMap (b2_torusCover Λ F) :=
    (QuotientAddGroup.isOpenQuotientMap_mk (N := (b2_latticeMap Λ F).range)).comp
      (b2_coordHomeomorph Λ F).symm.isOpenQuotientMap
  apply (hq.prodMap (IsOpenQuotientMap.id (X := ι → ℂ))).isQuotientMap.isCoinducing.isClosed_preimage.mp
  rw [b54_coverIncidence_preimage Λ F f hcover]
  exact (b54_vectorIncidence_isClosedAnalytic _ hf).isClosed

section Analytic
variable [DiscreteTopology (b2_latticeMap Λ F).range]
local instance b54_coverIncidenceChartedSpace : ChartedSpace (b5_V Λ F × (ι → ℂ)) (b2_torus Λ F × (ι → ℂ)) :=
  prodChartedSpace (b5_V Λ F) (b2_torus Λ F) (ι → ℂ) (ι → ℂ)

theorem b54_coverIncidence_isClosedAnalytic
    (f : b5_V Λ F → ι → ℂ)
    (hf : ∀ i, Differentiable ℂ (fun z => f z i))
    (hcover : ∀ z w, b2_torusCover Λ F z = b2_torusCover Λ F w →
      ∃ c : ℂ, c ≠ 0 ∧ f z = c • f w) :
    IsClosedAnalytic (b5_V Λ F × (ι → ℂ)) (b54_coverIncidence Λ F f) := by
  have heq (x : b2_torus Λ F × (ι → ℂ)) (y : b5_V Λ F × (ι → ℂ)) :
      (chartAt (b5_V Λ F × (ι → ℂ)) x).symm y =
        Prod.map (b2_torusCover Λ F) id y := by
    apply Prod.ext
    · exact b2t_torusChart_symm_apply F x.1 y.1
    · rfl
  have hp : IsClosedAnalytic (b5_V Λ F × (ι → ℂ))
      (Prod.map (b2_torusCover Λ F) id ⁻¹' b54_coverIncidence Λ F f) := by
    rw [b54_coverIncidence_preimage Λ F f hcover]
    exact b54_vectorIncidence_isClosedAnalytic _ hf
  refine ⟨b54_coverIncidence_isClosed Λ F f hf hcover, ?_⟩
  intro x hx
  let e := chartAt (b5_V Λ F × (ι → ℂ)) x
  have hxe : x ∈ e.source := mem_chart_source _ x
  have hy : e x ∈ Prod.map (b2_torusCover Λ F) id ⁻¹'
      b54_coverIncidence Λ F f := by
    change Prod.map (b2_torusCover Λ F) id (e x) ∈ b54_coverIncidence Λ F f
    rw [← heq, e.left_inv hxe]
    exact hx
  obtain ⟨U, hU, hUy, _, n, f, hf, hzero⟩ := hp.2 (e x) hy
  refine ⟨U ∩ e.target, hU.inter e.open_target, ⟨hUy, e.map_source hxe⟩,
    Set.inter_subset_right, n, f, fun i => (hf i).mono Set.inter_subset_left, ?_⟩
  intro y hy
  rw [heq]
  exact hzero y hy.1

end Analytic

theorem b54_coverIncidence_scale
    (f : b5_V Λ F → ι → ℂ) (c : ℂ)
    (t : b2_torus Λ F) (v : ι → ℂ) (hv : (t, v) ∈ b54_coverIncidence Λ F f) :
    (t, c • v) ∈ b54_coverIncidence Λ F f := by
  obtain ⟨⟨z, w⟩, hw, he⟩ := hv
  have ht : b2_torusCover Λ F z = t := congrArg Prod.fst he
  have hv : w = v := congrArg Prod.snd he
  subst w
  refine ⟨(z, c • v), ?_, ?_⟩
  · intro i j
    have hh := hw i j
    change f z i * (c * v j) -
      f z j * (c * v i) = 0
    calc
      _ = c * (f z i * v j -
        f z j * v i) := by ring
      _ = 0 := by rw [hh, mul_zero]
  · exact Prod.ext ht rfl

theorem b54_cover_cone_algebraic (hF : b2_IsWeightOne Λ F) (n : ℕ)
    (f : b5_V Λ F → Fin n → ℂ)
    (hf : ∀ i, Differentiable ℂ (fun z => f z i))
    (hcover : ∀ z w, b2_torusCover Λ F z = b2_torusCover Λ F w →
      ∃ c : ℂ, c ≠ 0 ∧ f z = c • f w) :
    ∃ (m : ℕ) (d : Fin m → ℕ) (P : Fin m → MvPolynomial (Fin n) ℂ),
      (∀ i, (P i).IsHomogeneous (d i)) ∧
      Prod.snd '' b54_coverIncidence Λ F f =
        {v | ∀ i, MvPolynomial.eval v (P i) = 0} := by
  letI := b2_latticeMap_discrete F hF
  letI := b2_torus_t2Space F
  letI := b2_torus_compactSpace F hF
  letI := b2_torus_isManifold F
  have hq : IsOpenQuotientMap (b2_torusCover Λ F) :=
    (QuotientAddGroup.isOpenQuotientMap_mk (N := (b2_latticeMap Λ F).range)).comp
      (b2_coordHomeomorph Λ F).symm.isOpenQuotientMap
  letI := Topology.IsOpenQuotientMap.secondCountableTopology hq
  exact b54_incidence_cone_algebraic n (b54_coverIncidence Λ F f)
    (b54_coverIncidence_isClosedAnalytic Λ F f hf hcover)
    (b54_coverIncidence_scale Λ F f)

theorem b54_cover_cone_mem_iff
    (f : b5_V Λ F → ι → ℂ)
    (hbase : ∀ z, f z ≠ 0) (v : ι → ℂ) :
    v ∈ Prod.snd '' b54_coverIncidence Λ F f ↔
      ∃ (z : b5_V Λ F) (c : ℂ), v = c • f z := by
  constructor
  · rintro ⟨⟨t, w⟩, ⟨⟨z, u⟩, hu, he⟩, hv⟩
    have huw : u = w := congrArg Prod.snd he
    change w = v at hv
    subst w
    subst u
    obtain ⟨c, hc⟩ := (b54_vectorIncidence_iff _ z v
      (hbase z)).mp hu
    exact ⟨z, c, hc⟩
  · rintro ⟨z, c, rfl⟩
    refine ⟨(b2_torusCover Λ F z, c • f z), ?_, rfl⟩
    refine ⟨(z, c • f z), ?_, rfl⟩
    exact (b54_vectorIncidence_iff _ z _
      (hbase z)).mpr ⟨c, rfl⟩

end HodgeLean.Foundations.Program
