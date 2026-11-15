import HodgeLean.Foundations.Program.TorusAlgebraizationB54Incidence
import HodgeLean.Foundations.Program.TorusAlgebraizationB54AnalyticCoordinates
import HodgeLean.Foundations.Program.RelativeTorusTopology

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

theorem b54_sectionCoordinates_cover_eq {ι : Type*}
    (b : Module.Basis ι ℂ (b5_sections Λ F hF Q 3)) (z w : b5_V Λ F)
    (h : b2_torusCover Λ F z = b2_torusCover Λ F w) :
    ∃ c : ℂ, c ≠ 0 ∧ b54_sectionCoordinates Λ F hF Q b z =
      c • b54_sectionCoordinates Λ F hF Q b w := by
  obtain ⟨l, hl⟩ := QuotientAddGroup.eq_iff_sub_mem.mp h
  have hz : z = w + b5_lattice Λ F l := by
    have hh : b2_coord _ ((b2_coordHomeomorph Λ F).symm z) =
        b2_coord _ ((b2_coordHomeomorph Λ F).symm w) +
          b2_coord _ (b2_latticeMap Λ F l) := by
      rw [hl, map_sub]
      abel
    change (b2_coordHomeomorph Λ F) ((b2_coordHomeomorph Λ F).symm z) =
      (b2_coordHomeomorph Λ F) ((b2_coordHomeomorph Λ F).symm w) + b5_lattice Λ F l at hh
    simpa only [Homeomorph.apply_symm_apply] using hh
  refine ⟨b5_factor Λ F hF Q l w ^ 3, ?_, ?_⟩
  · exact pow_ne_zero _ (mul_ne_zero (b5_chi Λ Q l).coe_ne_zero (Complex.exp_ne_zero _))
  · rw [hz]
    exact b54_sectionCoordinates_translate Λ F hF Q b l w

variable {ι : Type} [Fintype ι]

def b54_thetaIncidence (b : Module.Basis ι ℂ (b5_sections Λ F hF Q 3)) :
    Set (b2_torus Λ F × (ι → ℂ)) :=
  Prod.map (b2_torusCover Λ F) id ''
    b54_vectorIncidence (b54_sectionCoordinates Λ F hF Q b)

theorem b54_thetaIncidence_preimage
    (b : Module.Basis ι ℂ (b5_sections Λ F hF Q 3)) :
    Prod.map (b2_torusCover Λ F) id ⁻¹' b54_thetaIncidence Λ F hF Q b =
      b54_vectorIncidence (b54_sectionCoordinates Λ F hF Q b) := by
  ext p
  constructor
  · rintro ⟨⟨z, v⟩, hz, he⟩
    have hv : v = p.2 := congrArg Prod.snd he
    subst v
    obtain ⟨c, hc, hcoord⟩ := b54_sectionCoordinates_cover_eq Λ F hF Q b z p.1
      (congrArg Prod.fst he)
    intro i j
    have hh := hz i j
    change b54_sectionCoordinates Λ F hF Q b z i * p.2 j -
      b54_sectionCoordinates Λ F hF Q b z j * p.2 i = 0 at hh
    rw [hcoord] at hh
    simp only [Pi.smul_apply, smul_eq_mul] at hh
    apply (mul_eq_zero.mp ?_).resolve_left hc
    convert hh using 1 <;> ring
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem b54_thetaIncidence_isClosed
    (b : Module.Basis ι ℂ (b5_sections Λ F hF Q 3)) :
    IsClosed (b54_thetaIncidence Λ F hF Q b) := by
  have hq : IsOpenQuotientMap (b2_torusCover Λ F) :=
    (QuotientAddGroup.isOpenQuotientMap_mk (N := (b2_latticeMap Λ F).range)).comp
      (b2_coordHomeomorph Λ F).symm.isOpenQuotientMap
  apply (hq.prodMap (IsOpenQuotientMap.id (X := ι → ℂ))).isQuotientMap.isCoinducing.isClosed_preimage.mp
  rw [b54_thetaIncidence_preimage]
  exact (b54_vectorIncidence_isClosedAnalytic _ (fun i => (b i).property.1)).isClosed

section Analytic
variable [DiscreteTopology (b2_latticeMap Λ F).range]
local instance : ChartedSpace (b5_V Λ F × (ι → ℂ)) (b2_torus Λ F × (ι → ℂ)) :=
  prodChartedSpace (b5_V Λ F) (b2_torus Λ F) (ι → ℂ) (ι → ℂ)

theorem b54_thetaIncidence_isClosedAnalytic
    (b : Module.Basis ι ℂ (b5_sections Λ F hF Q 3)) :
    IsClosedAnalytic (b5_V Λ F × (ι → ℂ)) (b54_thetaIncidence Λ F hF Q b) := by
  have heq (x : b2_torus Λ F × (ι → ℂ)) (y : b5_V Λ F × (ι → ℂ)) :
      (chartAt (b5_V Λ F × (ι → ℂ)) x).symm y =
        Prod.map (b2_torusCover Λ F) id y := by
    apply Prod.ext
    · exact b2t_torusChart_symm_apply F x.1 y.1
    · rfl
  have hp : IsClosedAnalytic (b5_V Λ F × (ι → ℂ))
      (Prod.map (b2_torusCover Λ F) id ⁻¹' b54_thetaIncidence Λ F hF Q b) := by
    rw [b54_thetaIncidence_preimage]
    exact b54_vectorIncidence_isClosedAnalytic _ (fun i => (b i).property.1)
  refine ⟨b54_thetaIncidence_isClosed Λ F hF Q b, ?_⟩
  intro x hx
  let e := chartAt (b5_V Λ F × (ι → ℂ)) x
  have hxe : x ∈ e.source := mem_chart_source _ x
  have hy : e x ∈ Prod.map (b2_torusCover Λ F) id ⁻¹'
      b54_thetaIncidence Λ F hF Q b := by
    change Prod.map (b2_torusCover Λ F) id (e x) ∈ b54_thetaIncidence Λ F hF Q b
    rw [← heq, e.left_inv hxe]
    exact hx
  obtain ⟨U, hU, hUy, _, n, f, hf, hzero⟩ := hp.2 (e x) hy
  refine ⟨U ∩ e.target, hU.inter e.open_target, ⟨hUy, e.map_source hxe⟩,
    Set.inter_subset_right, n, f, fun i => (hf i).mono Set.inter_subset_left, ?_⟩
  intro y hy
  rw [heq]
  exact hzero y hy.1

end Analytic

theorem b54_thetaIncidence_scale
    (b : Module.Basis ι ℂ (b5_sections Λ F hF Q 3)) (c : ℂ)
    (t : b2_torus Λ F) (v : ι → ℂ) (hv : (t, v) ∈ b54_thetaIncidence Λ F hF Q b) :
    (t, c • v) ∈ b54_thetaIncidence Λ F hF Q b := by
  obtain ⟨⟨z, w⟩, hw, he⟩ := hv
  have ht : b2_torusCover Λ F z = t := congrArg Prod.fst he
  have hv : w = v := congrArg Prod.snd he
  subst w
  refine ⟨(z, c • v), ?_, ?_⟩
  · intro i j
    have hh := hw i j
    change b54_sectionCoordinates Λ F hF Q b z i * (c * v j) -
      b54_sectionCoordinates Λ F hF Q b z j * (c * v i) = 0
    calc
      _ = c * (b54_sectionCoordinates Λ F hF Q b z i * v j -
        b54_sectionCoordinates Λ F hF Q b z j * v i) := by ring
      _ = 0 := by rw [hh, mul_zero]
  · exact Prod.ext ht rfl

theorem b54_theta_cone_algebraic (n : ℕ)
    (b : Module.Basis (Fin n) ℂ (b5_sections Λ F hF Q 3)) :
    ∃ (m : ℕ) (d : Fin m → ℕ) (P : Fin m → MvPolynomial (Fin n) ℂ),
      (∀ i, (P i).IsHomogeneous (d i)) ∧
      Prod.snd '' b54_thetaIncidence Λ F hF Q b =
        {v | ∀ i, MvPolynomial.eval v (P i) = 0} := by
  letI := b2_latticeMap_discrete F hF
  letI := b2_torus_t2Space F
  letI := b2_torus_compactSpace F hF
  letI := b2_torus_isManifold F
  have hq : IsOpenQuotientMap (b2_torusCover Λ F) :=
    (QuotientAddGroup.isOpenQuotientMap_mk (N := (b2_latticeMap Λ F).range)).comp
      (b2_coordHomeomorph Λ F).symm.isOpenQuotientMap
  letI := Topology.IsOpenQuotientMap.secondCountableTopology hq
  exact b54_incidence_cone_algebraic n (b54_thetaIncidence Λ F hF Q b)
    (b54_thetaIncidence_isClosedAnalytic Λ F hF Q b)
    (b54_thetaIncidence_scale Λ F hF Q b)

theorem b54_theta_cone_mem_iff
    (b : Module.Basis ι ℂ (b5_sections Λ F hF Q 3))
    (hbase : ∀ z, ∃ s : b5_sections Λ F hF Q 3, s.val z ≠ 0) (v : ι → ℂ) :
    v ∈ Prod.snd '' b54_thetaIncidence Λ F hF Q b ↔
      ∃ (z : b5_V Λ F) (c : ℂ), v = c • b54_sectionCoordinates Λ F hF Q b z := by
  constructor
  · rintro ⟨⟨t, w⟩, ⟨⟨z, u⟩, hu, he⟩, hv⟩
    have huw : u = w := congrArg Prod.snd he
    change w = v at hv
    subst w
    subst u
    obtain ⟨c, hc⟩ := (b54_vectorIncidence_iff _ z v
      (b54_sectionCoordinates_ne_zero Λ F hF Q b z (hbase z))).mp hu
    exact ⟨z, c, hc⟩
  · rintro ⟨z, c, rfl⟩
    refine ⟨(b2_torusCover Λ F z, c • b54_sectionCoordinates Λ F hF Q b z), ?_, rfl⟩
    refine ⟨(z, c • b54_sectionCoordinates Λ F hF Q b z), ?_, rfl⟩
    exact (b54_vectorIncidence_iff _ z _
      (b54_sectionCoordinates_ne_zero Λ F hF Q b z (hbase z))).mpr ⟨c, rfl⟩

end HodgeLean.Foundations.Program
