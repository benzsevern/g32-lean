import HodgeLean.Foundations.BundleThom.RealNormalEquatorProjectionHelpers
import HodgeLean.Foundations.BundleThom.TopologicalProjectionCoverHelpers

/-! # Projection from actual punctured real products

HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Projection restricted to either cap in the actual punctured product is a rational chain quasi-isomorphism.
Source: Hatcher, Algebraic Topology, §2.2, contractions of the actual cover domains. -/
theorem i1_realPuncturedProductCapProjection_quasiIso
    (B : Type) [TopologicalSpace B] (d : ℕ) (positive : Bool) :
    QuasiIso (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map
      (topologicalSubsetInclusion (TopCat.of (B × {x : Fin (d + 1) → ℝ | x ≠ 0}))
        {p | p.2.1 ∈ i1_realNormalCap d positive} ≫
      TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ :
        ContinuousMap (B × {x : Fin (d + 1) → ℝ | x ≠ 0}) B))) := by
  letI := i1_realNormalPuncturedCap_contractible d positive
  exact i1_productSecondSubsetProjection_quasiIso B {x : Fin (d + 1) → ℝ | x ≠ 0}
    {x | x.1 ∈ i1_realNormalCap d positive}

/-- Punctured real product projection is invertible on rational homology below the first possible sphere degree over any base.
Source: Hatcher, Algebraic Topology, §2.2, the two-cap Mayer–Vietoris induction. -/
theorem i1_realPuncturedProductProjection_homology_isIso
    (B : Type) [TopologicalSpace B] (d n : ℕ) (hn : n + 1 < d) :
    IsIso (HomologicalComplex.homologyMap
      (((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map
        (TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ :
          ContinuousMap (B × {x : Fin d → ℝ | x ≠ 0}) B))) n) := by
  induction d generalizing n with
  | zero => omega
  | succ d ih =>
    have hd : 0 < d := by omega
    let X := TopCat.of (B × {x : Fin (d + 1) → ℝ | x ≠ 0})
    let p : X ⟶ TopCat.of B := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
    let U : Set X := {z | z.2.1 ∈ i1_realNormalCap d true}
    let V : Set X := {z | z.2.1 ∈ i1_realNormalCap d false}
    have hi : U ∩ V = {z : X | Fin.tail z.2.1 ≠ 0} := by
      ext z
      change (z.2.1 ∈ i1_realNormalCap d true ∩ i1_realNormalCap d false) ↔ _
      rw [i1_realNormalCap_inter]
      rfl
    refine i1_topologicalBinaryProjection_homology_isIso X (TopCat.of B) p U V
      ((i1_realNormalCap_isOpen d true).preimage
        (continuous_subtype_val.comp continuous_snd))
      ((i1_realNormalCap_isOpen d false).preimage
        (continuous_subtype_val.comp continuous_snd))
      ?_ (i1_realPuncturedProductCapProjection_quasiIso B d true)
      (i1_realPuncturedProductCapProjection_quasiIso B d false) n ?_ ?_
    · apply Set.eq_univ_of_forall
      intro z
      have hz : z.2.1 ∈ i1_realNormalCap d true ∪ i1_realNormalCap d false := by
        rw [i1_realNormalCap_union]
        exact z.2.2
      exact hz
    · rw [hi]
      apply (i1_realNormalEquatorProjection_homology_epi_iff B d n).mpr
      have hw : (fun _ : Fin d => (1 : ℝ)) ≠ 0 := by
        intro h
        have hh := congrFun h ⟨0, hd⟩
        norm_num at hh
      exact i1_productProjection_homology_epi B {x : Fin d → ℝ | x ≠ 0}
        ⟨fun _ => 1, hw⟩ n
    · intro m hm
      rw [hi]
      apply (i1_realNormalEquatorProjection_homology_isIso_iff B d m).mpr
      apply ih m
      change m + 1 = n at hm
      omega

end HodgeLean.Foundations.BundleThom
