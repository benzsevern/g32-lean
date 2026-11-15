import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cCoefficients
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cHomologyClasses
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cOpenLift

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false in
theorem b6m_relative_reduction_preserves_zero (P : TopPair.{0}) (n k : ℕ)
    (c : ((relativeChainFunctor ℤ).obj P).cycles k)
    (d : ((relativeChainFunctor (ZMod n)).obj P).cycles k)
    (a : (SingularChainComplex ℤ P.fst).X k)
    (hc : ((relativeChainProjection ℤ P).f k).hom a =
      (((relativeChainFunctor ℤ).obj P).iCycles k).hom c)
    (hd : ((relativeChainProjection (ZMod n) P).f k).hom
      (b6m_singularReduction P.fst n k a) =
        (((relativeChainFunctor (ZMod n)).obj P).iCycles k).hom d)
    (hz : (((relativeChainFunctor ℤ).obj P).homologyπ k).hom c = 0) :
    (((relativeChainFunctor (ZMod n)).obj P).homologyπ k).hom d = 0 := by
  let C := SingularChainComplex ℤ P.fst
  let D := SingularChainComplex (ZMod n) P.fst
  let Q := (relativeChainFunctor ℤ).obj P
  let Q' := (relativeChainFunctor (ZMod n)).obj P
  let π := relativeChainProjection ℤ P
  let π' := relativeChainProjection (ZMod n) P
  obtain ⟨b, hb⟩ := (b6m_homologyπ_zero_iff_boundary ℤ Q k c).mp hz
  obtain ⟨t, ht⟩ := b6m_relativeChainProjection_surjective ℤ P (k + 1) b
  have hπdt : (π.f k).hom ((C.d (k + 1) k).hom t) = (Q.d (k + 1) k).hom b := by
    have h := congrArg (fun f => f.hom t) (π.comm (k + 1) k)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [← h, ht]
  have hzero : (π.f k).hom (a - (C.d (k + 1) k).hom t) = 0 := by
    rw [map_sub, hc, hπdt, hb, sub_self]
  obtain ⟨u, hu⟩ := b6m_relativeChainProjection_exact ℤ P k _ hzero
  have hπdiff : (π'.f k).hom
      (b6m_singularReduction P.fst n k (a - (C.d (k + 1) k).hom t)) = 0 := by
    rw [← hu]
    change (π'.f k).hom (b6m_singularReduction P.fst n k
      (((((singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map P.map).f k).hom u)) = 0
    rw [b6m_singularReduction_map]
    exact congrArg (fun f => (f.f k).hom (b6m_singularReduction P.snd n k u))
      (subspaceChainMap_relativeChainProjection (ZMod n) P)
  have hπeq : (π'.f k).hom (b6m_singularReduction P.fst n k a) =
      (π'.f k).hom (b6m_singularReduction P.fst n k ((C.d (k + 1) k).hom t)) := by
    simpa only [map_sub, sub_eq_zero] using hπdiff
  apply (b6m_homologyπ_zero_iff_boundary (ZMod n) Q' k d).mpr
  refine ⟨(π'.f (k + 1)).hom (b6m_singularReduction P.fst n (k + 1) t), ?_⟩
  have hcomm := congrArg (fun f => f.hom (b6m_singularReduction P.fst n (k + 1) t))
    (π'.comm (k + 1) k)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
  calc
    _ = (π'.f k).hom ((D.d (k + 1) k).hom
        (b6m_singularReduction P.fst n (k + 1) t)) := hcomm
    _ = (π'.f k).hom (b6m_singularReduction P.fst n k ((C.d (k + 1) k).hom t)) := by
      exact congrArg (π'.f k).hom (b6m_singularReduction_boundary P.fst n k t).symm
    _ = (π'.f k).hom (b6m_singularReduction P.fst n k a) := hπeq.symm
    _ = _ := hd

set_option backward.isDefEq.respectTransparency false in
theorem b6m_relative_reduction_preserves_eq (P : TopPair.{0}) (n k : ℕ)
    (c₁ c₂ : ((relativeChainFunctor ℤ).obj P).cycles k)
    (d₁ d₂ : ((relativeChainFunctor (ZMod n)).obj P).cycles k)
    (a₁ a₂ : (SingularChainComplex ℤ P.fst).X k)
    (hc₁ : ((relativeChainProjection ℤ P).f k).hom a₁ =
      (((relativeChainFunctor ℤ).obj P).iCycles k).hom c₁)
    (hc₂ : ((relativeChainProjection ℤ P).f k).hom a₂ =
      (((relativeChainFunctor ℤ).obj P).iCycles k).hom c₂)
    (hd₁ : ((relativeChainProjection (ZMod n) P).f k).hom
      (b6m_singularReduction P.fst n k a₁) =
        (((relativeChainFunctor (ZMod n)).obj P).iCycles k).hom d₁)
    (hd₂ : ((relativeChainProjection (ZMod n) P).f k).hom
      (b6m_singularReduction P.fst n k a₂) =
        (((relativeChainFunctor (ZMod n)).obj P).iCycles k).hom d₂)
    (h : (((relativeChainFunctor ℤ).obj P).homologyπ k).hom c₁ =
      (((relativeChainFunctor ℤ).obj P).homologyπ k).hom c₂) :
    (((relativeChainFunctor (ZMod n)).obj P).homologyπ k).hom d₁ =
      (((relativeChainFunctor (ZMod n)).obj P).homologyπ k).hom d₂ := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply b6m_relative_reduction_preserves_zero P n k (c₁ - c₂) (d₁ - d₂) (a₁ - a₂)
  · simp only [map_sub, hc₁, hc₂]
  · simp only [map_sub, hd₁, hd₂]
  · rw [map_sub, h, sub_self]

end HodgeLean.Foundations.Program
