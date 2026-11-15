import HodgeLean.Foundations.Program.SchoenTransferQ3ComponentLengthBase
import HodgeLean.Foundations.Program.SchoenTransferQ3ComponentEtale
import HodgeLean.Foundations.Program.SchoenTransferQ3ClosedBaseFibreLength

/-! Synchronized smooth support and unreduced-length data for an actual inverse component. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
open HodgeLean.Adapters AlgebraicGeometry.SingularCycles
namespace HodgeLean.Foundations.Program

/-- Every retained inverse component has an actual finite reduced-component
square and one smooth etale base on which the ambient fibre length is its
original unreduced generic multiplicity. -/
theorem s4_q3_retained_component_generic_length_base
    {X W : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFinitePresentation W.hom] [QuasiCompact W.hom]
    (q : X ⟶ W) [IsFinite q.left] (hq : IsOpenMap q.left)
    (x : W.left) (η : (ccm3_inverseIdeal q.left x).subscheme)
    (hη : closure ({η} : Set (ccm3_inverseIdeal q.left x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal q.left x).subscheme) :
    let p := (ccm3_inverseIdeal q.left x).subschemeι η
    let C : Over (Spec ↧ℂ) := Over.mk ((ccm3_primeIdeal X.left p).subschemeι ≫ X.hom)
    let D : Over (Spec ↧ℂ) := Over.mk ((ccm3_primeIdeal W.left x).subschemeι ≫ W.hom)
    ∃ (ψ : C.left ⟶ (ccm3_inverseIdeal q.left x).subscheme) (f : C ⟶ D),
      ψ ≫ (ccm3_inverseIdeal q.left x).subschemeι = (ccm3_primeIdeal X.left p).subschemeι ∧
      f.left ≫ (ccm3_primeIdeal W.left x).subschemeι =
        (ccm3_primeIdeal X.left p).subschemeι ≫ q.left ∧
      IsClosedImmersion ψ ∧ IsFinite f.left ∧ Function.Surjective f.left ∧
      ∃ S : D.left.Opens, Dense (S : Set D.left) ∧
        Smooth (S.ι ≫ D.hom) ∧ Etale (f.left ∣_ S) ∧
        Smooth ((f.left ⁻¹ᵁ S).ι ≫ C.hom) ∧
        IsOpenEmbedding ((((f.left ⁻¹ᵁ S).ι ≫ ψ)).base) ∧
        ∀ (c : C.left), f.left c ∈ S → ∀ (r : ℕ), Order.coheight (f.left c) = r →
          IsRegularLocalRing (D.left.presheaf.stalk (f.left c)) →
          pointFibreLength q.left ((ccm3_primeIdeal X.left p).subschemeι c) =
            (genericMultiplicity q.left x η (ccm3_genericLength_finite_pos q x η hη).2 : ℕ∞) := by
  let K := ccm3_inverseIdeal q.left x
  let p := K.subschemeι η
  let I := ccm3_primeIdeal X.left p
  let J := ccm3_primeIdeal W.left x
  let C : Over (Spec ↧ℂ) := Over.mk (I.subschemeι ≫ X.hom)
  let D : Over (Spec ↧ℂ) := Over.mk (J.subschemeι ≫ W.hom)
  letI : IsIntegral C.left := inferInstanceAs (IsIntegral (cycleComponent X.left p))
  letI : IsIntegral D.left := inferInstanceAs (IsIntegral (cycleComponent W.left x))
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : IsNoetherian X.left := {}
  letI : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian W.hom
  letI : LocallyOfFinitePresentation D.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (J.subschemeι ≫ W.hom))
  letI : IsLocallyNoetherian K.subscheme := LocallyOfFiniteType.isLocallyNoetherian K.subschemeι
  letI : NoetherianSpace K.subscheme := K.subschemeι.isClosedEmbedding.isInducing.noetherianSpace
  letI : IsNoetherian K.subscheme := {}
  obtain ⟨ψ, hψ, hclosed, himage⟩ := s4_q3_inverse_reduced_support_map q.left x η
  letI : IsClosedImmersion ψ := hclosed
  have hmap : q.left p = x := s4_q3_inverse_component_dominates q.left hq x η hη
  have hdata := s4_q3_reduced_component_dense_etale_open q p
  rw [hmap] at hdata
  obtain ⟨f, hf, hfinite, hsurj, S₀, hd₀, he₀⟩ := hdata
  let fC : C ⟶ D := Over.homMk f (by
    change f ≫ J.subschemeι ≫ W.hom = I.subschemeι ≫ X.hom
    rw [← Category.assoc, hf, Category.assoc, Over.w q])
  letI : IsFinite fC.left := hfinite
  let κ := Scheme.IdealSheafData.subschemeMap K J q.left (J.le_map_comap q.left)
  have hκ : κ ≫ J.subschemeι = K.subschemeι ≫ q.left :=
    K.subschemeMap_subschemeι J q.left (J.le_map_comap q.left)
  letI : IsFinite (κ ≫ J.subschemeι) := by rw [hκ]; infer_instance
  letI : IsFinite κ := IsFinite.of_comp κ J.subschemeι
  have hcompat : ψ ≫ κ = fC.left :=
    s4_q3_inverse_support_component_square q.left J I.subschemeι ψ f hψ hf
  have hgenI : I.subschemeι (genericPoint C.left) = p := by
    change cycleComponentι X.left p (genericPoint (cycleComponent X.left p)) = p
    rw [← cycleComponentGenericPoint_eq_genericPoint, cycleComponentι_genericPoint]
  have hgeneric : ψ (genericPoint C.left) = η := by
    apply K.subschemeι.isClosedEmbedding.injective
    have he := congrArg (fun k : I.subscheme ⟶ X.left => k (genericPoint C.left)) hψ
    exact he.trans hgenI
  obtain ⟨S, hdS, _, hsD, he, hsC, hopen, hgood⟩ :=
    s4_q3_component_generic_length_base q x η hη ψ himage hgeneric κ fC hsurj hcompat S₀ hd₀ he₀
  refine ⟨ψ, fC, hψ, hf, hclosed, hfinite, hsurj, S, hdS, hsD, he, hsC, hopen, ?_⟩
  intro c hc r hr hreg
  have hι := congrArg (fun k : I.subscheme ⟶ X.left => k c) hψ
  calc
    pointFibreLength q.left (I.subschemeι c) = pointFibreLength q.left (K.subschemeι (ψ c)) :=
      congrArg (pointFibreLength q.left) hι.symm
    _ = pointFibreLength κ (ψ c) := (s4_q3_inverse_support_point_fibre_length q.left J (ψ c)).symm
    _ = _ := hgood c hc r hr hreg

end HodgeLean.Foundations.Program
