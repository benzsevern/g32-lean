import HodgeLean.Foundations.Program.SchoenDescentGluing

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A descent on an open source chart transfers to the image open of an open
quotient chart when its inverse image is exactly the source chart. -/
theorem s2_descent_chart_transfer {A B X Y T : Scheme.{0}}
    (j : A ⟶ X) [IsOpenImmersion j] (p : A ⟶ B)
    (q : X ⟶ Y) (i : B ⟶ Y) [IsOpenImmersion i]
    (hcomm : j ≫ q = p ≫ i)
    (hrange : q ⁻¹' Set.range i = Set.range j)
    (f : X ⟶ T) (d : B ⟶ T) (hd : p ≫ d = j ≫ f) :
    ∃ e : i.opensRange.toScheme ⟶ T,
      (q ∣_ i.opensRange) ≫ e = (q ⁻¹ᵁ i.opensRange).ι ≫ f := by
  let W := i.opensRange
  have hj : Set.range j ⊆ Set.range (q ⁻¹ᵁ W).ι := by
    rw [Scheme.Opens.range_ι]
    intro x hx
    change q x ∈ Set.range i
    exact (congrArg (fun S : Set X => x ∈ S) hrange).mpr hx
  let j' := IsOpenImmersion.lift (q ⁻¹ᵁ W).ι j hj
  have hjfac : j' ≫ (q ⁻¹ᵁ W).ι = j := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion (j' ≫ (q ⁻¹ᵁ W).ι) := hjfac.symm ▸ inferInstance
  haveI : IsOpenImmersion j' := IsOpenImmersion.of_comp j' (q ⁻¹ᵁ W).ι
  have hsurj : Function.Surjective j' := by
    intro x
    have hx : x.val ∈ Set.range j := hrange ▸ x.property
    obtain ⟨a, ha⟩ := hx
    refine ⟨a, (q ⁻¹ᵁ W).ι.isOpenEmbedding.injective ?_⟩
    exact (congrArg (fun k => k a) hjfac).trans ha
  haveI : Epi j'.base := ConcreteCategory.epi_of_surjective _ hsurj
  haveI : IsIso j' := IsOpenImmersion.isIso j'
  have hjq : j' ≫ (q ∣_ W) = p ≫ i.isoOpensRange.hom := by
    apply (cancel_mono W.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hjfac,
      Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
    exact hcomm
  refine ⟨i.isoOpensRange.inv ≫ d, ?_⟩
  apply (cancel_epi j').mp
  rw [← Category.assoc, hjq, Category.assoc, ← Category.assoc i.isoOpensRange.hom,
    Iso.hom_inv_id, Category.id_comp, hd, ← hjfac, Category.assoc]

/-- Surjectivity of a chart projection identifies its quotient-chart image. -/
theorem s2_commutative_square_range {A B X Y : Scheme.{0}}
    (j : A ⟶ X) (p : A ⟶ B) (q : X ⟶ Y) (i : B ⟶ Y)
    (hcomm : j ≫ q = p ≫ i) (hp : Function.Surjective p) :
    Set.range i = q '' Set.range j := by
  ext y
  constructor
  · rintro ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := hp b
    exact ⟨j a, ⟨a, rfl⟩, congrArg (fun f => f a) hcomm⟩
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨p a, (congrArg (fun f => f a) hcomm).symm⟩

end HodgeLean.Foundations.Program
