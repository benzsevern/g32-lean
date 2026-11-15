import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Intersecting translates of an affine neighborhood of an orbit gives an
invariant affine neighborhood on a scheme with affine diagonal. -/
theorem s2_invariantAffineNeighborhood
    (X : Scheme) [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (U : X.Opens) (hU : IsAffineOpen U) (x : X)
    (hx : ∀ g : G, (ρ g).asIso.hom x ∈ U) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U ∧
      ∀ g : G, (ρ g).asIso.hom ⁻¹ᵁ V = V := by
  let V : X.Opens := ⨅ g : G, (ρ g).asIso.hom ⁻¹ᵁ U
  have hmem (y : X) : y ∈ V ↔ ∀ g : G, (ρ g).asIso.hom y ∈ U := by
    change y ∈ (V : Set X) ↔ _
    rw [TopologicalSpace.Opens.coe_iInf]
    simp only [Set.mem_iInter, SetLike.mem_coe, Scheme.Hom.mem_preimage]
  refine ⟨V, IsAffineOpen.iInf (fun g => hU.preimage (ρ g).asIso.hom),
    (hmem x).mpr hx, ?_, ?_⟩
  · intro y hy
    have hy1 := (hmem y).mp hy 1
    simpa using hy1
  · intro g
    ext y
    change (ρ g).asIso.hom y ∈ V ↔ y ∈ V
    rw [hmem, hmem]
    have hcomp (a b : G) : (ρ a).asIso.hom ((ρ b).asIso.hom y) = (ρ (a * b)).asIso.hom y := by
      rw [map_mul]
      rfl
    constructor
    · intro hy a
      have h := hy (a * g⁻¹)
      rw [hcomp, inv_mul_cancel_right] at h
      exact h
    · intro hy a
      rw [hcomp]
      exact hy (a * g)

/-- Restriction of an endomorphism preserving an open subscheme. -/
def s2_invariantOpenMap {X : Scheme} (U : X.Opens) (f : X ⟶ X)
    (h : U ≤ f ⁻¹ᵁ U) : U.toScheme ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι (U.ι ≫ f) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact h y.property)

@[reassoc (attr := simp)]
theorem s2_invariantOpenMap_ι {X : Scheme} (U : X.Opens) (f : X ⟶ X)
    (h : U ≤ f ⁻¹ᵁ U) : s2_invariantOpenMap U f h ≫ U.ι = U.ι ≫ f :=
  IsOpenImmersion.lift_fac _ _ _

/-- A scheme action restricts to every invariant open subscheme. -/
def s2_invariantOpenAction {X : Scheme} (G : Type) [Group G]
    (ρ : G →* Aut X) (U : X.Opens)
    (hU : ∀ g : G, (ρ g).asIso.hom ⁻¹ᵁ U = U) : G →* Aut U.toScheme where
  toFun g := Aut.of
    { hom := s2_invariantOpenMap U (ρ g).asIso.hom (hU g).ge
      inv := s2_invariantOpenMap U (ρ g⁻¹).asIso.hom (hU g⁻¹).ge
      hom_inv_id := by
        apply (cancel_mono U.ι).mp
        simp only [Category.assoc, s2_invariantOpenMap_ι, s2_invariantOpenMap_ι_assoc,
          Category.id_comp]
        have he : (ρ g).asIso.hom ≫ (ρ g⁻¹).asIso.hom = 𝟙 X := by
          have hm := congrArg (fun a : Aut X => a.asIso.hom) (ρ.map_mul g⁻¹ g)
          simpa using hm.symm
        rw [he, Category.comp_id]
      inv_hom_id := by
        apply (cancel_mono U.ι).mp
        simp only [Category.assoc, s2_invariantOpenMap_ι, s2_invariantOpenMap_ι_assoc,
          Category.id_comp]
        have he : (ρ g⁻¹).asIso.hom ≫ (ρ g).asIso.hom = 𝟙 X := by
          have hm := congrArg (fun a : Aut X => a.asIso.hom) (ρ.map_mul g g⁻¹)
          simpa using hm.symm
        rw [he, Category.comp_id] }
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply (cancel_mono U.ι).mp
    simp
  map_mul' g k := by
    apply Aut.ext
    apply Iso.ext
    apply (cancel_mono U.ι).mp
    simp [map_mul, Category.assoc]

/-- Inclusions between invariant opens commute with the restricted actions. -/
theorem s2_invariantOpenAction_homOfLE {X : Scheme} (G : Type) [Group G]
    (ρ : G →* Aut X) (U V : X.Opens) (hUV : U ≤ V)
    (hU : ∀ g : G, (ρ g).asIso.hom ⁻¹ᵁ U = U)
    (hV : ∀ g : G, (ρ g).asIso.hom ⁻¹ᵁ V = V) (g : G) :
    X.homOfLE hUV ≫ (s2_invariantOpenAction G ρ V hV g).asIso.hom =
      (s2_invariantOpenAction G ρ U hU g).asIso.hom ≫ X.homOfLE hUV := by
  apply (cancel_mono V.ι).mp
  change (X.homOfLE hUV ≫ s2_invariantOpenMap V (ρ g).asIso.hom (hV g).ge) ≫ V.ι =
    (s2_invariantOpenMap U (ρ g).asIso.hom (hU g).ge ≫ X.homOfLE hUV) ≫ V.ι
  simp only [Category.assoc, s2_invariantOpenMap_ι, Scheme.homOfLE_ι,
    Scheme.homOfLE_ι_assoc, s2_invariantOpenMap_ι_assoc]

end HodgeLean.Foundations.Program
