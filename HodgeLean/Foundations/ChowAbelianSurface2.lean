import HodgeLean.Foundations.ChowAbelianSurface2Proofs

/-! # Projective comparison obligations for E²

Implications from closed analyticity to embedding slices and from closedness to
punctured-cone closedness. Vertex extension and final Chow assembly are deferred.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Curves
namespace HodgeLean.Foundations

/-- Local equations for the projective image, anchored at a specified normalized point.
Source: Serre, GAGA, §§1–2, analytification of closed immersions;
Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3, analytic subsets. -/
theorem chowEE2_embedding_local_equations
    (p : ProjectiveSpace.Presentation (g3_power E 2).hom)
    (Z : Set (ComplexPoint (g3_power E 2)))
    (hZ : IsClosedAnalytic (Fin (dim (g3_power E 2).left) → ℂ) Z)
    (i : Fin (p.ambientDimension + 1)) (w : Fin p.ambientDimension → ℂ)
    (hw : ∃ hn : (i.insertNth (1 : ℂ) w : Fin (p.ambientDimension + 1) → ℂ) ≠ 0,
      ∃ x ∈ Z, x.left ≫ p.immersion =
        ComplexProjectiveSpace.vectorToProjectiveSpace (i.insertNth (1 : ℂ) w) hn) :
    ∃ U : Set (Fin p.ambientDimension → ℂ), IsOpen U ∧ w ∈ U ∧
      ∃ (m : ℕ) (f : Fin m → (Fin p.ambientDimension → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ v ∈ U,
          ((∃ hn : (i.insertNth (1 : ℂ) v : Fin (p.ambientDimension + 1) → ℂ) ≠ 0,
            ∃ x ∈ Z, x.left ≫ p.immersion =
              ComplexProjectiveSpace.vectorToProjectiveSpace (i.insertNth (1 : ℂ) v) hn) ↔
            ∀ j, f j v = 0) :=
  chowEE2_embedding_local_equations_aux p Z hZ i w hw

/-- Standard affine slices of the projective image of an analytic subset of E² are analytic.
Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3,
local analytic submanifolds and the projective cone construction;
Serre, GAGA, §§1–2, analytification of closed immersions. -/
theorem chowEE2_embedding_slices
    (p : ProjectiveSpace.Presentation (g3_power E 2).hom)
    (Z : Set (ComplexPoint (g3_power E 2)))
    (hZ : IsClosedAnalytic (Fin (dim (g3_power E 2).left) → ℂ) Z)
    (i : Fin (p.ambientDimension + 1)) :
    IsClosedAnalytic (Fin p.ambientDimension → ℂ)
      {w : Fin p.ambientDimension → ℂ |
        ∃ hw : (i.insertNth (1 : ℂ) w : Fin (p.ambientDimension + 1) → ℂ) ≠ 0,
        ∃ x ∈ Z, x.left ≫ p.immersion =
          ComplexProjectiveSpace.vectorToProjectiveSpace (i.insertNth (1 : ℂ) w) hw} :=
  chowEE2_embedding_slices_aux p Z hZ i

/-- The homogeneous-coordinate preimage of a closed subset of E² is closed off zero.
Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3,
homogeneous coordinates; compact images in Hausdorff projective space. -/
theorem chowEE2_punctured_closed
    (p : ProjectiveSpace.Presentation (g3_power E 2).hom)
    (Z : Set (ComplexPoint (g3_power E 2))) (hZ : IsClosed Z) :
    IsClosed {z : {z : Fin (p.ambientDimension + 1) → ℂ // z ≠ 0} |
      ∃ x ∈ Z, x.left ≫ p.immersion =
        ComplexProjectiveSpace.vectorToProjectiveSpace z.val z.property} :=
  chowEE2_punctured_closed_aux p Z hZ

/-- W1: the actual projective surface with no equations on its source.
Source: Segre projectivity for `g3_power E 2` and the empty family of analytic equations. -/
example : ∃ p : ProjectiveSpace.Presentation (g3_power E 2).hom,
    ∀ i : Fin (p.ambientDimension + 1),
    IsClosedAnalytic (Fin p.ambientDimension → ℂ)
      {w : Fin p.ambientDimension → ℂ |
        ∃ hw : (i.insertNth (1 : ℂ) w : Fin (p.ambientDimension + 1) → ℂ) ≠ 0,
        ∃ x ∈ (univ : Set (ComplexPoint (g3_power E 2))), x.left ≫ p.immersion =
          ComplexProjectiveSpace.vectorToProjectiveSpace (i.insertNth (1 : ℂ) w) hw} := by
  let p := Classical.choice
    (inferInstance : IsProjective (g3_power E 2).hom).nonempty_presentation
  exact ⟨p, fun i ↦ chowEE2_embedding_slices p univ isClosedAnalytic_univ i⟩

/-- W2: a single identity point gives a nonempty punctured cone.
Source: abelian exponential at zero, projective compactness, and surjective homogeneous coordinates. -/
example : ∃ p : ProjectiveSpace.Presentation (g3_power E 2).hom,
    IsClosed {z : {z : Fin (p.ambientDimension + 1) → ℂ // z ≠ 0} |
      ∃ x ∈ ({abelianExp (g3_power E 2) 0} : Set (ComplexPoint (g3_power E 2))),
        x.left ≫ p.immersion =
          ComplexProjectiveSpace.vectorToProjectiveSpace z.val z.property} ∧
    ({z : {z : Fin (p.ambientDimension + 1) → ℂ // z ≠ 0} |
      ∃ x ∈ ({abelianExp (g3_power E 2) 0} : Set (ComplexPoint (g3_power E 2))),
        x.left ≫ p.immersion =
          ComplexProjectiveSpace.vectorToProjectiveSpace z.val z.property}).Nonempty := by
  let p := Classical.choice
    (inferInstance : IsProjective (g3_power E 2).hom).nonempty_presentation
  refine ⟨p, chowEE2_punctured_closed p _ isClosed_singleton, ?_⟩
  let x := abelianExp (g3_power E 2) 0
  let y := p.analyticImmersion x
  obtain ⟨z, hz⟩ := ComplexProjectiveSpace.surjective_vectorToComplexPoint y
  refine ⟨z, x, mem_singleton x, ?_⟩
  exact (congrArg (fun q ↦ q.left) hz).symm

/-- W3: empty input exercises the slice endpoint with all premises supplied.
Source: empty analytic sets and Segre projectivity. -/
example : ∃ p : ProjectiveSpace.Presentation (g3_power E 2).hom,
    ∀ i : Fin (p.ambientDimension + 1),
    IsClosedAnalytic (Fin p.ambientDimension → ℂ)
      {w : Fin p.ambientDimension → ℂ |
        ∃ hw : (i.insertNth (1 : ℂ) w : Fin (p.ambientDimension + 1) → ℂ) ≠ 0,
        ∃ x ∈ (∅ : Set (ComplexPoint (g3_power E 2))), x.left ≫ p.immersion =
          ComplexProjectiveSpace.vectorToProjectiveSpace (i.insertNth (1 : ℂ) w) hw} := by
  let p := Classical.choice
    (inferInstance : IsProjective (g3_power E 2).hom).nonempty_presentation
  exact ⟨p, fun i ↦ chowEE2_embedding_slices p ∅ isClosedAnalytic_empty i⟩

/-- W4: local equations at a normalized representative of the identity on the whole surface.
Source: nonzero homogeneous representatives and normalization in a nonzero coordinate. -/
example : ∃ (p : ProjectiveSpace.Presentation (g3_power E 2).hom)
    (i : Fin (p.ambientDimension + 1)) (w : Fin p.ambientDimension → ℂ),
    ∃ U : Set (Fin p.ambientDimension → ℂ), IsOpen U ∧ w ∈ U ∧
      ∃ (m : ℕ) (f : Fin m → (Fin p.ambientDimension → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ v ∈ U,
          ((∃ hn : (i.insertNth (1 : ℂ) v : Fin (p.ambientDimension + 1) → ℂ) ≠ 0,
            ∃ x ∈ (univ : Set (ComplexPoint (g3_power E 2))), x.left ≫ p.immersion =
              ComplexProjectiveSpace.vectorToProjectiveSpace (i.insertNth (1 : ℂ) v) hn) ↔
            ∀ j, f j v = 0) := by
  classical
  let p := Classical.choice
    (inferInstance : IsProjective (g3_power E 2).hom).nonempty_presentation
  let x := abelianExp (g3_power E 2) 0
  obtain ⟨z, hz⟩ := ComplexProjectiveSpace.surjective_vectorToComplexPoint
    (p.analyticImmersion x)
  obtain ⟨i, hi⟩ : ∃ i, z.val i ≠ 0 := by
    by_contra h
    apply z.property
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  let w : Fin p.ambientDimension → ℂ := fun j ↦ z.val (i.succAbove j) / z.val i
  have hn : i.insertNth (1 : ℂ) w = (z.val i)⁻¹ • z.val := by
    apply Fin.insertNth_eq_iff.2
    constructor
    · simp [hi]
    · funext j
      simp [Fin.removeNth, w, div_eq_inv_mul]
  have hw : (i.insertNth (1 : ℂ) w : Fin (p.ambientDimension + 1) → ℂ) ≠ 0 := by
    rw [hn]
    exact smul_ne_zero (inv_ne_zero hi) z.property
  refine ⟨p, i, w, chowEE2_embedding_local_equations p univ
    isClosedAnalytic_univ i w ⟨hw, x, mem_univ x, ?_⟩⟩
  have hbase : x.left ≫ p.immersion =
      ComplexProjectiveSpace.vectorToProjectiveSpace z.val z.property :=
    (congrArg (fun q ↦ q.left) hz).symm
  have hvec : (⟨i.insertNth (1 : ℂ) w, hw⟩ :
      {v : Fin (p.ambientDimension + 1) → ℂ // v ≠ 0}) =
      ⟨(z.val i)⁻¹ • z.val, smul_ne_zero (inv_ne_zero hi) z.property⟩ :=
    Subtype.ext hn
  have hproj := congrArg
    (fun v : {v : Fin (p.ambientDimension + 1) → ℂ // v ≠ 0} ↦
      ComplexProjectiveSpace.vectorToProjectiveSpace v.val v.property) hvec
  exact hbase.trans (hproj.trans
    (ComplexProjectiveSpace.vectorToProjectiveSpace_smul z.val z.property
      (z.val i)⁻¹ (inv_ne_zero hi))).symm

/-- A singleton at the identity is nonempty and proper, and its punctured cone is closed.
Source: local injectivity of the abelian exponential and projective compactness. -/
example : ∃ v : Fin (dim (g3_power E 2).left) → ℂ,
    let x := abelianExp (g3_power E 2) 0
    let y := abelianExp (g3_power E 2) v
    y ≠ x ∧ ({x} : Set (ComplexPoint (g3_power E 2))).Nonempty ∧
      {x} ≠ Set.univ ∧
      ∃ p : ProjectiveSpace.Presentation (g3_power E 2).hom,
        IsClosed {z : {z : Fin (p.ambientDimension + 1) → ℂ // z ≠ 0} |
          ∃ q ∈ ({x} : Set (ComplexPoint (g3_power E 2))),
            q.left ≫ p.immersion =
              ComplexProjectiveSpace.vectorToProjectiveSpace z.val z.property} := by
  let X := g3_power E 2
  letI : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  obtain ⟨e, he0, he⟩ := complexExponential_localHomeomorph X (dim X.left)
  have he' : (fun v ↦ abelianExp X v) =ᶠ[nhds 0] e := by
    simpa only [abelianExp] using he
  have hgood : e.source ∩ {v | abelianExp X v = e v} ∈
      nhds (0 : Fin (dim X.left) → ℂ) :=
    Filter.inter_mem (e.open_source.mem_nhds he0) he'
  haveI : Nontrivial (Fin (dim X.left) → ℂ) := by
    rw [show dim X.left = 2 by simp [X, spec_g3link_dim_eq, E_dim]]
    infer_instance
  letI : PerfectSpace (Fin (dim X.left) → ℂ) :=
    perfectSpace_of_module ℂ (Fin (dim X.left) → ℂ)
  obtain ⟨v, hv, hv0⟩ := (preperfect_iff_nhds.mp
    (PerfectSpace.univ_preperfect : Preperfect
      (Set.univ : Set (Fin (dim X.left) → ℂ)))) 0 (Set.mem_univ 0) _ hgood
  refine ⟨v, ?_, Set.singleton_nonempty _, ?_, ?_⟩
  · intro h
    have hev : e v = e 0 := by
      rw [← hv.1.2, ← he'.self_of_nhds]
      exact h
    exact hv0 (e.injOn hv.1.1 he0 hev)
  · intro h
    have hy : abelianExp X v ∈ ({abelianExp X 0} : Set (ComplexPoint X)) := by
      rw [h]
      exact Set.mem_univ _
    exact (show abelianExp X v ≠ abelianExp X 0 from by
      intro h'; exact hv0 (e.injOn hv.1.1 he0
        (by rw [← hv.1.2, ← he'.self_of_nhds, h'])))
      (Set.mem_singleton_iff.mp hy)
  · let p := Classical.choice
      (inferInstance : IsProjective X.hom).nonempty_presentation
    exact ⟨p, chowEE2_punctured_closed p _ isClosed_singleton⟩

end HodgeLean.Foundations
