import HodgeLean.Foundations.RationalHomologyManifold.CompactSheafBoundary
import HodgeLean.Foundations.RationalHomologyManifold.SheafImageLocalLifting
import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionSoftness

/-! Compact extension for the actual boundary image in the subdivision-limit chain sheaf.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual boundary-image inclusion has zero composite with the next boundary.
Source: Mathlib, Algebra.Homology.HomologicalComplex, d_comp_d; the image factorization.
HC no distance; AV milestone no distance.
-/
theorem subdivision_boundary_image_comp_zero (X : TopCat.{0}) (n : ℕ) :
    image.ι ((subdivisionLimitSheafComplex X).d (n + 2) (n + 1)) ≫
      (subdivisionLimitSheafComplex X).d (n + 1) n = 0 := by
  apply (cancel_epi (factorThruImage ((subdivisionLimitSheafComplex X).d (n + 2) (n + 1)))).mp
  rw [← Category.assoc, image.fac, HomologicalComplex.d_comp_d, comp_zero]

#print axioms subdivision_boundary_image_comp_zero
/-- In positive orientation degree, the actual boundary-image sheaf is soft.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; compact support detection and extension of chain boundaries.
HC no distance; AV milestone no distance.
-/
theorem subdivision_boundary_image_isSoft (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (t : FiniteTriangulation X) (n : ℕ) (o : LocalRationalOrientation X (n + 1)) :
    IsSoft (image ((subdivisionLimitSheafComplex X).d (n + 2) (n + 1))) := by
  classical
  intro K U hK hKU s
  let C := subdivisionLimitSheafComplex X
  let f := C.d (n + 2) (n + 1)
  let I := image f
  let j := image.ι f
  let g := factorThruImage f
  let L := (C.X (n + 1)).obj
  let sC := j.hom.app (Opposite.op U) s
  obtain ⟨N, hNU, hKN, M, z, hz⟩ := subdivisionLimitSheaf_extend_by_ambient X (n + 1)
    K hK U hKU sC
  have hrN := ConcreteCategory.congr_hom
    (subdivisionAmbientSectionMap_restriction X (n + 1) M ⊤ N le_top) z
  change L.map (homOfLE (show N ≤ ⊤ from le_top)).op
      ((subdivisionAmbientSectionMap X (n + 1) ⊤ M).hom z) =
    (subdivisionAmbientSectionMap X (n + 1) N M).hom z at hrN
  have hzN : (subdivisionAmbientSectionMap X (n + 1) N M).hom z =
      L.map (homOfLE hNU).op sC := hrN.symm.trans hz
  let sN := I.obj.map (homOfLE hNU).op s
  have hjN := ConcreteCategory.congr_hom (j.hom.naturality (homOfLE hNU).op) s
  change j.hom.app (Opposite.op N) sN = L.map (homOfLE hNU).op sC at hjN
  have hzin := hzN.trans hjN.symm
  have hcycle : ((C.d (n + 1) n).hom.app (Opposite.op N))
      ((subdivisionAmbientSectionMap X (n + 1) N M).hom z) = 0 := by
    have hd := ConcreteCategory.congr_hom
      (congrArg (fun φ => φ.hom.app (Opposite.op N))
        (subdivision_boundary_image_comp_zero X n)) sN
    change ((C.d (n + 1) n).hom.app (Opposite.op N))
      (j.hom.app (Opposite.op N) sN) = 0 at hd
    exact (congrArg ((C.d (n + 1) n).hom.app (Opposite.op N)) hzin).trans hd
  have hlocal : ∀ x ∈ K, ∃ (V : Opens X)
      (a : (C.X (n + 2)).obj.obj (Opposite.op V)), x ∈ V ∧
      f.hom.app (Opposite.op V) a = (subdivisionAmbientSectionMap X (n + 1) V M).hom z := by
    intro x hx
    obtain ⟨V, hVN, a, hxV, ha⟩ := sheaf_image_section_locally_lifts X f N sN x (hKN hx)
    have hj := ConcreteCategory.congr_hom (j.hom.naturality (homOfLE hVN).op) sN
    change j.hom.app (Opposite.op V) (I.obj.map (homOfLE hVN).op sN) =
      L.map (homOfLE hVN).op (j.hom.app (Opposite.op N) sN) at hj
    have hr := ConcreteCategory.congr_hom
      (subdivisionAmbientSectionMap_restriction X (n + 1) M N V hVN) z
    change L.map (homOfLE hVN).op ((subdivisionAmbientSectionMap X (n + 1) N M).hom z) =
      (subdivisionAmbientSectionMap X (n + 1) V M).hom z at hr
    exact ⟨V, a, hxV, ha.trans (hj.trans ((congrArg (L.map (homOfLE hVN).op) hzin).symm.trans hr))⟩
  obtain ⟨R, b, V, hKV, hb⟩ := compact_sheaf_boundary_ambient_primitive X t n M o N K
    hK.isCompact hKN z hcycle hlocal
  let W : Opens X := N ⊓ V
  have hWU : W ≤ U := inf_le_left.trans hNU
  have hKW : K ⊆ W := fun _ hx => ⟨hKN hx, hKV hx⟩
  let α := (subdivisionAmbientSectionMap X (n + 2) ⊤ (M + R)).hom b
  let τ := g.hom.app (Opposite.op ⊤) α
  refine ⟨W, hWU, hKW, τ, ?_⟩
  letI : Mono (j.hom.app (Opposite.op W)) := inferInstanceAs
    (Mono (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (Opposite.op W)).map
      ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).map j)))
  apply (AddCommGrpCat.mono_iff_injective (j.hom.app (Opposite.op W))).mp inferInstance
  have hl := ConcreteCategory.congr_hom
    (j.hom.naturality (homOfLE (show W ≤ ⊤ from le_top)).op) τ
  have hright := ConcreteCategory.congr_hom (j.hom.naturality (homOfLE hWU).op) s
  change j.hom.app (Opposite.op W) (I.obj.map (homOfLE (show W ≤ ⊤ from le_top)).op τ) =
    L.map (homOfLE (show W ≤ ⊤ from le_top)).op (j.hom.app (Opposite.op ⊤) τ) at hl
  change j.hom.app (Opposite.op W) (I.obj.map (homOfLE hWU).op s) =
    L.map (homOfLE hWU).op sC at hright
  have hfac := ConcreteCategory.congr_hom
    (congrArg (fun φ => φ.hom.app (Opposite.op ⊤)) (image.fac f)) α
  change j.hom.app (Opposite.op ⊤) τ = f.hom.app (Opposite.op ⊤) α at hfac
  have hbd := ConcreteCategory.congr_hom (subdivisionAmbientSectionMap_boundary X (n + 1) (M + R) ⊤) b
  change f.hom.app (Opposite.op ⊤) α =
    (subdivisionAmbientSectionMap X (n + 1) ⊤ (M + R)).hom
      ((SingularChainComplex ℚ X).d (n + 2) (n + 1) b) at hbd
  have hrTop := ConcreteCategory.congr_hom
    (subdivisionAmbientSectionMap_restriction X (n + 1) (M + R) ⊤ W le_top)
    ((SingularChainComplex ℚ X).d (n + 2) (n + 1) b)
  change L.map (homOfLE (show W ≤ ⊤ from le_top)).op
      ((subdivisionAmbientSectionMap X (n + 1) ⊤ (M + R)).hom
        ((SingularChainComplex ℚ X).d (n + 2) (n + 1) b)) =
    (subdivisionAmbientSectionMap X (n + 1) W (M + R)).hom
      ((SingularChainComplex ℚ X).d (n + 2) (n + 1) b) at hrTop
  have hwproj : (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (W : Set X)ᶜ)).f (n + 1)
      ((rationalSubdivisionIterate X R).f (n + 1) z) =
    (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (W : Set X)ᶜ)).f (n + 1)
      ((SingularChainComplex ℚ X).d (n + 2) (n + 1) b) := by
    apply (supportedChainProjection_eq_iff_coefficients X (W : Set X) (n + 1) _ _).mpr
    rintro σ ⟨u, hu⟩
    exact (supportedChainProjection_eq_iff_coefficients X (V : Set X) (n + 1) _ _).mp hb σ
      ⟨u, (show W ≤ V from inf_le_right) hu⟩
  have hwsec : (subdivisionAmbientSectionMap X (n + 1) W (M + R)).hom
      ((rationalSubdivisionIterate X R).f (n + 1) z) =
    (subdivisionAmbientSectionMap X (n + 1) W (M + R)).hom
      ((SingularChainComplex ℚ X).d (n + 2) (n + 1) b) := by
    exact congrArg (fun a => ((toSheafify (Opens.grothendieckTopology X)
      ((subdivisionLimitPresheafComplex X).X (n + 1))).app (Opposite.op W))
      ((((colimit.ι (presheafSubdivisionDiagram X) (M + R)).f (n + 1)).app (Opposite.op W)) a)) hwproj
  have ht := ConcreteCategory.congr_hom
    (subdivisionAmbientSectionMap_transition X (n + 1) W M R) z
  change (subdivisionAmbientSectionMap X (n + 1) W (M + R)).hom
      ((rationalSubdivisionIterate X R).f (n + 1) z) =
    (subdivisionAmbientSectionMap X (n + 1) W M).hom z at ht
  have hrNw := ConcreteCategory.congr_hom
    (subdivisionAmbientSectionMap_restriction X (n + 1) M N W inf_le_left) z
  change L.map (homOfLE (show W ≤ N from inf_le_left)).op
      ((subdivisionAmbientSectionMap X (n + 1) N M).hom z) =
    (subdivisionAmbientSectionMap X (n + 1) W M).hom z at hrNw
  have hcomp : L.map (homOfLE hNU).op ≫ L.map (homOfLE (show W ≤ N from inf_le_left)).op =
      L.map (homOfLE hWU).op := by rw [← L.map_comp]; rfl
  have hcompS := ConcreteCategory.congr_hom hcomp sC
  simp only [ConcreteCategory.comp_apply] at hcompS
  have horig := hrNw.symm.trans
    ((congrArg (L.map (homOfLE (show W ≤ N from inf_le_left)).op) hzN).trans hcompS)
  exact hl.trans ((congrArg (L.map (homOfLE (show W ≤ ⊤ from le_top)).op) hfac).trans
    ((congrArg (L.map (homOfLE (show W ≤ ⊤ from le_top)).op) hbd).trans
      (hrTop.trans (hwsec.symm.trans (ht.trans (horig.trans hright.symm))))))

#print axioms subdivision_boundary_image_isSoft
/-- At or above the orientation degree, each positive-degree boundary-image sheaf is soft.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; compact support detection and extension of chain boundaries.
HC no distance; AV milestone no distance.
-/
theorem subdivision_boundary_image_isSoft_of_le (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (t : FiniteTriangulation X) (N n : ℕ) (o : LocalRationalOrientation X N) (hN : N ≤ n + 1) :
    IsSoft (image ((subdivisionLimitSheafComplex X).d (n + 2) (n + 1))) := by
  classical
  intro K U hK hKU s
  let C := subdivisionLimitSheafComplex X
  let f := C.d (n + 2) (n + 1)
  let I := image f
  let j := image.ι f
  let g := factorThruImage f
  let L := (C.X (n + 1)).obj
  let sC := j.hom.app (Opposite.op U) s
  obtain ⟨N, hNU, hKN, M, z, hz⟩ := subdivisionLimitSheaf_extend_by_ambient X (n + 1)
    K hK U hKU sC
  have hrN := ConcreteCategory.congr_hom
    (subdivisionAmbientSectionMap_restriction X (n + 1) M ⊤ N le_top) z
  change L.map (homOfLE (show N ≤ ⊤ from le_top)).op
      ((subdivisionAmbientSectionMap X (n + 1) ⊤ M).hom z) =
    (subdivisionAmbientSectionMap X (n + 1) N M).hom z at hrN
  have hzN : (subdivisionAmbientSectionMap X (n + 1) N M).hom z =
      L.map (homOfLE hNU).op sC := hrN.symm.trans hz
  let sN := I.obj.map (homOfLE hNU).op s
  have hjN := ConcreteCategory.congr_hom (j.hom.naturality (homOfLE hNU).op) s
  change j.hom.app (Opposite.op N) sN = L.map (homOfLE hNU).op sC at hjN
  have hzin := hzN.trans hjN.symm
  have hcycle : ((C.d (n + 1) n).hom.app (Opposite.op N))
      ((subdivisionAmbientSectionMap X (n + 1) N M).hom z) = 0 := by
    have hd := ConcreteCategory.congr_hom
      (congrArg (fun φ => φ.hom.app (Opposite.op N))
        (subdivision_boundary_image_comp_zero X n)) sN
    change ((C.d (n + 1) n).hom.app (Opposite.op N))
      (j.hom.app (Opposite.op N) sN) = 0 at hd
    exact (congrArg ((C.d (n + 1) n).hom.app (Opposite.op N)) hzin).trans hd
  have hlocal : ∀ x ∈ K, ∃ (V : Opens X)
      (a : (C.X (n + 2)).obj.obj (Opposite.op V)), x ∈ V ∧
      f.hom.app (Opposite.op V) a = (subdivisionAmbientSectionMap X (n + 1) V M).hom z := by
    intro x hx
    obtain ⟨V, hVN, a, hxV, ha⟩ := sheaf_image_section_locally_lifts X f N sN x (hKN hx)
    have hj := ConcreteCategory.congr_hom (j.hom.naturality (homOfLE hVN).op) sN
    change j.hom.app (Opposite.op V) (I.obj.map (homOfLE hVN).op sN) =
      L.map (homOfLE hVN).op (j.hom.app (Opposite.op N) sN) at hj
    have hr := ConcreteCategory.congr_hom
      (subdivisionAmbientSectionMap_restriction X (n + 1) M N V hVN) z
    change L.map (homOfLE hVN).op ((subdivisionAmbientSectionMap X (n + 1) N M).hom z) =
      (subdivisionAmbientSectionMap X (n + 1) V M).hom z at hr
    exact ⟨V, a, hxV, ha.trans (hj.trans ((congrArg (L.map (homOfLE hVN).op) hzin).symm.trans hr))⟩
  obtain ⟨R, b, V, hKV, hb⟩ := compact_sheaf_boundary_ambient_primitive_of_le X t _ n M o hN N K
    hK.isCompact hKN z hcycle hlocal
  let W : Opens X := N ⊓ V
  have hWU : W ≤ U := inf_le_left.trans hNU
  have hKW : K ⊆ W := fun _ hx => ⟨hKN hx, hKV hx⟩
  let α := (subdivisionAmbientSectionMap X (n + 2) ⊤ (M + R)).hom b
  let τ := g.hom.app (Opposite.op ⊤) α
  refine ⟨W, hWU, hKW, τ, ?_⟩
  letI : Mono (j.hom.app (Opposite.op W)) := inferInstanceAs
    (Mono (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (Opposite.op W)).map
      ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).map j)))
  apply (AddCommGrpCat.mono_iff_injective (j.hom.app (Opposite.op W))).mp inferInstance
  have hl := ConcreteCategory.congr_hom
    (j.hom.naturality (homOfLE (show W ≤ ⊤ from le_top)).op) τ
  have hright := ConcreteCategory.congr_hom (j.hom.naturality (homOfLE hWU).op) s
  change j.hom.app (Opposite.op W) (I.obj.map (homOfLE (show W ≤ ⊤ from le_top)).op τ) =
    L.map (homOfLE (show W ≤ ⊤ from le_top)).op (j.hom.app (Opposite.op ⊤) τ) at hl
  change j.hom.app (Opposite.op W) (I.obj.map (homOfLE hWU).op s) =
    L.map (homOfLE hWU).op sC at hright
  have hfac := ConcreteCategory.congr_hom
    (congrArg (fun φ => φ.hom.app (Opposite.op ⊤)) (image.fac f)) α
  change j.hom.app (Opposite.op ⊤) τ = f.hom.app (Opposite.op ⊤) α at hfac
  have hbd := ConcreteCategory.congr_hom (subdivisionAmbientSectionMap_boundary X (n + 1) (M + R) ⊤) b
  change f.hom.app (Opposite.op ⊤) α =
    (subdivisionAmbientSectionMap X (n + 1) ⊤ (M + R)).hom
      ((SingularChainComplex ℚ X).d (n + 2) (n + 1) b) at hbd
  have hrTop := ConcreteCategory.congr_hom
    (subdivisionAmbientSectionMap_restriction X (n + 1) (M + R) ⊤ W le_top)
    ((SingularChainComplex ℚ X).d (n + 2) (n + 1) b)
  change L.map (homOfLE (show W ≤ ⊤ from le_top)).op
      ((subdivisionAmbientSectionMap X (n + 1) ⊤ (M + R)).hom
        ((SingularChainComplex ℚ X).d (n + 2) (n + 1) b)) =
    (subdivisionAmbientSectionMap X (n + 1) W (M + R)).hom
      ((SingularChainComplex ℚ X).d (n + 2) (n + 1) b) at hrTop
  have hwproj : (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (W : Set X)ᶜ)).f (n + 1)
      ((rationalSubdivisionIterate X R).f (n + 1) z) =
    (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (W : Set X)ᶜ)).f (n + 1)
      ((SingularChainComplex ℚ X).d (n + 2) (n + 1) b) := by
    apply (supportedChainProjection_eq_iff_coefficients X (W : Set X) (n + 1) _ _).mpr
    rintro σ ⟨u, hu⟩
    exact (supportedChainProjection_eq_iff_coefficients X (V : Set X) (n + 1) _ _).mp hb σ
      ⟨u, (show W ≤ V from inf_le_right) hu⟩
  have hwsec : (subdivisionAmbientSectionMap X (n + 1) W (M + R)).hom
      ((rationalSubdivisionIterate X R).f (n + 1) z) =
    (subdivisionAmbientSectionMap X (n + 1) W (M + R)).hom
      ((SingularChainComplex ℚ X).d (n + 2) (n + 1) b) := by
    exact congrArg (fun a => ((toSheafify (Opens.grothendieckTopology X)
      ((subdivisionLimitPresheafComplex X).X (n + 1))).app (Opposite.op W))
      ((((colimit.ι (presheafSubdivisionDiagram X) (M + R)).f (n + 1)).app (Opposite.op W)) a)) hwproj
  have ht := ConcreteCategory.congr_hom
    (subdivisionAmbientSectionMap_transition X (n + 1) W M R) z
  change (subdivisionAmbientSectionMap X (n + 1) W (M + R)).hom
      ((rationalSubdivisionIterate X R).f (n + 1) z) =
    (subdivisionAmbientSectionMap X (n + 1) W M).hom z at ht
  have hrNw := ConcreteCategory.congr_hom
    (subdivisionAmbientSectionMap_restriction X (n + 1) M N W inf_le_left) z
  change L.map (homOfLE (show W ≤ N from inf_le_left)).op
      ((subdivisionAmbientSectionMap X (n + 1) N M).hom z) =
    (subdivisionAmbientSectionMap X (n + 1) W M).hom z at hrNw
  have hcomp : L.map (homOfLE hNU).op ≫ L.map (homOfLE (show W ≤ N from inf_le_left)).op =
      L.map (homOfLE hWU).op := by rw [← L.map_comp]; rfl
  have hcompS := ConcreteCategory.congr_hom hcomp sC
  simp only [ConcreteCategory.comp_apply] at hcompS
  have horig := hrNw.symm.trans
    ((congrArg (L.map (homOfLE (show W ≤ N from inf_le_left)).op) hzN).trans hcompS)
  exact hl.trans ((congrArg (L.map (homOfLE (show W ≤ ⊤ from le_top)).op) hfac).trans
    ((congrArg (L.map (homOfLE (show W ≤ ⊤ from le_top)).op) hbd).trans
      (hrTop.trans (hwsec.symm.trans (ht.trans (horig.trans hright.symm))))))

#print axioms subdivision_boundary_image_isSoft_of_le
end HodgeLean.Foundations.RationalHomologyManifold
