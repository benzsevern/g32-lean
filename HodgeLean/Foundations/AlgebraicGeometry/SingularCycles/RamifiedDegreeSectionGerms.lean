import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeFlatParameters
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreePointLength

/-! # Germs of parameters on smaller affine source opens

Restriction to a smaller source open commutes with the actual stalk map.
This permits the source parameter sections to be taken on an affine open.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.SingularCycles

theorem germ_appLE_parameter {X Z : Scheme} (f : X ⟶ Z)
    (U : Z.Opens) (V : X.Opens) (hVU : V ≤ f ⁻¹ᵁ U)
    (x : X) (hxV : x ∈ V) (s : Γ(Z, U)) :
    X.presheaf.germ V x hxV (f.appLE U V hVU s) =
      (f.stalkMap x).hom (Z.presheaf.germ U (f x) (hVU hxV) s) := by
  change X.presheaf.germ V x hxV
    (X.presheaf.map (homOfLE hVU).op (f.app U s)) = _
  rw [X.presheaf.germ_res_apply]
  exact (Scheme.Hom.germ_stalkMap_apply f U x (hVU hxV) s).symm

theorem evaluate_appLE_parameter {X Z : Over (Spec (CommRingCat.of ℂ))}
    (f : X ⟶ Z) (U : Z.left.Opens) (V : X.left.Opens) (hVU : V ≤ f.left ⁻¹ᵁ U)
    (x : ComplexPoint X) (hxV : x.underlying ∈ V) (s : Γ(Z.left, U)) :
    Point.evaluate V (f.left.appLE U V hVU s) x = Point.evaluate U s (Point.map f x) := by
  exact (Point.evaluate_res hVU (f.left.app U s) x hxV).symm.trans
    (Point.evaluate_map f U s x).symm

theorem appLE_parameter_quotient_length_eq_fibreLength
    {X Z : Scheme} (f : X ⟶ Z) (U : Z.Opens) (V : X.Opens)
    (hVU : V ≤ f ⁻¹ᵁ U) (x : X) (hxV : x ∈ V)
    {d : ℕ} (g : Fin d → Γ(Z, U))
    (hgen : Ideal.ofList (List.ofFn fun k => Z.presheaf.germ U (f x) (hVU hxV) (g k)) =
      IsLocalRing.maximalIdeal (Z.presheaf.stalk (f x))) :
    Module.length (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ Ideal.ofList (List.ofFn fun k =>
        X.presheaf.germ V x hxV (f.appLE U V hVU (g k)))) = pointFibreLength f x := by
  have hid : Ideal.ofList (List.ofFn fun k =>
      X.presheaf.germ V x hxV (f.appLE U V hVU (g k))) =
      (Ideal.ofList (List.ofFn fun k => Z.presheaf.germ U (f x) (hVU hxV) (g k))).map
        (f.stalkMap x).hom := by
    rw [Ideal.map_ofList, List.map_ofFn]
    apply congrArg Ideal.ofList
    apply congrArg List.ofFn
    funext k
    exact germ_appLE_parameter f U V hVU x hxV (g k)
  rw [hid, hgen]
  rfl

theorem regular_appLE_parameter_germs_pullback
    {X Z : Scheme} (f : X ⟶ Z) [Flat f] (U : Z.Opens) (V : X.Opens)
    (hVU : V ≤ f ⁻¹ᵁ U) (x : X) (hxV : x ∈ V)
    {d : ℕ} (g : Fin d → Γ(Z, U))
    (hreg : RingTheory.Sequence.IsRegular (Z.presheaf.stalk (f x))
      (List.ofFn fun k => Z.presheaf.germ U (f x) (hVU hxV) (g k))) :
    RingTheory.Sequence.IsRegular (X.presheaf.stalk x)
      (List.ofFn fun k => X.presheaf.germ V x hxV (f.appLE U V hVU (g k))) := by
  have h := regular_stalk_parameters_pullback f x _ hreg
  rw [List.map_ofFn] at h
  simp only [Function.comp_def] at h
  have heq : (fun k => (f.stalkMap x).hom
      (Z.presheaf.germ U (f x) (hVU hxV) (g k))) =
      (fun k => X.presheaf.germ V x hxV (f.appLE U V hVU (g k))) := by
    funext k
    exact (germ_appLE_parameter f U V hVU x hxV (g k)).symm
  rw [heq] at h
  exact h

theorem parameter_germs_at_equal_point
    {Z : Scheme} (U : Z.Opens) {d : ℕ} (g : Fin d → Γ(Z, U))
    (z z' : Z) (hz : z ∈ U) (hz' : z' ∈ U) (he : z = z')
    (hreg : RingTheory.Sequence.IsRegular (Z.presheaf.stalk z')
      (List.ofFn fun k => Z.presheaf.germ U z' hz' (g k)))
    (hgen : Ideal.ofList (List.ofFn fun k => Z.presheaf.germ U z' hz' (g k)) =
      IsLocalRing.maximalIdeal (Z.presheaf.stalk z')) :
    RingTheory.Sequence.IsRegular (Z.presheaf.stalk z)
        (List.ofFn fun k => Z.presheaf.germ U z hz (g k)) ∧
      Ideal.ofList (List.ofFn fun k => Z.presheaf.germ U z hz (g k)) =
        IsLocalRing.maximalIdeal (Z.presheaf.stalk z) := by
  subst z'
  exact ⟨hreg, hgen⟩

end AlgebraicGeometry.SingularCycles
