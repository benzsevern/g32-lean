import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeLength

/-! # Fibre length at an actual source point

This is the length of the source-stalk quotient by the extended target
maximal ideal. No choice of a point of an auxiliary fibre is needed.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
namespace AlgebraicGeometry.SingularCycles

def pointFibreLength {X Z : Scheme} (f : X ⟶ Z) (x : X) : ℕ∞ :=
  Module.length (X.presheaf.stalk x)
    (X.presheaf.stalk x ⧸
      (IsLocalRing.maximalIdeal (Z.presheaf.stalk (f x))).map (f.stalkMap x).hom)

theorem pointFibreLength_eq_genericLength {X Z : Scheme} [IsNoetherian Z]
    (f : X ⟶ Z) (z : Z) (y : (ccm3_inverseIdeal f z).subscheme)
    (hy : f ((ccm3_inverseIdeal f z).subschemeι y) = z) :
    pointFibreLength f ((ccm3_inverseIdeal f z).subschemeι y) = ccm3_genericLength f z y :=
  (genericLength_eq_source_stalk_quotient f z y hy).symm

theorem genericMultiplicity_eq_pointFibreLength {X Z : Scheme} [IsNoetherian Z]
    (f : X ⟶ Z) (z : Z) (y : (ccm3_inverseIdeal f z).subscheme)
    (hy : f ((ccm3_inverseIdeal f z).subschemeι y) = z)
    (hfin : ccm3_genericLength f z y < ⊤) :
    (genericMultiplicity f z y hfin : ℕ∞) =
      pointFibreLength f ((ccm3_inverseIdeal f z).subschemeι y) := by
  rw [pointFibreLength_eq_genericLength f z y hy]
  exact ENat.natCast_toNat (ne_of_lt hfin)

theorem parameter_source_quotient_length_eq_fibreLength
    {X Z : Scheme} (f : X ⟶ Z) (x : X) (U : Z.Opens) (hx : f x ∈ U)
    {d : ℕ} (g : Fin d → Γ(Z, U))
    (hgen : Ideal.ofList (List.ofFn fun j => Z.presheaf.germ U (f x) hx (g j)) =
      IsLocalRing.maximalIdeal (Z.presheaf.stalk (f x))) :
    Module.length (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ Ideal.ofList (List.ofFn fun j =>
        X.presheaf.germ (f ⁻¹ᵁ U) x hx (f.app U (g j)))) = pointFibreLength f x := by
  have hideal : Ideal.ofList (List.ofFn fun j =>
      X.presheaf.germ (f ⁻¹ᵁ U) x hx (f.app U (g j))) =
      (Ideal.ofList (List.ofFn fun j => Z.presheaf.germ U (f x) hx (g j))).map
        (f.stalkMap x).hom := by
    rw [Ideal.map_ofList, List.map_ofFn]
    apply congrArg Ideal.ofList
    apply congrArg List.ofFn
    funext j
    exact (Scheme.Hom.germ_stalkMap_apply f U x hx (g j)).symm
  rw [hideal, hgen]
  rfl

end AlgebraicGeometry.SingularCycles
