module

public import Mathlib.Algebra.Tropical.BigOperators
public import Mathlib.Algebra.Order.Group.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# The real max-plus semiring

This file supplies a numerical interface to max-plus tropical numbers and defines the
matrix-vector product on real vectors.  The latter is deliberately only defined for matrices
whose rows contain a finite coefficient.
-/

@[expose] public section

open scoped BigOperators

/-- The reversed order on `ℝ ∪ {-∞}` has `-∞` as an absorbing top element. -/
noncomputable instance : LinearOrderedAddCommMonoidWithTop (OrderDual (WithBot ℝ)) where
  top_add' x := by
    change (⊥ : WithBot ℝ) + OrderDual.ofDual x = ⊥
    simp
  isAddLeftRegular_of_ne_top x hx y z h := by
    change OrderDual.ofDual x ≠ (⊥ : WithBot ℝ) at hx
    change OrderDual.ofDual y = OrderDual.ofDual z
    apply WithBot.add_left_cancel hx
    exact h

/-- The max-plus semiring over the reals.  Its additive zero represents `-∞`. -/
abbrev RMax := Tropical (OrderDual (WithBot ℝ))

namespace RMax

/-- Forget the tropical and order-dual wrappers. -/
def toWithBot (x : RMax) : WithBot ℝ :=
  OrderDual.ofDual (Tropical.untrop x)

/-- Embed a real number as a finite max-plus number. -/
def ofReal (x : ℝ) : RMax :=
  Tropical.trop (OrderDual.toDual (x : WithBot ℝ))

@[simp] theorem toWithBot_zero : toWithBot 0 = ⊥ := rfl

@[simp] theorem toWithBot_one : toWithBot 1 = 0 := rfl

@[simp] theorem toWithBot_add (x y : RMax) :
    toWithBot (x + y) = max (toWithBot x) (toWithBot y) := rfl

@[simp] theorem toWithBot_mul (x y : RMax) :
    toWithBot (x * y) = toWithBot x + toWithBot y := rfl

@[simp] theorem toWithBot_ofReal (x : ℝ) : toWithBot (ofReal x) = x := rfl

theorem toWithBot_injective : Function.Injective toWithBot := by
  intro x y h
  exact Tropical.untrop_injective h

@[simp] theorem ofReal_injective : Function.Injective ofReal := by
  intro x y h
  apply WithBot.coe_eq_coe.mp
  exact Tropical.trop_injective h

@[simp] theorem ofReal_inj {x y : ℝ} : ofReal x = ofReal y ↔ x = y :=
  ofReal_injective.eq_iff

theorem ne_zero_iff_toWithBot_ne_bot (x : RMax) : x ≠ 0 ↔ toWithBot x ≠ ⊥ := by
  constructor
  · intro hx hbot
    apply hx
    apply toWithBot_injective
    simpa using hbot
  · intro hx hzero
    apply hx
    simpa [hzero]

/-- Extract the real represented by a nonzero max-plus number. -/
def toReal (x : RMax) (hx : x ≠ 0) : ℝ :=
  (toWithBot x).unbot ((ne_zero_iff_toWithBot_ne_bot x).mp hx)

@[simp] theorem coe_toReal (x : RMax) (hx : x ≠ 0) :
    (x.toReal hx : WithBot ℝ) = x.toWithBot :=
  WithBot.coe_unbot _ _

@[simp] theorem ofReal_toReal (x : RMax) (hx : x ≠ 0) : ofReal (x.toReal hx) = x := by
  apply toWithBot_injective
  simp

@[simp] theorem toReal_ofReal (x : ℝ) (hx : ofReal x ≠ 0) : (ofReal x).toReal hx = x := by
  apply ofReal_injective
  rw [ofReal_toReal]

@[simp] theorem ofReal_ne_zero (x : ℝ) : ofReal x ≠ 0 := by
  rw [ne_zero_iff_toWithBot_ne_bot]
  simp

@[simp] theorem ofReal_add (x y : ℝ) : ofReal (x + y) = ofReal x * ofReal y := rfl

@[simp] theorem ofReal_max (x y : ℝ) : ofReal (max x y) = ofReal x + ofReal y := rfl

theorem toWithBot_sum {ι : Type*} [Fintype ι] (f : ι → RMax) :
    toWithBot (∑ i, f i) = Finset.univ.sup (toWithBot ∘ f) := by
  change OrderDual.ofDual (Tropical.untrop (∑ i, f i)) = _
  rw [Finset.untrop_sum']
  rfl

end RMax

namespace Matrix

variable {ι : Type*} [Fintype ι]

/-- The support graph uses the convention `j → i` iff the `(i,j)` coefficient is finite. -/
def HasEdge (A : Matrix ι ι RMax) (j i : ι) : Prop :=
  A i j ≠ 0

/-- Every row has a finite coefficient. -/
def HasNonzeroRows (A : Matrix ι ι RMax) : Prop :=
  ∀ i, ∃ j, A.HasEdge j i

noncomputable def incoming (A : Matrix ι ι RMax) (i : ι) : Finset ι :=
  by
    classical
    exact Finset.univ.filter fun j ↦ A.HasEdge j i

theorem incoming_nonempty (A : Matrix ι ι RMax) (hrow : A.HasNonzeroRows) (i : ι) :
    (incoming A i).Nonempty := by
  classical
  obtain ⟨j, hj⟩ := hrow i
  exact ⟨j, by simp [incoming, hj]⟩

/-- The real weight of an edge.  The value away from the support is irrelevant. -/
noncomputable def edgeWeight (A : Matrix ι ι RMax) (j i : ι) : ℝ :=
  by
    classical
    exact if h : A.HasEdge j i then (A i j).toReal h else 0

theorem edgeWeight_of_edge (A : Matrix ι ι RMax) {j i : ι} (h : A.HasEdge j i) :
    A.edgeWeight j i = (A i j).toReal h := by
  simp [edgeWeight, h]

/-- The total max-plus product, interpreted in `ℝ ∪ {-∞}`. -/
def maxPlusMulVecSemantic (A : Matrix ι ι RMax) (v : ι → ℝ) (i : ι) : WithBot ℝ :=
  Finset.univ.sup fun j ↦ (A i j).toWithBot + (v j : WithBot ℝ)

/-- The max-plus product on real vectors, for a matrix with nonempty rows. -/
noncomputable def maxPlusMulVecReal (A : Matrix ι ι RMax) (hrow : A.HasNonzeroRows)
    (v : ι → ℝ) (i : ι) : ℝ :=
  (incoming A i).sup' (incoming_nonempty A hrow i)
    fun j ↦ A.edgeWeight j i + v j

/-- A finite max-plus eigenpair. -/
def IsMaxPlusRealEigenpair (A : Matrix ι ι RMax) (hrow : A.HasNonzeroRows)
    (lam : ℝ) (v : ι → ℝ) : Prop :=
  A.maxPlusMulVecReal hrow v = fun i ↦ lam + v i

theorem le_maxPlusMulVecReal (A : Matrix ι ι RMax) (hrow : A.HasNonzeroRows)
    (v : ι → ℝ) {i j : ι} (hji : A.HasEdge j i) :
    (A i j).toReal hji + v j ≤ A.maxPlusMulVecReal hrow v i := by
  rw [← A.edgeWeight_of_edge hji]
  unfold maxPlusMulVecReal
  classical
  exact Finset.le_sup' (fun k ↦ A.edgeWeight k i + v k) (by simp [incoming, hji])

theorem maxPlusMulVecReal_le (A : Matrix ι ι RMax) (hrow : A.HasNonzeroRows)
    (v : ι → ℝ) {i : ι} {b : ℝ}
    (h : ∀ j, (hji : A.HasEdge j i) → (A i j).toReal hji + v j ≤ b) :
    A.maxPlusMulVecReal hrow v i ≤ b := by
  unfold maxPlusMulVecReal
  apply Finset.sup'_le
  intro j hj
  classical
  have hji : A.HasEdge j i := by simpa [incoming] using hj
  rw [A.edgeWeight_of_edge hji]
  exact h j hji

theorem maxPlusMulVecReal_monotone (A : Matrix ι ι RMax) (hrow : A.HasNonzeroRows)
    {u v : ι → ℝ} (huv : ∀ i, u i ≤ v i) :
    ∀ i, A.maxPlusMulVecReal hrow u i ≤ A.maxPlusMulVecReal hrow v i := by
  intro i
  apply maxPlusMulVecReal_le
  intro j hji
  have hj := add_le_add_left (huv j) ((A i j).toReal hji)
  have hj' : (A i j).toReal hji + u j ≤ (A i j).toReal hji + v j := by
    simpa [add_comm] using hj
  exact hj'.trans (le_maxPlusMulVecReal A hrow v hji)

theorem maxPlusMulVecReal_add_const (A : Matrix ι ι RMax) (hrow : A.HasNonzeroRows)
    (v : ι → ℝ) (c : ℝ) :
    A.maxPlusMulVecReal hrow (fun i ↦ v i + c) =
      fun i ↦ A.maxPlusMulVecReal hrow v i + c := by
  funext i
  simpa only [maxPlusMulVecReal, add_assoc] using
    (Finset.sup'_add (incoming A i) (fun j ↦ A.edgeWeight j i + v j) c
      (incoming_nonempty A hrow i)).symm

theorem maxPlusMulVecSemantic_eq_coe (A : Matrix ι ι RMax) (hrow : A.HasNonzeroRows)
    (v : ι → ℝ) (i : ι) :
    A.maxPlusMulVecSemantic v i = (A.maxPlusMulVecReal hrow v i : WithBot ℝ) := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro j _
    by_cases hji : A.HasEdge j i
    · rw [← RMax.coe_toReal (A i j) hji]
      exact_mod_cast A.le_maxPlusMulVecReal hrow v hji
    · have hz : A i j = 0 := by simpa only [HasEdge, not_not] using hji
      simp [hz]
  · obtain ⟨j, hjmem, hj⟩ := Finset.exists_mem_eq_sup' (incoming_nonempty A hrow i)
      fun j ↦ A.edgeWeight j i + v j
    have hji : A.HasEdge j i := by simpa [incoming] using hjmem
    calc
      (A.maxPlusMulVecReal hrow v i : WithBot ℝ) =
          (A.edgeWeight j i + v j : ℝ) := by rw [maxPlusMulVecReal, hj]
      _ = (A i j).toWithBot + (v j : WithBot ℝ) := by
        rw [A.edgeWeight_of_edge hji, WithBot.coe_add]
        exact congrArg (fun x : WithBot ℝ ↦ x + (v j : WithBot ℝ))
          (RMax.coe_toReal (A i j) hji)
      _ ≤ A.maxPlusMulVecSemantic v i :=
        Finset.le_sup (s := Finset.univ)
          (f := fun k ↦ (A i k).toWithBot + (v k : WithBot ℝ)) (Finset.mem_univ j)

theorem mulVec_ofReal (A : Matrix ι ι RMax) (hrow : A.HasNonzeroRows) (v : ι → ℝ) :
    A *ᵥ (fun j ↦ RMax.ofReal (v j)) =
      fun i ↦ RMax.ofReal (A.maxPlusMulVecReal hrow v i) := by
  funext i
  apply RMax.toWithBot_injective
  change RMax.toWithBot (∑ j, A i j * RMax.ofReal (v j)) = _
  rw [RMax.toWithBot_sum]
  simp only [Function.comp_apply, RMax.toWithBot_mul, RMax.toWithBot_ofReal]
  exact A.maxPlusMulVecSemantic_eq_coe hrow v i

theorem isMaxPlusEigenpair_of_isMaxPlusRealEigenpair (A : Matrix ι ι RMax)
    (hrow : A.HasNonzeroRows) {lam : ℝ} {v : ι → ℝ}
    (h : A.IsMaxPlusRealEigenpair hrow lam v) :
    A *ᵥ (fun i ↦ RMax.ofReal (v i)) =
      fun i ↦ RMax.ofReal lam * RMax.ofReal (v i) := by
  rw [A.mulVec_ofReal hrow v, h]
  funext i
  simp [RMax.ofReal_add]

theorem realEigenvalue_le [Nonempty ι] (A : Matrix ι ι RMax) (hrow : A.HasNonzeroRows)
    {lam mu : ℝ} {u v : ι → ℝ}
    (hlam : A.IsMaxPlusRealEigenpair hrow lam u)
    (hmu : A.IsMaxPlusRealEigenpair hrow mu v) : lam ≤ mu := by
  let c := Finset.univ.sup' Finset.univ_nonempty fun i ↦ u i - v i
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun i ↦ u i - v i
  have huv : ∀ j, u j ≤ v j + c := by
    intro j
    rw [show c = u i - v i by exact hi]
    linarith [Finset.le_sup' (fun k ↦ u k - v k) (Finset.mem_univ j)]
  have hprod := A.maxPlusMulVecReal_monotone hrow huv i
  rw [hlam] at hprod
  rw [A.maxPlusMulVecReal_add_const hrow v c] at hprod
  rw [hmu] at hprod
  change lam + u i ≤ mu + v i + c at hprod
  rw [show c = u i - v i by exact hi] at hprod
  linarith

theorem realEigenvalue_unique [Nonempty ι] (A : Matrix ι ι RMax) (hrow : A.HasNonzeroRows)
    {lam mu : ℝ} {u v : ι → ℝ}
    (hlam : A.IsMaxPlusRealEigenpair hrow lam u)
    (hmu : A.IsMaxPlusRealEigenpair hrow mu v) : lam = mu :=
  le_antisymm (A.realEigenvalue_le hrow hlam hmu) (A.realEigenvalue_le hrow hmu hlam)

end Matrix
