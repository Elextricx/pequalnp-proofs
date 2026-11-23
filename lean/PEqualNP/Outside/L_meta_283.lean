import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_283

def c283 : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates :=
      [ ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩
      , ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩
      , ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩
      , ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 8]⟩
      , ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩
      , ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 9]⟩
      , ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩
      , ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 9]⟩
      , ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 13]⟩
      ]
  , output := 14 }

def edges283 : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4)]

def rhs283 (b0 b1 b2 b3 b4 b5 : Bool) : Bool :=
  (b0 && b2) || (b0 && b3) || (b0 && b4) || (b0 && b5) ||
  (b1 && b2) || (b1 && b3) || (b1 && b4) || (b1 && b5) ||
  (b2 && b3) || (b2 && b5) || (b3 && b4)

lemma mono2 : PEqualNP.MetaComplexity.Monotone2 c283 := by
  intro g hg
  simp only [c283, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp, by decide⟩

lemma and_count :
    ∃ A : Finset ℕ, A.card ≤ 2 ∧
      ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        c283.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A := by
  refine ⟨{3, 8}, by decide, ?_⟩
  intro j g hj hop
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  · simp [c283] at hj; subst hj; cases hop
  · simp [c283] at hj; subst hj; cases hop
  · simp [c283] at hj; subst hj; cases hop
  · decide
  · simp [c283] at hj; subst hj; cases hop
  · simp [c283] at hj; subst hj; cases hop
  · simp [c283] at hj; subst hj; cases hop
  · simp [c283] at hj; subst hj; cases hop
  · decide
  · simp [c283] at hj

lemma ofFn6 (x : Fin 6 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
  simp [List.ofFn_succ]

lemma eval_eq_rhs (b0 b1 b2 b3 b4 b5 : Bool) :
    c283.eval [b0, b1, b2, b3, b4, b5] = rhs283 b0 b1 b2 b3 b4 b5 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> rfl

lemma rhs_iff (x : Fin 6 → Bool) :
    rhs283 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) = true ↔
      ∃ u v : Fin 6, (u.val, v.val) ∈ edges283 ∧ x u = true ∧ x v = true := by
  constructor
  · intro h
    simp only [rhs283, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
    · exact ⟨0, 2, by decide, h.1, h.2⟩
    · exact ⟨0, 3, by decide, h.1, h.2⟩
    · exact ⟨0, 4, by decide, h.1, h.2⟩
    · exact ⟨0, 5, by decide, h.1, h.2⟩
    · exact ⟨1, 2, by decide, h.1, h.2⟩
    · exact ⟨1, 3, by decide, h.1, h.2⟩
    · exact ⟨1, 4, by decide, h.1, h.2⟩
    · exact ⟨1, 5, by decide, h.1, h.2⟩
    · exact ⟨2, 3, by decide, h.1, h.2⟩
    · exact ⟨2, 5, by decide, h.1, h.2⟩
    · exact ⟨3, 4, by decide, h.1, h.2⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    simp only [edges283, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at huv
    rcases huv with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : u = 0 := Fin.ext h1; have : v = 2 := Fin.ext h2; subst_vars; simp [rhs283, hu, hv]
    · have : u = 0 := Fin.ext h1; have : v = 3 := Fin.ext h2; subst_vars; simp [rhs283, hu, hv]
    · have : u = 0 := Fin.ext h1; have : v = 4 := Fin.ext h2; subst_vars; simp [rhs283, hu, hv]
    · have : u = 0 := Fin.ext h1; have : v = 5 := Fin.ext h2; subst_vars; simp [rhs283, hu, hv]
    · have : u = 1 := Fin.ext h1; have : v = 2 := Fin.ext h2; subst_vars; simp [rhs283, hu, hv]
    · have : u = 1 := Fin.ext h1; have : v = 3 := Fin.ext h2; subst_vars; simp [rhs283, hu, hv]
    · have : u = 1 := Fin.ext h1; have : v = 4 := Fin.ext h2; subst_vars; simp [rhs283, hu, hv]
    · have : u = 1 := Fin.ext h1; have : v = 5 := Fin.ext h2; subst_vars; simp [rhs283, hu, hv]
    · have : u = 2 := Fin.ext h1; have : v = 3 := Fin.ext h2; subst_vars; simp [rhs283, hu, hv]
    · have : u = 2 := Fin.ext h1; have : v = 5 := Fin.ext h2; subst_vars; simp [rhs283, hu, hv]
    · have : u = 3 := Fin.ext h1; have : v = 4 := Fin.ext h2; subst_vars; simp [rhs283, hu, hv]

lemma eval_iff (x : Fin 6 → Bool) :
    c283.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 6, (u.val, v.val) ∈ edges283 ∧ x u = true ∧ x v = true := by
  rw [ofFn6, eval_eq_rhs, rhs_iff]

end PEqualNP.Outside.L_meta_283

theorem PEqualNP.Outside.L_meta_283 :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 13]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) → (PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 2 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)) ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C hC
  subst hC
  exact ⟨⟨PEqualNP.Outside.L_meta_283.mono2, PEqualNP.Outside.L_meta_283.and_count⟩,
    PEqualNP.Outside.L_meta_283.eval_iff⟩
