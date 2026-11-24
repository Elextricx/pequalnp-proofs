import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2051

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wireVal {N : ℕ} (D : Circuit) (y : Fin (N + N) → Bool) (w : ℕ) : Bool :=
  (D.wires (List.ofFn y)).getD w false

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g)]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl step w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval
        ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
          if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by simp [step]
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) := by
        simp [step, List.getD_eq_getElem?_getD]
      rw [hself]
      change g0.op.eval _ = g0.op.eval _
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by simp [step]; omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp only [hi, ↓reduceIte]
        rw [List.getD_eq_default _ _ (by omega)]
    | succ j' =>
      have hj' : j' < gs.length := by simp at hj; omega
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by simp [step]; omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj'

lemma wireVal_input {N : ℕ} (D : Circuit) (y : Fin (N + N) → Bool) (w : ℕ) (hw : w < N + N) :
    wireVal D y w = y ⟨w, hw⟩ := by
  change (D.gates.foldl step (List.ofFn y)).getD w false = y ⟨w, hw⟩
  rw [foldl_step_getD_lt D.gates (List.ofFn y) w (by simp [hw])]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma wireVal_oob {N : ℕ} (D : Circuit) (y : Fin (N + N) → Bool) (w : ℕ)
    (hw : N + N + D.gates.length ≤ w) : wireVal D y w = false := by
  change (D.gates.foldl step (List.ofFn y)).getD w false = false
  apply List.getD_eq_default
  rw [foldl_step_len]
  simp only [List.length_ofFn]
  exact hw

lemma wireVal_gate_rb {N : ℕ} (D : Circuit) (hrb : ReadsBack (N + N) D)
    (y : Fin (N + N) → Bool) (j : ℕ) (hj : j < D.gates.length) :
    wireVal D y (N + N + j) =
      (gateAt D j).op.eval ((gateAt D j).inputs.map (wireVal D y)) := by
  have h := foldl_step_gate D.gates (List.ofFn y) j hj
  simp only [List.length_ofFn] at h
  change (D.gates.foldl step (List.ofFn y)).getD (N + N + j) false = _
  rw [h]
  congr 1
  apply List.map_congr_left
  intro u hu
  have hlt : u < N + N + j := hrb j hj u hu
  simp only [hlt, ↓reduceIte]
  rfl

def ptIn {N : ℕ} (p : Fin N) : Fin (N + N) → Bool :=
  fun k => decide (k = Fin.castAdd N p)

def lnIn {N : ℕ} (l : Fin N) : Fin (N + N) → Bool :=
  fun k => decide (k = Fin.natAdd N l)

def pairIn {N : ℕ} (p l : Fin N) : Fin (N + N) → Bool :=
  fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)

def ptSup {N : ℕ} (D : Circuit) (w : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun p => wireVal D (ptIn p) w = true

def lnSup {N : ℕ} (D : Circuit) (w : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun l => wireVal D (lnIn l) w = true

lemma ptSup_input {N : ℕ} (D : Circuit) (w : ℕ) (hw : w < N) :
    ptSup D w = {⟨w, hw⟩} := by
  ext p
  simp only [ptSup, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [wireVal_input D (ptIn p) w (by omega)]
  simp only [ptIn, decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd]
  exact eq_comm

lemma lnSup_input {N : ℕ} (D : Circuit) (w : ℕ) (hw1 : N ≤ w) (hw2 : w < N + N) :
    lnSup (N := N) D w = ({⟨w - N, by omega⟩} : Finset (Fin N)) := by
  ext l
  simp only [lnSup, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [wireVal_input D (lnIn l) w hw2]
  simp only [lnIn, decide_eq_true_eq, Fin.ext_iff, Fin.val_natAdd]
  constructor <;> intro h <;> omega

lemma wireVal_of_mem_P {N : ℕ} (D : Circuit) (P : Finset ℕ) (hrb : ReadsBack (N + N) D)
    (hP : ∀ w ∈ P, w < N ∨ ∃ i < D.gates.length, w = N + N + i ∧
      (gateAt D i).op = GateOp.or ∧ ∀ u ∈ (gateAt D i).inputs, u ∈ P) :
    ∀ w ∈ P, ∀ y : Fin (N + N) → Bool,
      wireVal D y w = true ↔ ∃ p ∈ ptSup D w, y (Fin.castAdd N p) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw y
    rcases hP w hw with hwlt | ⟨i, hi, rfl, hop, hsub⟩
    · rw [ptSup_input D w hwlt, wireVal_input D y w (by omega)]
      simp only [Finset.mem_singleton, exists_eq_left]
      rfl
    · have hgate (z : Fin (N + N) → Bool) :
          wireVal D z (N + N + i) = true ↔ ∃ u ∈ (gateAt D i).inputs, wireVal D z u = true := by
        rw [wireVal_gate_rb D hrb z i hi, hop]
        change ((gateAt D i).inputs.map (wireVal D z)).any id = true ↔ _
        simp [List.any_eq_true]
      have hsup (p : Fin N) :
          p ∈ ptSup D (N + N + i) ↔ ∃ u ∈ (gateAt D i).inputs, p ∈ ptSup D u := by
        simp only [ptSup, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hgate (ptIn p)
      rw [hgate y]
      constructor
      · rintro ⟨u, hu, hvu⟩
        obtain ⟨p, hp, hyp⟩ := (ih u (hrb i hi u hu) (hsub u hu) y).mp hvu
        exact ⟨p, (hsup p).mpr ⟨u, hu, hp⟩, hyp⟩
      · rintro ⟨p, hp, hyp⟩
        obtain ⟨u, hu, hpu⟩ := (hsup p).mp hp
        exact ⟨u, hu, (ih u (hrb i hi u hu) (hsub u hu) y).mpr ⟨p, hpu, hyp⟩⟩

lemma wireVal_of_mem_L {N : ℕ} (D : Circuit) (L : Finset ℕ) (hrb : ReadsBack (N + N) D)
    (hL : ∀ w ∈ L, (N ≤ w ∧ w < N + N) ∨ ∃ i < D.gates.length, w = N + N + i ∧
      (gateAt D i).op = GateOp.or ∧ ∀ u ∈ (gateAt D i).inputs, u ∈ L) :
    ∀ w ∈ L, ∀ y : Fin (N + N) → Bool,
      wireVal D y w = true ↔ ∃ l ∈ lnSup D w, y (Fin.natAdd N l) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw y
    rcases hL w hw with ⟨hw1, hw2⟩ | ⟨i, hi, rfl, hop, hsub⟩
    · rw [lnSup_input D w hw1 hw2, wireVal_input D y w hw2]
      simp only [Finset.mem_singleton, exists_eq_left]
      have heq : (⟨w, hw2⟩ : Fin (N + N)) = Fin.natAdd N ⟨w - N, by omega⟩ := by
        apply Fin.ext; simp only [Fin.val_natAdd]; omega
      rw [heq]
    · have hgate (z : Fin (N + N) → Bool) :
          wireVal D z (N + N + i) = true ↔ ∃ u ∈ (gateAt D i).inputs, wireVal D z u = true := by
        rw [wireVal_gate_rb D hrb z i hi, hop]
        change ((gateAt D i).inputs.map (wireVal D z)).any id = true ↔ _
        simp [List.any_eq_true]
      have hsup (l : Fin N) :
          l ∈ lnSup D (N + N + i) ↔ ∃ u ∈ (gateAt D i).inputs, l ∈ lnSup D u := by
        simp only [lnSup, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hgate (lnIn l)
      rw [hgate y]
      constructor
      · rintro ⟨u, hu, hvu⟩
        obtain ⟨l, hl, hyl⟩ := (ih u (hrb i hi u hu) (hsub u hu) y).mp hvu
        exact ⟨l, (hsup l).mpr ⟨u, hu, hl⟩, hyl⟩
      · rintro ⟨l, hl, hyl⟩
        obtain ⟨u, hu, hlu⟩ := (hsup l).mp hl
        exact ⟨u, hu, (ih u (hrb i hi u hu) (hsub u hu) y).mpr ⟨l, hlu, hyl⟩⟩

lemma ptSup_gate_P {N : ℕ} (D : Circuit) (P : Finset ℕ) (hrb : ReadsBack (N + N) D)
    (hP : ∀ w ∈ P, w < N ∨ ∃ i < D.gates.length, w = N + N + i ∧
      (gateAt D i).op = GateOp.or ∧ ∀ u ∈ (gateAt D i).inputs, u ∈ P)
    (j : ℕ) (hj : j < D.gates.length) (hmem : N + N + j ∈ P) :
    ptSup (N := N) D (N + N + j) = (gateAt D j).inputs.toFinset.biUnion (ptSup (N := N) D) := by
  have hop : (gateAt D j).op = GateOp.or := by
    rcases hP (N + N + j) hmem with hlt | ⟨i, _, heq, hop, _⟩
    · omega
    · have : i = j := by omega
      subst this; exact hop
  ext p
  simp only [ptSup, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, List.mem_toFinset]
  rw [wireVal_gate_rb D hrb (ptIn p) j hj, hop]
  change ((gateAt D j).inputs.map (wireVal D (ptIn p))).any id = true ↔ _
  simp [List.any_eq_true]

lemma lnSup_gate_L {N : ℕ} (D : Circuit) (L : Finset ℕ) (hrb : ReadsBack (N + N) D)
    (hL : ∀ w ∈ L, (N ≤ w ∧ w < N + N) ∨ ∃ i < D.gates.length, w = N + N + i ∧
      (gateAt D i).op = GateOp.or ∧ ∀ u ∈ (gateAt D i).inputs, u ∈ L)
    (j : ℕ) (hj : j < D.gates.length) (hmem : N + N + j ∈ L) :
    lnSup (N := N) D (N + N + j) = (gateAt D j).inputs.toFinset.biUnion (lnSup (N := N) D) := by
  have hop : (gateAt D j).op = GateOp.or := by
    rcases hL (N + N + j) hmem with ⟨_, hlt⟩ | ⟨i, _, heq, hop, _⟩
    · omega
    · have : i = j := by omega
      subst this; exact hop
  ext l
  simp only [lnSup, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, List.mem_toFinset]
  rw [wireVal_gate_rb D hrb (lnIn l) j hj, hop]
  change ((gateAt D j).inputs.map (wireVal D (lnIn l))).any id = true ↔ _
  simp [List.any_eq_true]

lemma ptSup_eq_empty_of_mem_L {N : ℕ} (D : Circuit) (L : Finset ℕ) (hrb : ReadsBack (N + N) D)
    (hL : ∀ w ∈ L, (N ≤ w ∧ w < N + N) ∨ ∃ i < D.gates.length, w = N + N + i ∧
      (gateAt D i).op = GateOp.or ∧ ∀ u ∈ (gateAt D i).inputs, u ∈ L)
    (w : ℕ) (hw : w ∈ L) : ptSup (N := N) D w = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p hp
  have hv : wireVal D (ptIn p) w = true := (Finset.mem_filter.mp hp).2
  obtain ⟨l, _, hl⟩ := (wireVal_of_mem_L D L hrb hL w hw (ptIn p)).mp hv
  simp only [ptIn, decide_eq_true_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at hl
  omega

def orDecomp (D : Circuit) (N : ℕ) : ℕ → ℕ → Finset (Fin (N + N)) × Finset ℕ
  | 0, _ => (∅, ∅)
  | fuel + 1, w =>
    if h1 : w < N + N then
      ({⟨w, h1⟩}, ∅)
    else if w - (N + N) < D.gates.length then
      let j := w - (N + N)
      match (gateAt D j).op with
      | GateOp.and => (∅, {j})
      | GateOp.or =>
        ((gateAt D j).inputs.toFinset.biUnion (fun u => (orDecomp D N fuel u).1),
         (gateAt D j).inputs.toFinset.biUnion (fun u => (orDecomp D N fuel u).2))
      | _ => (∅, ∅)
    else (∅, ∅)

lemma orDecomp_spec {N : ℕ} (D : Circuit) (hmono : Monotone2 D) (hrb : ReadsBack (N + N) D) :
    ∀ (fuel w : ℕ), w < fuel →
      (∀ i ∈ (orDecomp D N fuel w).2, i < D.gates.length ∧ (gateAt D i).op = GateOp.and) ∧
      (∀ y : Fin (N + N) → Bool,
        wireVal D y w = true ↔
          (∃ v ∈ (orDecomp D N fuel w).1, y v = true) ∨
          (∃ i ∈ (orDecomp D N fuel w).2, wireVal D y (N + N + i) = true)) := by
  intro fuel
  induction fuel with
  | zero => intro w hw; omega
  | succ fuel ih =>
    intro w hw
    simp only [orDecomp]
    split_ifs with h1 h2
    · refine ⟨by simp, fun y => ?_⟩
      rw [wireVal_input D y w h1]
      simp
    · set j := w - (N + N)
      have hwj : w = N + N + j := by omega
      have hgop : (gateAt D j).op = GateOp.and ∨ (gateAt D j).op = GateOp.or := by
        have hgmem : gateAt D j ∈ D.gates := by
          simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
          exact List.getElem_mem h2
        simpa using (hmono _ hgmem).1
      rcases hgop with hop | hop
      · rw [hop]
        refine ⟨?_, fun y => ?_⟩
        · intro i hi
          simp only [Finset.mem_singleton] at hi
          subst hi; exact ⟨h2, hop⟩
        · simp only [Finset.notMem_empty, false_and, exists_false, false_or,
            Finset.mem_singleton, exists_eq_left]
          rw [hwj]
      · rw [hop]
        refine ⟨?_, fun y => ?_⟩
        · intro i hi
          simp only [Finset.mem_biUnion, List.mem_toFinset] at hi
          obtain ⟨u, hu, hui⟩ := hi
          have hult : u < fuel := by have := hrb j h2 u hu; omega
          exact (ih u hult).1 i hui
        · rw [hwj, wireVal_gate_rb D hrb y j h2, hop]
          change ((gateAt D j).inputs.map (wireVal D y)).any id = true ↔ _
          simp only [List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and,
            Finset.mem_biUnion, List.mem_toFinset]
          constructor
          · rintro ⟨u, hu, hvu⟩
            have hult : u < fuel := by have := hrb j h2 u hu; omega
            rcases (ih u hult).2 y |>.mp hvu with ⟨v, hv, hyv⟩ | ⟨i, hi, hvi⟩
            · exact Or.inl ⟨v, ⟨u, hu, hv⟩, hyv⟩
            · exact Or.inr ⟨i, ⟨u, hu, hi⟩, hvi⟩
          · rintro (⟨v, ⟨u, hu, hv⟩, hyv⟩ | ⟨i, ⟨u, hu, hi⟩, hvi⟩)
            · have hult : u < fuel := by have := hrb j h2 u hu; omega
              exact ⟨u, hu, (ih u hult).2 y |>.mpr (Or.inl ⟨v, hv, hyv⟩)⟩
            · have hult : u < fuel := by have := hrb j h2 u hu; omega
              exact ⟨u, hu, (ih u hult).2 y |>.mpr (Or.inr ⟨i, hi, hvi⟩)⟩
    · refine ⟨by simp, fun y => ?_⟩
      rw [wireVal_oob D y w (by omega)]
      simp

def coneS (D : Circuit) (N : ℕ) : ℕ → ℕ → Finset ℕ
  | 0, _ => ∅
  | fuel + 1, w =>
    insert w
      (if N + N ≤ w ∧ w - (N + N) < D.gates.length then
        (gateAt D (w - (N + N))).inputs.toFinset.biUnion (coneS D N fuel)
      else ∅)

lemma mem_coneS_self (D : Circuit) (N fuel w : ℕ) (hf : 0 < fuel) : w ∈ coneS D N fuel w := by
  cases fuel with
  | zero => omega
  | succ fuel => simp [coneS]

lemma coneS_step_mem (D : Circuit) (N fuel w u : ℕ) (h1 : N + N ≤ w)
    (h2 : w - (N + N) < D.gates.length) (hu : u ∈ (gateAt D (w - (N + N))).inputs)
    (z : ℕ) (hz : z ∈ coneS D N fuel u) : z ∈ coneS D N (fuel + 1) w := by
  simp only [coneS, Finset.mem_insert, h1, h2, and_self, ↓reduceIte, Finset.mem_biUnion, List.mem_toFinset]
  exact Or.inr ⟨u, hu, hz⟩

lemma coneS_mono (D : Circuit) (N : ℕ) : ∀ {f1 f2 w : ℕ}, f1 ≤ f2 →
    coneS D N f1 w ⊆ coneS D N f2 w := by
  intro f1
  induction f1 with
  | zero => intro f2 w _; simp [coneS]
  | succ f1 ih =>
    intro f2 w hle
    cases f2 with
    | zero => omega
    | succ f2 =>
      intro z hz
      simp only [coneS, Finset.mem_insert] at hz ⊢
      rcases hz with rfl | hz
      · exact Or.inl rfl
      · right
        split_ifs at hz ⊢ with h
        · simp only [Finset.mem_biUnion, List.mem_toFinset] at hz ⊢
          obtain ⟨u, hu, hzu⟩ := hz
          exact ⟨u, hu, ih (by omega) hzu⟩
        · simp at hz

lemma coneS_props {N : ℕ} (D : Circuit) (S : Finset ℕ) (sup : ℕ → Finset (Fin N))
    (_hrb : ReadsBack (N + N) D)
    (hS : ∀ w ∈ S, w < N + N ∨ ∃ j < D.gates.length, w = N + N + j ∧
      (gateAt D j).op = GateOp.or ∧ ∀ u ∈ (gateAt D j).inputs, u ∈ S)
    (hsup_gate : ∀ j < D.gates.length, N + N + j ∈ S →
      sup (N + N + j) = (gateAt D j).inputs.toFinset.biUnion sup) :
    ∀ (fuel w : ℕ), w ∈ S → ∀ z ∈ coneS D N fuel w, z ∈ S ∧ sup z ⊆ sup w := by
  intro fuel
  induction fuel with
  | zero => intro w _ z hz; simp [coneS] at hz
  | succ fuel ih =>
    intro w hw z hz
    simp only [coneS, Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact ⟨hw, Finset.Subset.refl _⟩
    · split_ifs at hz with h
      · simp only [Finset.mem_biUnion, List.mem_toFinset] at hz
        obtain ⟨u, hu, hzu⟩ := hz
        set j := w - (N + N)
        have hwj : w = N + N + j := by omega
        have hsub : ∀ v ∈ (gateAt D j).inputs, v ∈ S := by
          rcases hS w hw with hlt | ⟨i, _, heq, _, hsub⟩
          · omega
          · have : i = j := by omega
            subst this; exact hsub
        obtain ⟨hzS, hzsup⟩ := ih u (hsub u hu) z hzu
        refine ⟨hzS, Finset.Subset.trans hzsup ?_⟩
        rw [hwj, hsup_gate j h.2 (hwj ▸ hw)]
        intro a ha
        exact Finset.mem_biUnion.mpr ⟨u, List.mem_toFinset.mpr hu, ha⟩
      · simp at hz

lemma coneS_parent {N : ℕ} (D : Circuit) (_hrb : ReadsBack (N + N) D) :
    ∀ (fuel w z : ℕ), z ∈ coneS D N fuel w → z ≠ w →
      ∃ m < D.gates.length, N + N + m ∈ coneS D N fuel w ∧ z ∈ (gateAt D m).inputs := by
  intro fuel
  induction fuel with
  | zero => intro w z hz; simp [coneS] at hz
  | succ fuel ih =>
    intro w z hz hne
    simp only [coneS, Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact absurd rfl hne
    · split_ifs at hz with h
      · simp only [Finset.mem_biUnion, List.mem_toFinset] at hz
        obtain ⟨u, hu, hzu⟩ := hz
        by_cases hzu_eq : z = u
        · subst hzu_eq
          refine ⟨w - (N + N), h.2, ?_, hu⟩
          have hwj : N + N + (w - (N + N)) = w := by omega
          rw [hwj]
          exact mem_coneS_self D N (fuel + 1) w (by omega)
        · obtain ⟨m, hm, hmc, hzm⟩ := ih u z hzu hzu_eq
          exact ⟨m, hm, coneS_step_mem D N fuel w u h.1 h.2 hu _ hmc, hzm⟩
      · simp at hz

lemma coneS_closed {N : ℕ} (D : Circuit) (hrb : ReadsBack (N + N) D) :
    ∀ (fuel w z : ℕ), w < fuel → z ∈ coneS D N fuel w →
      ∀ (j : ℕ), z = N + N + j → j < D.gates.length →
      ∀ u ∈ (gateAt D j).inputs, u ∈ coneS D N fuel w := by
  intro fuel
  induction fuel with
  | zero => intro w _ hw; omega
  | succ fuel ih =>
    intro w z hw hz j hzj hj u hu
    simp only [coneS, Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · rw [hzj]
      have h1 : N + N ≤ N + N + j := by omega
      have h2 : N + N + j - (N + N) < D.gates.length := by omega
      have hu' : u ∈ (gateAt D (N + N + j - (N + N))).inputs := by
        simpa [Nat.add_sub_cancel_left] using hu
      have hult : u < fuel := by have := hrb j hj u hu; omega
      exact coneS_step_mem D N fuel (N + N + j) u h1 h2 hu' u (mem_coneS_self D N fuel u (by omega))
    · split_ifs at hz with h
      · simp only [Finset.mem_biUnion, List.mem_toFinset] at hz
        obtain ⟨v, hv, hzv⟩ := hz
        have hvlt : v < fuel := by
          have := hrb (w - (N + N)) h.2 v hv
          omega
        exact coneS_step_mem D N fuel w v h.1 h.2 hv u (ih v z hvlt hzv j hzj hj u hu)
      · simp at hz

lemma cone_bound {N : ℕ} (D : Circuit) (S : Finset ℕ) (sup : ℕ → Finset (Fin N))
    (hmono : Monotone2 D) (hrb : ReadsBack (N + N) D)
    (hS : ∀ w ∈ S, w < N + N ∨ ∃ j < D.gates.length, w = N + N + j ∧
      (gateAt D j).op = GateOp.or ∧ ∀ u ∈ (gateAt D j).inputs, u ∈ S)
    (hsup_inp : ∀ w ∈ S, w < N + N → (sup w).card ≤ 1)
    (hsup_gate : ∀ j < D.gates.length, N + N + j ∈ S →
      sup (N + N + j) = (gateAt D j).inputs.toFinset.biUnion sup)
    (Rs : Finset ℕ) (wire : ℕ → ℕ)
    (hRs : ∀ i ∈ Rs, wire i ∈ S ∧ (sup (wire i)).Nonempty) :
    let fuel := N + N + D.gates.length + 1
    let Cw := Rs.biUnion (fun i => coneS D N fuel (wire i))
    let Gor := (Finset.range D.gates.length).filter (fun j => N + N + j ∈ Cw ∧ 2 ≤ (sup (N + N + j)).card)
    let Ecov := Rs.biUnion (fun i => sup (wire i))
    Ecov.card ≤ Rs.card + Gor.card := by
  intro fuel Cw Gor Ecov
  let phi : ℕ → Option (Fin N ⊕ ℕ) := fun w =>
    if h : (sup w).Nonempty then
      if (sup w).card = 1 then some (Sum.inl ((sup w).min' h))
      else some (Sum.inr (w - (N + N)))
    else none
  have hphi_one (w : ℕ) (a : Fin N) (ha : sup w = {a}) : phi w = some (Sum.inl a) := by
    have hne : (sup w).Nonempty := by rw [ha]; exact Finset.singleton_nonempty a
    have hcard : (sup w).card = 1 := by rw [ha]; exact Finset.card_singleton a
    have hmin : (sup w).min' hne = a := by
      have hm : (sup w).min' hne ∈ ({a} : Finset (Fin N)) := ha ▸ Finset.min'_mem (sup w) hne
      exact Finset.mem_singleton.mp hm
    simp only [phi, hne, ↓reduceDIte, hcard, ↓reduceIte, hmin]
  have hphi_ge2 (j : ℕ) (hge : 2 ≤ (sup (N + N + j)).card) :
      phi (N + N + j) = some (Sum.inr j) := by
    have hne : (sup (N + N + j)).Nonempty := Finset.card_pos.mp (by omega)
    have hne1 : (sup (N + N + j)).card ≠ 1 := by omega
    simp only [phi, hne, ↓reduceDIte, hne1, ↓reduceIte, Nat.add_sub_cancel_left]
  let Nodes : Finset (Fin N ⊕ ℕ) := (Ecov.image Sum.inl) ∪ (Gor.image Sum.inr)
  let RootNodes : Finset (Fin N ⊕ ℕ) := Rs.biUnion (fun i => (phi (wire i)).toFinset)
  let ChildNodes : Finset (Fin N ⊕ ℕ) :=
    Gor.biUnion (fun m => ((gateAt D m).inputs.filterMap phi).toFinset)
  have hNodes_card : Nodes.card = Ecov.card + Gor.card := by
    have hdisj : Disjoint (Ecov.image (Sum.inl : Fin N → Fin N ⊕ ℕ))
        (Gor.image (Sum.inr : ℕ → Fin N ⊕ ℕ)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_image] at hx1 hx2
      rcases hx1 with ⟨_, _, rfl⟩
      rcases hx2 with ⟨_, _, h⟩
      cases h
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective]
  have hRoots_card : RootNodes.card ≤ Rs.card := by
    calc RootNodes.card
        ≤ ∑ i ∈ Rs, ((phi (wire i)).toFinset).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ Rs, 1 := Finset.sum_le_sum fun i _ => by
          cases phi (wire i) <;> simp
      _ = Rs.card := by simp
  have hChildren_card : ChildNodes.card ≤ 2 * Gor.card := by
    calc ChildNodes.card
        ≤ ∑ m ∈ Gor, (((gateAt D m).inputs.filterMap phi).toFinset).card := Finset.card_biUnion_le
      _ ≤ ∑ _m ∈ Gor, 2 := Finset.sum_le_sum fun m hm => by
          have hmlt : m < D.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
          have hgmem : gateAt D m ∈ D.gates := by
            simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmlt, Option.getD_some]
            exact List.getElem_mem hmlt
          have hlen2 : (gateAt D m).inputs.length ≤ 2 := (hmono _ hgmem).2
          calc (((gateAt D m).inputs.filterMap phi).toFinset).card
              ≤ ((gateAt D m).inputs.filterMap phi).length := List.toFinset_card_le _
            _ ≤ (gateAt D m).inputs.length := List.length_filterMap_le _ _
            _ ≤ 2 := hlen2
      _ = 2 * Gor.card := by simp [mul_comm]
  have hCw_lt (i : ℕ) (hi : i ∈ Rs) : wire i < fuel := by
    rcases hS (wire i) (hRs i hi).1 with hlt | ⟨j, hj, heq, _, _⟩ <;> omega
  -- Helper: from any w ∈ Cw with a ∈ sup w and 2 ≤ (sup w).card, descend to a gate m ∈ Gor with a child u having sup u = {a}
  have hdescend (a : Fin N) :
      ∀ w : ℕ, w ∈ Cw → a ∈ sup w → 2 ≤ (sup w).card →
        ∃ m ∈ Gor, ∃ u ∈ (gateAt D m).inputs, sup u = {a} := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hwCw ha hcard2
      obtain ⟨i, hiRs, hwcone⟩ := Finset.mem_biUnion.mp hwCw
      have hwS : w ∈ S := (coneS_props D S sup hrb hS hsup_gate fuel (wire i) (hRs i hiRs).1 w hwcone).1
      rcases hS w hwS with hlt | ⟨k, hk, hw_eq, _, _⟩
      · have := hsup_inp w hwS hlt; omega
      · have hkGor : k ∈ Gor := by
          simp only [Gor, Finset.mem_filter, Finset.mem_range]
          exact ⟨hk, hw_eq ▸ hwCw, hw_eq ▸ hcard2⟩
        have ha' : a ∈ (gateAt D k).inputs.toFinset.biUnion sup := by
          rw [← hsup_gate k hk (hw_eq ▸ hwS), ← hw_eq]; exact ha
        obtain ⟨u, hu_f, hau⟩ := Finset.mem_biUnion.mp ha'
        have hu : u ∈ (gateAt D k).inputs := List.mem_toFinset.mp hu_f
        have hult : u < w := by rw [hw_eq]; exact hrb k hk u hu
        have hucone : u ∈ coneS D N fuel (wire i) :=
          coneS_closed D hrb fuel (wire i) w (hCw_lt i hiRs) hwcone k hw_eq hk u hu
        have huCw : u ∈ Cw := Finset.mem_biUnion.mpr ⟨i, hiRs, hucone⟩
        by_cases hucard : (sup u).card = 1
        · obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hucard
          have hba : a = b := Finset.mem_singleton.mp (hb ▸ hau)
          subst hba
          exact ⟨k, hkGor, u, hu, hb⟩
        · have hupos : 0 < (sup u).card := Finset.card_pos.mpr ⟨a, hau⟩
          exact ih u hult huCw hau (by omega)
  have hsub : Nodes \ RootNodes ⊆ ChildNodes := by
    intro x hx
    obtain ⟨hxN, hxNotR⟩ := Finset.mem_sdiff.mp hx
    simp only [Nodes, Finset.mem_union, Finset.mem_image] at hxN
    rcases hxN with ⟨a, haE, rfl⟩ | ⟨j, hjG, rfl⟩
    · obtain ⟨i, hiRs, ha_sup⟩ := Finset.mem_biUnion.mp haE
      have hge2 : 2 ≤ (sup (wire i)).card := by
        by_contra hlt2
        have hpos : 0 < (sup (wire i)).card := Finset.card_pos.mpr ⟨a, ha_sup⟩
        have heq1 : (sup (wire i)).card = 1 := by omega
        obtain ⟨b, hb⟩ := Finset.card_eq_one.mp heq1
        have hba : a = b := Finset.mem_singleton.mp (hb ▸ ha_sup)
        subst hba
        apply hxNotR
        simp only [RootNodes, Finset.mem_biUnion, Option.mem_toFinset]
        exact ⟨i, hiRs, hphi_one (wire i) a hb⟩
      have hwiCw : wire i ∈ Cw :=
        Finset.mem_biUnion.mpr ⟨i, hiRs, mem_coneS_self D N fuel (wire i) (by omega)⟩
      obtain ⟨m, hmGor, u, hu, hsu⟩ := hdescend a (wire i) hwiCw ha_sup hge2
      simp only [ChildNodes, Finset.mem_biUnion, List.mem_toFinset, List.mem_filterMap]
      exact ⟨m, hmGor, u, hu, hphi_one u a hsu⟩
    · have hjlt : j < D.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hjG).1
      have hjCw : N + N + j ∈ Cw := (Finset.mem_filter.mp hjG).2.1
      have hjcard : 2 ≤ (sup (N + N + j)).card := (Finset.mem_filter.mp hjG).2.2
      obtain ⟨i, hiRs, hjcone⟩ := Finset.mem_biUnion.mp hjCw
      have hne : N + N + j ≠ wire i := by
        intro heq
        apply hxNotR
        simp only [RootNodes, Finset.mem_biUnion, Option.mem_toFinset]
        exact ⟨i, hiRs, heq ▸ hphi_ge2 j hjcard⟩
      obtain ⟨m, hmlt, hmcone, hjm⟩ := coneS_parent D hrb fuel (wire i) (N + N + j) hjcone hne
      have hmS : N + N + m ∈ S :=
        (coneS_props D S sup hrb hS hsup_gate fuel (wire i) (hRs i hiRs).1 (N + N + m) hmcone).1
      have hsup_sub : sup (N + N + j) ⊆ sup (N + N + m) := by
        rw [hsup_gate m hmlt hmS]
        intro a ha
        exact Finset.mem_biUnion.mpr ⟨N + N + j, List.mem_toFinset.mpr hjm, ha⟩
      have hmcard : 2 ≤ (sup (N + N + m)).card := le_trans hjcard (Finset.card_le_card hsup_sub)
      have hmGor : m ∈ Gor := by
        simp only [Gor, Finset.mem_filter, Finset.mem_range]
        exact ⟨hmlt, Finset.mem_biUnion.mpr ⟨i, hiRs, hmcone⟩, hmcard⟩
      simp only [ChildNodes, Finset.mem_biUnion, List.mem_toFinset, List.mem_filterMap]
      exact ⟨m, hmGor, N + N + j, hjm, hphi_ge2 j hjcard⟩
  have hsdiff := Finset.card_le_card hsub
  have hle_sdiff : Nodes.card - RootNodes.card ≤ (Nodes \ RootNodes).card := Finset.le_card_sdiff RootNodes Nodes
  omega

end PEqualNP.Outside.L_meta_2051

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_2051 in
theorem PEqualNP.Outside.L_meta_2051 :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (D : PEqualNP.CircuitLowerBounds.Circuit) (P L : Finset ℕ), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D → (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = true ↔ ∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true) → (∀ w ∈ P, w < N ∨ ∃ i < D.gates.length, w = N + N + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P) → (∀ w ∈ L, (N ≤ w ∧ w < N + N) ∨ ∃ i < D.gates.length, w = N + N + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ L) → (∀ i < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) → (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card ≤ D.size + 1 := by
  classical
  intro N I _ D P L hC4 hmono hrb hfun hP hL hAnd
  let fuelO := D.output + 1
  have hdec := orDecomp_spec D hmono hrb fuelO D.output (by omega)
  let R0 : Finset ℕ := (orDecomp D N fuelO D.output).2
  have hno_leaf : (orDecomp D N fuelO D.output).1 = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro v hv
    let y : Fin (N + N) → Bool := fun k => decide (k = v)
    have ht : wireVal D y D.output = true := (hdec.2 y).mpr (Or.inl ⟨v, hv, by simp [y]⟩)
    obtain ⟨p, l, _, hp, hl⟩ := (hfun y).mp ht
    simp only [y, decide_eq_true_eq] at hp hl
    have heq : (Fin.castAdd N p : Fin (N + N)).val = (Fin.natAdd N l : Fin (N + N)).val := by
      rw [hp, hl]
    simp only [Fin.val_castAdd, Fin.val_natAdd] at heq
    omega
  have hD_eval (y : Fin (N + N) → Bool) :
      circuitFun (N + N) D y = true ↔ ∃ i ∈ R0, wireVal D y (N + N + i) = true := by
    change wireVal D y D.output = true ↔ _
    have h1 := hdec.2 y
    rw [hno_leaf] at h1
    simpa only [Finset.notMem_empty, false_and, exists_false, false_or] using h1
  let pWire (i : ℕ) : ℕ :=
    match (gateAt D i).inputs with
    | [a, b] => if a ∈ P ∧ b ∈ L then a else b
    | _ => 0
  let lWire (i : ℕ) : ℕ :=
    match (gateAt D i).inputs with
    | [a, b] => if a ∈ P ∧ b ∈ L then b else a
    | _ => 0
  have hR0_spec (i : ℕ) (hi : i ∈ R0) :
      i < D.gates.length ∧ (gateAt D i).op = GateOp.and ∧
      pWire i ∈ P ∧ lWire i ∈ L ∧
      (∀ y : Fin (N + N) → Bool,
        wireVal D y (N + N + i) = true ↔
          (∃ p ∈ ptSup D (pWire i), y (Fin.castAdd N p) = true) ∧
          (∃ l ∈ lnSup D (lWire i), y (Fin.natAdd N l) = true)) := by
    obtain ⟨hilt, hop⟩ := hdec.1 i hi
    obtain ⟨a, b, hins, hab⟩ := hAnd i hilt hop
    have hgate (y : Fin (N + N) → Bool) :
        wireVal D y (N + N + i) = true ↔ wireVal D y a = true ∧ wireVal D y b = true := by
      rw [wireVal_gate_rb D hrb y i hilt, hop, hins]
      change ([wireVal D y a, wireVal D y b].all id = true) ↔ _
      simp
    by_cases hcond : a ∈ P ∧ b ∈ L
    · have hpW : pWire i = a := by simp [pWire, hins, hcond]
      have hlW : lWire i = b := by simp [lWire, hins, hcond]
      refine ⟨hilt, hop, hpW ▸ hcond.1, hlW ▸ hcond.2, fun y => ?_⟩
      rw [hgate y, hpW, hlW, wireVal_of_mem_P D P hrb hP a hcond.1 y,
        wireVal_of_mem_L D L hrb hL b hcond.2 y]
    · have hba : a ∈ L ∧ b ∈ P := hab.resolve_left hcond
      have hpW : pWire i = b := by simp [pWire, hins, hcond]
      have hlW : lWire i = a := by simp [lWire, hins, hcond]
      refine ⟨hilt, hop, hpW ▸ hba.2, hlW ▸ hba.1, fun y => ?_⟩
      rw [hgate y, hpW, hlW, wireVal_of_mem_L D L hrb hL a hba.1 y,
        wireVal_of_mem_P D P hrb hP b hba.2 y, and_comm]
  let R : Finset ℕ := R0.filter (fun i => (ptSup (N := N) D (pWire i)).Nonempty ∧ (lnSup (N := N) D (lWire i)).Nonempty)
  have hrect (i : ℕ) (hi : i ∈ R) (p : Fin N) (hp : p ∈ ptSup D (pWire i))
      (l : Fin N) (hl : l ∈ lnSup D (lWire i)) : I p l := by
    have hi0 : i ∈ R0 := (Finset.mem_filter.mp hi).1
    have hspec := hR0_spec i hi0
    have hv : wireVal D (pairIn p l) (N + N + i) = true :=
      (hspec.2.2.2.2 (pairIn p l)).mpr ⟨⟨p, hp, by simp [pairIn]⟩, ⟨l, hl, by simp [pairIn]⟩⟩
    have hD : circuitFun (N + N) D (pairIn p l) = true :=
      (hD_eval (pairIn p l)).mpr ⟨i, hi0, hv⟩
    obtain ⟨p', l', hI, hp', hl'⟩ := (hfun (pairIn p l)).mp hD
    simp only [pairIn, decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at hp' hl'
    have hpeq : p' = p := by
      rcases hp' with h | h
      · exact Fin.ext h
      · omega
    have hleq : l' = l := by
      rcases hl' with h | h
      · omega
      · exact Fin.ext (by omega)
    subst hpeq; subst hleq; exact hI
  have hcov (p l : Fin N) (hI : I p l) :
      ∃ i ∈ R, p ∈ ptSup D (pWire i) ∧ l ∈ lnSup D (lWire i) := by
    have hD : circuitFun (N + N) D (pairIn p l) = true :=
      (hfun (pairIn p l)).mpr ⟨p, l, hI, by simp [pairIn], by simp [pairIn]⟩
    obtain ⟨i, hi0, hvi⟩ := (hD_eval (pairIn p l)).mp hD
    obtain ⟨⟨p', hp', hpp'⟩, ⟨l', hl', hll'⟩⟩ := ((hR0_spec i hi0).2.2.2.2 (pairIn p l)).mp hvi
    simp only [pairIn, decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at hpp' hll'
    have hpeq : p' = p := by
      rcases hpp' with h | h
      · exact Fin.ext h
      · omega
    have hleq : l' = l := by
      rcases hll' with h | h
      · omega
      · exact Fin.ext (by omega)
    rw [hpeq] at hp'
    rw [hleq] at hl'
    exact ⟨i, Finset.mem_filter.mpr ⟨hi0, ⟨p, hp'⟩, ⟨l, hl'⟩⟩, hp', hl'⟩
  have hstar (i : ℕ) (hi : i ∈ R) :
      (ptSup (N := N) D (pWire i)).card = 1 ∨ (lnSup (N := N) D (lWire i)).card = 1 := by
    by_contra h
    push Not at h
    have hp_pos : 0 < (ptSup (N := N) D (pWire i)).card := Finset.card_pos.mpr (Finset.mem_filter.mp hi).2.1
    have hl_pos : 0 < (lnSup (N := N) D (lWire i)).card := Finset.card_pos.mpr (Finset.mem_filter.mp hi).2.2
    obtain ⟨p, hp, p', hp', hpp'⟩ := Finset.one_lt_card.mp (by omega : 1 < (ptSup (N := N) D (pWire i)).card)
    obtain ⟨l, hl, l', hl', hll'⟩ := Finset.one_lt_card.mp (by omega : 1 < (lnSup (N := N) D (lWire i)).card)
    exact hC4 p p' l l' hpp' hll' ⟨hrect i hi p hp l hl, hrect i hi p hp l' hl',
      hrect i hi p' hp' l hl, hrect i hi p' hp' l' hl'⟩
  let RP : Finset ℕ := R.filter (fun i => (ptSup (N := N) D (pWire i)).card = 1)
  let RL : Finset ℕ := R.filter (fun i => (ptSup (N := N) D (pWire i)).card ≠ 1)
  have hR_split : RP.card + RL.card = R.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext i
      simp only [RP, RL, Finset.mem_union, Finset.mem_filter]
      by_cases h : (ptSup (N := N) D (pWire i)).card = 1 <;> simp [h]
    · rw [Finset.disjoint_left]
      intro i h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  let RP_at (p : Fin N) : Finset ℕ := RP.filter (fun i => p ∈ ptSup (N := N) D (pWire i))
  let RL_at (l : Fin N) : Finset ℕ := RL.filter (fun i => l ∈ lnSup (N := N) D (lWire i))
  let fuel := N + N + D.gates.length + 1
  let L_or (p : Fin N) : Finset ℕ :=
    (Finset.range D.gates.length).filter (fun j =>
      N + N + j ∈ (RP_at p).biUnion (fun i => coneS D N fuel (lWire i)) ∧ 2 ≤ (lnSup (N := N) D (N + N + j)).card)
  let P_or (l : Fin N) : Finset ℕ :=
    (Finset.range D.gates.length).filter (fun j =>
      N + N + j ∈ (RL_at l).biUnion (fun i => coneS D N fuel (pWire i)) ∧ 2 ≤ (ptSup (N := N) D (N + N + j)).card)
  let E_P (p : Fin N) : Finset (Fin N) := (RP_at p).biUnion (fun i => lnSup (N := N) D (lWire i))
  let E_L (l : Fin N) : Finset (Fin N) := (RL_at l).biUnion (fun i => ptSup (N := N) D (pWire i))
  -- Apply cone_bound to each p (L-side) and each l (P-side)
  have hbound_P (p : Fin N) : (E_P p).card ≤ (RP_at p).card + (L_or p).card :=
    cone_bound D L (lnSup (N := N) D) hmono hrb
      (fun w hw => by rcases hL w hw with ⟨_, hlt⟩ | h; exact Or.inl hlt; exact Or.inr h)
      (fun w hw hlt => by
        rcases hL w hw with ⟨hw1, hw2⟩ | ⟨j, _, heq, _, _⟩
        · rw [lnSup_input D w hw1 hw2]; simp
        · omega)
      (fun j hj hm => lnSup_gate_L D L hrb hL j hj hm)
      (RP_at p) lWire
      (fun i hi => by
        have hiR : i ∈ R := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
        exact ⟨(hR0_spec i (Finset.mem_filter.mp hiR).1).2.2.2.1, (Finset.mem_filter.mp hiR).2.2⟩)
  have hbound_L (l : Fin N) : (E_L l).card ≤ (RL_at l).card + (P_or l).card :=
    cone_bound D P (ptSup (N := N) D) hmono hrb
      (fun w hw => by rcases hP w hw with hlt | h; exact Or.inl (by omega); exact Or.inr h)
      (fun w hw hlt => by
        rcases hP w hw with hw1 | ⟨j, _, heq, _, _⟩
        · rw [ptSup_input D w hw1]; simp
        · omega)
      (fun j hj hm => ptSup_gate_P D P hrb hP j hj hm)
      (RL_at l) pWire
      (fun i hi => by
        have hiR : i ∈ R := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
        exact ⟨(hR0_spec i (Finset.mem_filter.mp hiR).1).2.2.1, (Finset.mem_filter.mp hiR).2.1⟩)
  -- Pairwise disjointness of RP_at, RL_at, L_or, P_or
  have hdisj_RP : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin N)) : Set (Fin N)) RP_at := by
    intro p1 _ p2 _ hne
    change Disjoint (RP_at p1) (RP_at p2)
    rw [Finset.disjoint_left]
    intro i h1 h2
    have hcard : (ptSup (N := N) D (pWire i)).card = 1 := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard
    have hp1 : p1 = q := Finset.mem_singleton.mp (hq ▸ (Finset.mem_filter.mp h1).2)
    have hp2 : p2 = q := Finset.mem_singleton.mp (hq ▸ (Finset.mem_filter.mp h2).2)
    exact hne (hp1.trans hp2.symm)
  have hdisj_RL : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin N)) : Set (Fin N)) RL_at := by
    intro l1 _ l2 _ hne
    change Disjoint (RL_at l1) (RL_at l2)
    rw [Finset.disjoint_left]
    intro i h1 h2
    have hiRL := (Finset.mem_filter.mp h1).1
    have hiR : i ∈ R := (Finset.mem_filter.mp hiRL).1
    have hcard : (lnSup (N := N) D (lWire i)).card = 1 := (hstar i hiR).resolve_left (Finset.mem_filter.mp hiRL).2
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard
    have hl1 : l1 = q := Finset.mem_singleton.mp (hq ▸ (Finset.mem_filter.mp h1).2)
    have hl2 : l2 = q := Finset.mem_singleton.mp (hq ▸ (Finset.mem_filter.mp h2).2)
    exact hne (hl1.trans hl2.symm)
  have hdisj_Lor : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin N)) : Set (Fin N)) L_or := by
    intro p1 _ p2 _ hne
    change Disjoint (L_or p1) (L_or p2)
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have hcard : 2 ≤ (lnSup (N := N) D (N + N + j)).card := (Finset.mem_filter.mp hj1).2.2
    obtain ⟨l1, hl1, l2, hl2, hlne⟩ := Finset.one_lt_card.mp (by omega : 1 < (lnSup (N := N) D (N + N + j)).card)
    have hIof (p : Fin N) (hj : j ∈ L_or p) (l : Fin N) (hl : l ∈ lnSup (N := N) D (N + N + j)) : I p l := by
      obtain ⟨i, hi, hcone⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hj).2.1
      have hiR : i ∈ R := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
      have hsub := (coneS_props D L (lnSup (N := N) D) hrb
        (fun w hw => by rcases hL w hw with ⟨_, hlt⟩ | h; exact Or.inl hlt; exact Or.inr h)
        (fun k hk hm => lnSup_gate_L D L hrb hL k hk hm)
        fuel (lWire i) (hR0_spec i (Finset.mem_filter.mp hiR).1).2.2.2.1 (N + N + j) hcone).2
      exact hrect i hiR p (Finset.mem_filter.mp hi).2 l (hsub hl)
    exact hC4 p1 p2 l1 l2 hne hlne ⟨hIof p1 hj1 l1 hl1, hIof p1 hj1 l2 hl2, hIof p2 hj2 l1 hl1, hIof p2 hj2 l2 hl2⟩
  have hdisj_Por : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin N)) : Set (Fin N)) P_or := by
    intro l1 _ l2 _ hne
    change Disjoint (P_or l1) (P_or l2)
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have hcard : 2 ≤ (ptSup (N := N) D (N + N + j)).card := (Finset.mem_filter.mp hj1).2.2
    obtain ⟨p1, hp1, p2, hp2, hpne⟩ := Finset.one_lt_card.mp (by omega : 1 < (ptSup (N := N) D (N + N + j)).card)
    have hIof (l : Fin N) (hj : j ∈ P_or l) (p : Fin N) (hp : p ∈ ptSup (N := N) D (N + N + j)) : I p l := by
      obtain ⟨i, hi, hcone⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hj).2.1
      have hiR : i ∈ R := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
      have hsub := (coneS_props D P (ptSup (N := N) D) hrb
        (fun w hw => by rcases hP w hw with hlt | h; exact Or.inl (by omega); exact Or.inr h)
        (fun k hk hm => ptSup_gate_P D P hrb hP k hk hm)
        fuel (pWire i) (hR0_spec i (Finset.mem_filter.mp hiR).1).2.2.1 (N + N + j) hcone).2
      exact hrect i hiR p (hsub hp) l (Finset.mem_filter.mp hi).2
    exact hC4 p1 p2 l1 l2 hpne hne ⟨hIof l1 hj1 p1 hp1, hIof l2 hj2 p1 hp1, hIof l1 hj1 p2 hp2, hIof l2 hj2 p2 hp2⟩
  -- Define total L_or_all and P_or_all
  let L_or_all : Finset ℕ := Finset.univ.biUnion L_or
  let P_or_all : Finset ℕ := Finset.univ.biUnion P_or
  have hsum_RP : ∑ p : Fin N, (RP_at p).card ≤ RP.card := by
    rw [← Finset.card_biUnion hdisj_RP]
    apply Finset.card_le_card
    intro i hi
    obtain ⟨p, _, hip⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_filter.mp hip).1
  have hsum_RL : ∑ l : Fin N, (RL_at l).card ≤ RL.card := by
    rw [← Finset.card_biUnion hdisj_RL]
    apply Finset.card_le_card
    intro i hi
    obtain ⟨l, _, hil⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_filter.mp hil).1
  have hsum_Lor : ∑ p : Fin N, (L_or p).card = L_or_all.card := (Finset.card_biUnion hdisj_Lor).symm
  have hsum_Por : ∑ l : Fin N, (P_or l).card = P_or_all.card := (Finset.card_biUnion hdisj_Por).symm
  -- E is covered by E_P and E_L
  have hE_card : (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card ≤
      (∑ p : Fin N, (E_P p).card) + (∑ l : Fin N, (E_L l).card) := by
    let S1 : Finset (Fin N × Fin N) := Finset.univ.biUnion (fun p => (E_P p).image (fun l => (p, l)))
    let S2 : Finset (Fin N × Fin N) := Finset.univ.biUnion (fun l => (E_L l).image (fun p => (p, l)))
    have hsub : Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2) ⊆ S1 ∪ S2 := by
      intro e he
      rcases e with ⟨p, l⟩
      have hI : I p l := (Finset.mem_filter.mp he).2
      obtain ⟨i, hiR, hp, hl⟩ := hcov p l hI
      rw [Finset.mem_union]
      by_cases h1 : (ptSup (N := N) D (pWire i)).card = 1
      · left
        simp only [S1, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
        refine ⟨p, l, ?_, rfl⟩
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hiR, h1⟩, hp⟩, hl⟩
      · right
        simp only [S2, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
        refine ⟨l, p, ?_, rfl⟩
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hiR, h1⟩, hl⟩, hp⟩
    have hS1 : S1.card ≤ ∑ p : Fin N, (E_P p).card := by
      calc S1.card
          ≤ ∑ p : Fin N, ((E_P p).image (fun l => (p, l))).card := Finset.card_biUnion_le
        _ ≤ ∑ p : Fin N, (E_P p).card := Finset.sum_le_sum fun p _ => Finset.card_image_le
    have hS2 : S2.card ≤ ∑ l : Fin N, (E_L l).card := by
      calc S2.card
          ≤ ∑ l : Fin N, ((E_L l).image (fun p => (p, l))).card := Finset.card_biUnion_le
        _ ≤ ∑ l : Fin N, (E_L l).card := Finset.sum_le_sum fun l _ => Finset.card_image_le
    calc (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card
        ≤ (S1 ∪ S2).card := Finset.card_le_card hsub
      _ ≤ S1.card + S2.card := Finset.card_union_le _ _
      _ ≤ (∑ p : Fin N, (E_P p).card) + (∑ l : Fin N, (E_L l).card) := Nat.add_le_add hS1 hS2
  -- Show R, L_or_all, P_or_all are pairwise disjoint subsets of Finset.range D.gates.length
  have hLor_mem (j : ℕ) (hj : j ∈ L_or_all) :
      j < D.gates.length ∧ N + N + j ∈ L ∧ (gateAt D j).op = GateOp.or ∧ 2 ≤ (lnSup (N := N) D (N + N + j)).card := by
    obtain ⟨p, _, hjp⟩ := Finset.mem_biUnion.mp hj
    have hjlt : j < D.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hjp).1
    have hjcard : 2 ≤ (lnSup (N := N) D (N + N + j)).card := (Finset.mem_filter.mp hjp).2.2
    obtain ⟨i, hi, hcone⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hjp).2.1
    have hiR : i ∈ R := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
    have hmL : N + N + j ∈ L := (coneS_props D L (lnSup (N := N) D) hrb
      (fun w hw => by rcases hL w hw with ⟨_, hlt⟩ | h; exact Or.inl hlt; exact Or.inr h)
      (fun k hk hm => lnSup_gate_L D L hrb hL k hk hm)
      fuel (lWire i) (hR0_spec i (Finset.mem_filter.mp hiR).1).2.2.2.1 (N + N + j) hcone).1
    have hop : (gateAt D j).op = GateOp.or := by
      rcases hL (N + N + j) hmL with ⟨_, hlt⟩ | ⟨k, _, heq, hop, _⟩
      · omega
      · have : k = j := by omega
        subst this; exact hop
    exact ⟨hjlt, hmL, hop, hjcard⟩
  have hPor_mem (j : ℕ) (hj : j ∈ P_or_all) :
      j < D.gates.length ∧ N + N + j ∈ P ∧ (gateAt D j).op = GateOp.or ∧ 2 ≤ (ptSup (N := N) D (N + N + j)).card := by
    obtain ⟨l, _, hjl⟩ := Finset.mem_biUnion.mp hj
    have hjlt : j < D.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hjl).1
    have hjcard : 2 ≤ (ptSup (N := N) D (N + N + j)).card := (Finset.mem_filter.mp hjl).2.2
    obtain ⟨i, hi, hcone⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hjl).2.1
    have hiR : i ∈ R := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
    have hmP : N + N + j ∈ P := (coneS_props D P (ptSup (N := N) D) hrb
      (fun w hw => by rcases hP w hw with hlt | h; exact Or.inl (by omega); exact Or.inr h)
      (fun k hk hm => ptSup_gate_P D P hrb hP k hk hm)
      fuel (pWire i) (hR0_spec i (Finset.mem_filter.mp hiR).1).2.2.1 (N + N + j) hcone).1
    have hop : (gateAt D j).op = GateOp.or := by
      rcases hP (N + N + j) hmP with hlt | ⟨k, _, heq, hop, _⟩
      · omega
      · have : k = j := by omega
        subst this; exact hop
    exact ⟨hjlt, hmP, hop, hjcard⟩
  have hdisj_RLor : Disjoint R L_or_all := by
    rw [Finset.disjoint_left]
    intro j hjR hjL
    have h1 := (hR0_spec j (Finset.mem_filter.mp hjR).1).2.1
    have h2 := (hLor_mem j hjL).2.2.1
    rw [h1] at h2; cases h2
  have hdisj_RPor : Disjoint R P_or_all := by
    rw [Finset.disjoint_left]
    intro j hjR hjP
    have h1 := (hR0_spec j (Finset.mem_filter.mp hjR).1).2.1
    have h2 := (hPor_mem j hjP).2.2.1
    rw [h1] at h2; cases h2
  have hdisj_LP : Disjoint L_or_all P_or_all := by
    rw [Finset.disjoint_left]
    intro j hjL hjP
    have h1 := ptSup_eq_empty_of_mem_L D L hrb hL (N + N + j) (hLor_mem j hjL).2.1
    have h2 := (hPor_mem j hjP).2.2.2
    rw [h1] at h2; simp at h2
  have htotal : R.card + L_or_all.card + P_or_all.card ≤ D.size := by
    have hu1 : (R ∪ L_or_all).card = R.card + L_or_all.card := Finset.card_union_of_disjoint hdisj_RLor
    have hdisj2 : Disjoint (R ∪ L_or_all) P_or_all := Finset.disjoint_union_left.mpr ⟨hdisj_RPor, hdisj_LP⟩
    have hu2 : (R ∪ L_or_all ∪ P_or_all).card = R.card + L_or_all.card + P_or_all.card := by
      rw [Finset.card_union_of_disjoint hdisj2, hu1]
    rw [← hu2]
    change _ ≤ D.gates.length
    rw [← Finset.card_range D.gates.length]
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_union] at hj
    rw [Finset.mem_range]
    rcases hj with (hj | hj) | hj
    · exact (hR0_spec j (Finset.mem_filter.mp hj).1).1
    · exact (hLor_mem j hj).1
    · exact (hPor_mem j hj).1
  have hsum_EP : ∑ p : Fin N, (E_P p).card ≤ RP.card + L_or_all.card := by
    have h1 := Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) => hbound_P p
    rw [Finset.sum_add_distrib, hsum_Lor] at h1
    omega
  have hsum_EL : ∑ l : Fin N, (E_L l).card ≤ RL.card + P_or_all.card := by
    have h1 := Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => hbound_L l
    rw [Finset.sum_add_distrib, hsum_Por] at h1
    omega
  omega
