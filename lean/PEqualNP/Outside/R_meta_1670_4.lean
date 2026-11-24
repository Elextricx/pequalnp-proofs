import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_1670_4
    (h_sub8 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 8
      (fun x : Fin 8 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) ||
        (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (h_norm14 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C → C.size = 14 →
      PEqualNP.MetaComplexity.circuitFun 9 C =
        (fun x : Fin 9 → Bool =>
          (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
          (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
          (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      (∀ v : ℕ, v = 4 ∨ v = 6 ∨ v = 7 →
        ∃ k : ℕ, ∃ g : PEqualNP.CircuitLowerBounds.Gate,
          C.gates[k]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          (∃ u : ℕ, 9 ≤ u ∧ u < 9 + k ∧ (g.inputs = [v, u] ∨ g.inputs = [u, v])) ∧
          (∀ j : ℕ, ∀ h : PEqualNP.CircuitLowerBounds.Gate,
            j ≠ k → C.gates[j]? = some h →
            (h.op = PEqualNP.CircuitLowerBounds.GateOp.not → h.inputs.head? ≠ some v) ∧
            (h.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → v ∉ h.inputs))) →
      False) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  let f9 : (Fin 9 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
    (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let f8 : (Fin 8 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) ||
    (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let uses (g : PEqualNP.CircuitLowerBounds.Gate) (i : ℕ) : Prop :=
    (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.head? = some i) ∨
    (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ i ∈ g.inputs)
  have uses_mem {g : PEqualNP.CircuitLowerBounds.Gate} {i : ℕ}
      (hop : g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) (hu : uses g i) : i ∈ g.inputs :=
    Or.elim hu (fun h => (hop h.1).elim) (fun h => h.2)
  have uses_head {g : PEqualNP.CircuitLowerBounds.Gate} {i : ℕ}
      (hop : g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (hu : uses g i) : g.inputs.head? = some i :=
    Or.elim hu (fun h => h.2) (fun h => (h.1 hop).elim)
  have kept (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ)
      (hi : i < w.length) : (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have wlen (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g)]
      simp [step]
      omega
  have atEnd (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
    simp [List.getD_eq_getElem?_getD]
  have gateEq (g : PEqualNP.CircuitLowerBounds.Gate) (w1 w2 : List Bool)
      (h : ∀ i, uses g i → w1.getD i false = w2.getD i false) :
      g.op.eval (g.inputs.map fun i => w1.getD i false) =
      g.op.eval (g.inputs.map fun i => w2.getD i false) := by
    cases hop : g.op with
    | not =>
      cases hins : g.inputs with
      | nil => rfl
      | cons a tl =>
        change (!(w1.getD a false)) = (!(w2.getD a false))
        rw [h a (Or.inl ⟨hop, by simp [hins]⟩)]
    | and =>
      congr 1
      apply List.map_congr_left
      intro i hi
      exact h i (Or.inr ⟨by simp [hop], hi⟩)
    | or =>
      congr 1
      apply List.map_congr_left
      intro i hi
      exact h i (Or.inr ⟨by simp [hop], hi⟩)
    | mod m =>
      congr 1
      apply List.map_congr_left
      intro i hi
      exact h i (Or.inr ⟨by simp [hop], hi⟩)
    | maj =>
      congr 1
      apply List.map_congr_left
      intro i hi
      exact h i (Or.inr ⟨by simp [hop], hi⟩)
  have foldl_indep (gs : List PEqualNP.CircuitLowerBounds.Gate) (S : ℕ → Prop)
      (w1 w2 : List Bool) (hlen : w1.length = w2.length)
      (hagree : ∀ i, ¬ S i → w1.getD i false = w2.getD i false)
      (hS : ∀ i, S i → i < w1.length)
      (hno : ∀ g ∈ gs, ∀ i, uses g i → ¬ S i) :
      ∀ i, ¬ S i → (gs.foldl step w1).getD i false = (gs.foldl step w2).getD i false := by
    induction gs generalizing w1 w2 with
    | nil => exact hagree
    | cons g gs ih =>
      rw [List.foldl_cons, List.foldl_cons]
      have hg : g.op.eval (g.inputs.map fun i => w1.getD i false) =
          g.op.eval (g.inputs.map fun i => w2.getD i false) :=
        gateEq g w1 w2 (fun i hi => hagree i (hno g (List.mem_cons_self ..) i hi))
      apply ih (step w1 g) (step w2 g)
      · simp [step, hlen]
      · intro i hi
        by_cases hlt : i < w1.length
        · have hlt2 : i < w2.length := hlen ▸ hlt
          simp only [step, List.getD_eq_getElem?_getD,
            List.getElem?_append_left hlt, List.getElem?_append_left hlt2]
          simpa [List.getD_eq_getElem?_getD] using hagree i hi
        · by_cases heq : i = w1.length
          · subst heq
            have h1 := atEnd w1 (g.op.eval (g.inputs.map fun i => w1.getD i false))
            have h2 : (step w2 g).getD w1.length false =
                g.op.eval (g.inputs.map fun i => w2.getD i false) := by
              rw [hlen]
              exact atEnd w2 _
            exact h1.trans (hg.trans h2.symm)
          · have hge1 : (step w1 g).length ≤ i := by simp [step]; omega
            have hge2 : (step w2 g).length ≤ i := by simp [step, ← hlen]; omega
            rw [List.getD_eq_default _ _ hge1, List.getD_eq_default _ _ hge2]
      · intro i hi
        have := hS i hi
        simp [step]
        omega
      · intro g' hg'
        exact hno g' (List.mem_cons_of_mem g hg')
  -- Compiler state: (wmap : List (Bool ⊕ ℕ), og : List Gate)
  let cstep (st : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate)
      (g : PEqualNP.CircuitLowerBounds.Gate) :
      List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate :=
    PEqualNP.CircuitLowerBounds.GateOp.casesOn g.op
      (List.casesOn g.inputs
        (st.1 ++ [Sum.inl true], st.2)
        (fun a tl => List.casesOn tl
          (st.1 ++ [st.1.getD a (Sum.inl false)], st.2)
          (fun b tl2 => List.casesOn tl2
            (Sum.elim
              (fun ba => Bool.casesOn ba
                (st.1 ++ [Sum.inl false], st.2)
                (st.1 ++ [st.1.getD b (Sum.inl false)], st.2))
              (fun ia => Sum.elim
                (fun bb => Bool.casesOn bb
                  (st.1 ++ [Sum.inl false], st.2)
                  (st.1 ++ [Sum.inr ia], st.2))
                (fun ib => (st.1 ++ [Sum.inr (8 + st.2.length)], st.2 ++ [⟨.and, [ia, ib]⟩]))
                (st.1.getD b (Sum.inl false)))
              (st.1.getD a (Sum.inl false)))
            (fun _ _ => (st.1 ++ [Sum.inl false], st.2)))))
      (List.casesOn g.inputs
        (st.1 ++ [Sum.inl false], st.2)
        (fun a tl => List.casesOn tl
          (st.1 ++ [st.1.getD a (Sum.inl false)], st.2)
          (fun b tl2 => List.casesOn tl2
            (Sum.elim
              (fun ba => Bool.casesOn ba
                (st.1 ++ [st.1.getD b (Sum.inl false)], st.2)
                (st.1 ++ [Sum.inl true], st.2))
              (fun ia => Sum.elim
                (fun bb => Bool.casesOn bb
                  (st.1 ++ [Sum.inr ia], st.2)
                  (st.1 ++ [Sum.inl true], st.2))
                (fun ib => (st.1 ++ [Sum.inr (8 + st.2.length)], st.2 ++ [⟨.or, [ia, ib]⟩]))
                (st.1.getD b (Sum.inl false)))
              (st.1.getD a (Sum.inl false)))
            (fun _ _ => (st.1 ++ [Sum.inl false], st.2)))))
      (List.casesOn g.inputs
        (st.1 ++ [Sum.inl true], st.2)
        (fun a _ => Sum.elim
          (fun ba => (st.1 ++ [Sum.inl (!ba)], st.2))
          (fun ia => (st.1 ++ [Sum.inr (8 + st.2.length)], st.2 ++ [⟨.not, [ia]⟩]))
          (st.1.getD a (Sum.inl false))))
      (fun _ => (st.1 ++ [Sum.inl false], st.2))
      (st.1 ++ [Sum.inl false], st.2)
  have cstep_wmap_len (st : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate)
      (g : PEqualNP.CircuitLowerBounds.Gate) : (cstep st g).1.length = st.1.length + 1 := by
    rcases st with ⟨wmap, og⟩
    rcases g with ⟨op, ins⟩
    cases op with
    | and =>
      rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
      · simp [cstep]
      · simp [cstep]
      · dsimp only [cstep]
        cases wmap.getD a (Sum.inl false) with
        | inl ba => cases ba <;> simp
        | inr ia => cases wmap.getD b (Sum.inl false) with | inl bb => cases bb <;> simp | inr ib => simp
      · simp [cstep]
    | or =>
      rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
      · simp [cstep]
      · simp [cstep]
      · dsimp only [cstep]
        cases wmap.getD a (Sum.inl false) with
        | inl ba => cases ba <;> simp
        | inr ia => cases wmap.getD b (Sum.inl false) with | inl bb => cases bb <;> simp | inr ib => simp
      · simp [cstep]
    | not =>
      rcases ins with _ | ⟨a, _⟩
      · simp [cstep]
      · dsimp only [cstep]
        cases wmap.getD a (Sum.inl false) <;> simp
    | mod m => simp [cstep]
    | maj => simp [cstep]
  have cstep_og_len (st : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate)
      (g : PEqualNP.CircuitLowerBounds.Gate) : (cstep st g).2.length ≤ st.2.length + 1 := by
    rcases st with ⟨wmap, og⟩
    rcases g with ⟨op, ins⟩
    cases op with
    | and =>
      rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
      · simp [cstep]
      · simp [cstep]
      · dsimp only [cstep]
        cases wmap.getD a (Sum.inl false) with
        | inl ba => cases ba <;> simp
        | inr ia => cases wmap.getD b (Sum.inl false) with | inl bb => cases bb <;> simp | inr ib => simp
      · simp [cstep]
    | or =>
      rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
      · simp [cstep]
      · simp [cstep]
      · dsimp only [cstep]
        cases wmap.getD a (Sum.inl false) with
        | inl ba => cases ba <;> simp
        | inr ia => cases wmap.getD b (Sum.inl false) with | inl bb => cases bb <;> simp | inr ib => simp
      · simp [cstep]
    | not =>
      rcases ins with _ | ⟨a, _⟩
      · simp [cstep]
      · dsimp only [cstep]
        cases wmap.getD a (Sum.inl false) <;> simp
    | mod m => simp [cstep]
    | maj => simp [cstep]
  have cstep_wmap_kept (st : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate)
      (g : PEqualNP.CircuitLowerBounds.Gate) (i : ℕ) (hi : i < st.1.length) :
      (cstep st g).1.getD i (Sum.inl false) = st.1.getD i (Sum.inl false) := by
    rcases st with ⟨wmap, og⟩
    rcases g with ⟨op, ins⟩
    have happ (s : Bool ⊕ ℕ) : (wmap ++ [s]).getD i (Sum.inl false) = wmap.getD i (Sum.inl false) := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    cases op with
    | and =>
      rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
      · exact happ _
      · exact happ _
      · dsimp only [cstep]
        cases wmap.getD a (Sum.inl false) with
        | inl ba => cases ba <;> exact happ _
        | inr ia => cases wmap.getD b (Sum.inl false) with | inl bb => cases bb <;> exact happ _ | inr ib => exact happ _
      · exact happ _
    | or =>
      rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
      · exact happ _
      · exact happ _
      · dsimp only [cstep]
        cases wmap.getD a (Sum.inl false) with
        | inl ba => cases ba <;> exact happ _
        | inr ia => cases wmap.getD b (Sum.inl false) with | inl bb => cases bb <;> exact happ _ | inr ib => exact happ _
      · exact happ _
    | not =>
      rcases ins with _ | ⟨a, _⟩
      · exact happ _
      · dsimp only [cstep]
        cases wmap.getD a (Sum.inl false) <;> exact happ _
    | mod m => exact happ _
    | maj => exact happ _
  have cfold_wmap_len (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (st : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate) :
      (gs.foldl cstep st).1.length = st.1.length + gs.length := by
    induction gs generalizing st with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih (cstep st g), cstep_wmap_len]
      simp only [List.length_cons]
      omega
  have cfold_og_len (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (st : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate) :
      (gs.foldl cstep st).2.length ≤ st.2.length + gs.length := by
    induction gs generalizing st with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons]
      have h1 := ih (cstep st g)
      have h2 := cstep_og_len st g
      simp only [List.length_cons]
      omega
  have cfold_wmap_kept (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (st : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate)
      (i : ℕ) (hi : i < st.1.length) :
      (gs.foldl cstep st).1.getD i (Sum.inl false) = st.1.getD i (Sum.inl false) := by
    induction gs generalizing st with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (cstep st g) (by rw [cstep_wmap_len]; omega)]
      exact cstep_wmap_kept st g i hi
  let evalS (x : Fin 8 → Bool) (og : List PEqualNP.CircuitLowerBounds.Gate) (s : Bool ⊕ ℕ) : Bool :=
    Sum.elim id (fun j => (og.foldl step (List.ofFn x)).getD j false) s
  let validS (og : List PEqualNP.CircuitLowerBounds.Gate) (s : Bool ⊕ ℕ) : Prop :=
    Sum.elim (fun _ => True) (fun j => j < 8 + og.length) s
  have cstep_ok (st : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate)
      (g : PEqualNP.CircuitLowerBounds.Gate)
      (hg : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
        PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2)
      (w : (Fin 8 → Bool) → List Bool)
      (hwlen : ∀ x, (w x).length = st.1.length)
      (hagree : ∀ x i, (w x).getD i false = evalS x st.2 (st.1.getD i (Sum.inl false)))
      (hval : ∀ i, validS st.2 (st.1.getD i (Sum.inl false)))
      (hfan : PEqualNP.MetaComplexity.FanInTwo ⟨st.2, 0⟩) :
      (∀ x, (step (w x) g).length = (cstep st g).1.length) ∧
      (∀ x i, (step (w x) g).getD i false = evalS x (cstep st g).2 ((cstep st g).1.getD i (Sum.inl false))) ∧
      (∀ i, validS (cstep st g).2 ((cstep st g).1.getD i (Sum.inl false))) ∧
      PEqualNP.MetaComplexity.FanInTwo ⟨(cstep st g).2, 0⟩ := by
    rcases st with ⟨wmap, og⟩
    have step_elim (s : Bool ⊕ ℕ)
        (hs : ∀ x, g.op.eval (g.inputs.map fun i => (w x).getD i false) = evalS x og s)
        (hvs : validS og s) :
        (∀ x, (step (w x) g).length = (wmap ++ [s]).length) ∧
        (∀ x i, (step (w x) g).getD i false = evalS x og ((wmap ++ [s]).getD i (Sum.inl false))) ∧
        (∀ i, validS og ((wmap ++ [s]).getD i (Sum.inl false))) ∧
        PEqualNP.MetaComplexity.FanInTwo ⟨og, 0⟩ := by
      refine ⟨fun x => by simp [step, hwlen x], ?_, ?_, hfan⟩
      · intro x i
        by_cases hlt : i < wmap.length
        · have hltw : i < (w x).length := (hwlen x).symm ▸ hlt
          simp only [step, List.getD_eq_getElem?_getD,
            List.getElem?_append_left hltw, List.getElem?_append_left hlt]
          simpa [List.getD_eq_getElem?_getD] using hagree x i
        · by_cases heq : i = wmap.length
          · subst heq
            have h1 : (step (w x) g).getD wmap.length false =
                g.op.eval (g.inputs.map fun j => (w x).getD j false) := by
              rw [← hwlen x]; exact atEnd (w x) _
            have h2 : (wmap ++ [s]).getD wmap.length (Sum.inl false) = s := by
              simp [List.getD_eq_getElem?_getD]
            rw [h1, h2, hs x]
          · have hge1 : (step (w x) g).length ≤ i := by simp [step, hwlen x]; omega
            have hge2 : (wmap ++ [s]).length ≤ i := by simp; omega
            rw [List.getD_eq_default _ _ hge1, List.getD_eq_default _ _ hge2]
            rfl
      · intro i
        by_cases hlt : i < wmap.length
        · have h1 : (wmap ++ [s]).getD i (Sum.inl false) = wmap.getD i (Sum.inl false) := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
          rw [h1]; exact hval i
        · by_cases heq : i = wmap.length
          · subst heq; simpa [List.getD_eq_getElem?_getD] using hvs
          · rw [List.getD_eq_default _ _ (by simp; omega)]; trivial
    have step_emit (g' : PEqualNP.CircuitLowerBounds.Gate)
        (hg' : g'.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
          PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g'.inputs.length ≤ 2)
        (hs : ∀ x, g.op.eval (g.inputs.map fun i => (w x).getD i false) =
          g'.op.eval (g'.inputs.map fun i => (og.foldl step (List.ofFn x)).getD i false)) :
        (∀ x, (step (w x) g).length = (wmap ++ [Sum.inr (8 + og.length)]).length) ∧
        (∀ x i, (step (w x) g).getD i false =
          evalS x (og ++ [g']) ((wmap ++ [Sum.inr (8 + og.length)]).getD i (Sum.inl false))) ∧
        (∀ i, validS (og ++ [g']) ((wmap ++ [Sum.inr (8 + og.length)]).getD i (Sum.inl false))) ∧
        PEqualNP.MetaComplexity.FanInTwo ⟨og ++ [g'], 0⟩ := by
      have kept_og (x : Fin 8 → Bool) (s : Bool ⊕ ℕ) (hvs : validS og s) :
          evalS x (og ++ [g']) s = evalS x og s := by
        cases s with
        | inl b => rfl
        | inr j =>
          simp only [evalS, Sum.elim_inr, List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hlt : j < (og.foldl step (List.ofFn x)).length := by
            rw [wlen]; simp only [List.length_ofFn]; exact hvs
          change ((og.foldl step (List.ofFn x)) ++ [_]).getD j false = (og.foldl step (List.ofFn x)).getD j false
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      refine ⟨fun x => by simp [step, hwlen x], ?_, ?_, ?_⟩
      · intro x i
        by_cases hlt : i < wmap.length
        · have hltw : i < (w x).length := (hwlen x).symm ▸ hlt
          simp only [step, List.getD_eq_getElem?_getD,
            List.getElem?_append_left hltw, List.getElem?_append_left hlt]
          have h1 := hagree x i
          have h2 := kept_og x (wmap.getD i (Sum.inl false)) (hval i)
          simpa [List.getD_eq_getElem?_getD] using h1.trans h2.symm
        · by_cases heq : i = wmap.length
          · subst heq
            have h1 : (step (w x) g).getD wmap.length false =
                g.op.eval (g.inputs.map fun j => (w x).getD j false) := by
              rw [← hwlen x]; exact atEnd (w x) _
            have h2 : (wmap ++ [Sum.inr (8 + og.length)]).getD wmap.length (Sum.inl false) =
                Sum.inr (8 + og.length) := by simp [List.getD_eq_getElem?_getD]
            rw [h1, h2, hs x]
            simp only [evalS, Sum.elim_inr, List.foldl_append, List.foldl_cons, List.foldl_nil]
            have hlen0 : (og.foldl step (List.ofFn x)).length = 8 + og.length := by
              rw [wlen]; simp
            rw [← hlen0]
            exact (atEnd _ _).symm
          · have hge1 : (step (w x) g).length ≤ i := by simp [step, hwlen x]; omega
            have hge2 : (wmap ++ [Sum.inr (8 + og.length)]).length ≤ i := by simp; omega
            rw [List.getD_eq_default _ _ hge1, List.getD_eq_default _ _ hge2]
            rfl
      · intro i
        by_cases hlt : i < wmap.length
        · have h1 : (wmap ++ [Sum.inr (8 + og.length)]).getD i (Sum.inl false) =
              wmap.getD i (Sum.inl false) := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
          rw [h1]
          have hv := hval i
          cases hget : wmap.getD i (Sum.inl false) with
          | inl _ => trivial
          | inr j =>
            rw [hget] at hv
            simp only [validS, Sum.elim_inr, List.length_append, List.length_cons, List.length_nil] at hv ⊢
            omega
        · by_cases heq : i = wmap.length
          · subst heq; simp [List.getD_eq_getElem?_getD, validS]
          · rw [List.getD_eq_default _ _ (by simp; omega)]; trivial
      · intro a ha
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with ha | rfl
        · exact hfan a ha
        · exact hg'
    rcases g with ⟨op, ins⟩
    obtain ⟨hopset, hlen2⟩ := hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hopset
    rcases hopset with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
      · exact step_elim (Sum.inl true) (fun x => rfl) trivial
      · exact step_elim (wmap.getD a (Sum.inl false))
          (fun x => by
            change ((w x).getD a false && true) = evalS x og (wmap.getD a (Sum.inl false))
            rw [Bool.and_true, hagree x a]) (hval a)
      · dsimp only [cstep]
        cases ha : wmap.getD a (Sum.inl false) with
        | inl ba =>
          cases ba with
          | false =>
            exact step_elim (Sum.inl false)
              (fun x => by
                change ((w x).getD a false && ((w x).getD b false && true)) = false
                rw [hagree x a, ha]; rfl) trivial
          | true =>
            exact step_elim (wmap.getD b (Sum.inl false))
              (fun x => by
                change ((w x).getD a false && ((w x).getD b false && true)) =
                  evalS x og (wmap.getD b (Sum.inl false))
                rw [hagree x a, ha, hagree x b]
                simp only [evalS, Sum.elim_inl, id_eq, Bool.true_and, Bool.and_true]) (hval b)
        | inr ia =>
          cases hb : wmap.getD b (Sum.inl false) with
          | inl bb =>
            cases bb with
            | false =>
              exact step_elim (Sum.inl false)
                (fun x => by
                  change ((w x).getD a false && ((w x).getD b false && true)) = false
                  rw [hagree x b, hb]
                  simp only [evalS, Sum.elim_inl, id_eq, Bool.false_and, Bool.and_false]) trivial
            | true =>
              exact step_elim (Sum.inr ia)
                (fun x => by
                  change ((w x).getD a false && ((w x).getD b false && true)) =
                    evalS x og (Sum.inr ia)
                  rw [hagree x a, ha, hagree x b, hb]
                  simp only [evalS, Sum.elim_inl, id_eq, Bool.and_true])
                (ha ▸ hval a)
          | inr ib =>
            exact step_emit ⟨.and, [ia, ib]⟩ ⟨by simp, by simp⟩
              (fun x => by
                change ((w x).getD a false && ((w x).getD b false && true)) =
                  ((og.foldl step (List.ofFn x)).getD ia false &&
                    ((og.foldl step (List.ofFn x)).getD ib false && true))
                rw [hagree x a, ha, hagree x b, hb]; rfl)
      · simp at hlen2
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
      · exact step_elim (Sum.inl false) (fun x => rfl) trivial
      · exact step_elim (wmap.getD a (Sum.inl false))
          (fun x => by
            change ((w x).getD a false || false) = evalS x og (wmap.getD a (Sum.inl false))
            rw [Bool.or_false, hagree x a]) (hval a)
      · dsimp only [cstep]
        cases ha : wmap.getD a (Sum.inl false) with
        | inl ba =>
          cases ba with
          | true =>
            exact step_elim (Sum.inl true)
              (fun x => by
                change ((w x).getD a false || ((w x).getD b false || false)) = true
                rw [hagree x a, ha]; rfl) trivial
          | false =>
            exact step_elim (wmap.getD b (Sum.inl false))
              (fun x => by
                change ((w x).getD a false || ((w x).getD b false || false)) =
                  evalS x og (wmap.getD b (Sum.inl false))
                rw [hagree x a, ha, hagree x b]
                simp only [evalS, Sum.elim_inl, id_eq, Bool.false_or, Bool.or_false]) (hval b)
        | inr ia =>
          cases hb : wmap.getD b (Sum.inl false) with
          | inl bb =>
            cases bb with
            | true =>
              exact step_elim (Sum.inl true)
                (fun x => by
                  change ((w x).getD a false || ((w x).getD b false || false)) = true
                  rw [hagree x b, hb]
                  simp only [evalS, Sum.elim_inl, id_eq, Bool.true_or, Bool.or_true]) trivial
            | false =>
              exact step_elim (Sum.inr ia)
                (fun x => by
                  change ((w x).getD a false || ((w x).getD b false || false)) =
                    evalS x og (Sum.inr ia)
                  rw [hagree x a, ha, hagree x b, hb]
                  simp only [evalS, Sum.elim_inl, id_eq, Bool.or_false])
                (ha ▸ hval a)
          | inr ib =>
            exact step_emit ⟨.or, [ia, ib]⟩ ⟨by simp, by simp⟩
              (fun x => by
                change ((w x).getD a false || ((w x).getD b false || false)) =
                  ((og.foldl step (List.ofFn x)).getD ia false ||
                    ((og.foldl step (List.ofFn x)).getD ib false || false))
                rw [hagree x a, ha, hagree x b, hb]; rfl)
      · simp at hlen2
    · rcases ins with _ | ⟨a, tl⟩
      · exact step_elim (Sum.inl true) (fun x => rfl) trivial
      · dsimp only [cstep]
        cases ha : wmap.getD a (Sum.inl false) with
        | inl ba =>
          exact step_elim (Sum.inl (!ba))
            (fun x => by
              change (!((w x).getD a false)) = (!ba)
              rw [hagree x a, ha]; rfl) trivial
        | inr ia =>
          exact step_emit ⟨.not, [ia]⟩ ⟨by simp, by simp⟩
            (fun x => by
              change (!((w x).getD a false)) = (!((og.foldl step (List.ofFn x)).getD ia false))
              rw [hagree x a, ha]; rfl)
  have cfold_ok (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (st : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate)
      (hgs : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
        PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2)
      (w : (Fin 8 → Bool) → List Bool)
      (hwlen : ∀ x, (w x).length = st.1.length)
      (hagree : ∀ x i, (w x).getD i false = evalS x st.2 (st.1.getD i (Sum.inl false)))
      (hval : ∀ i, validS st.2 (st.1.getD i (Sum.inl false)))
      (hfan : PEqualNP.MetaComplexity.FanInTwo ⟨st.2, 0⟩) :
      (∀ x i, (gs.foldl step (w x)).getD i false =
        evalS x (gs.foldl cstep st).2 ((gs.foldl cstep st).1.getD i (Sum.inl false))) ∧
      PEqualNP.MetaComplexity.FanInTwo ⟨(gs.foldl cstep st).2, 0⟩ := by
    induction gs generalizing st w with
    | nil => exact ⟨hagree, hfan⟩
    | cons g gs ih =>
      rw [List.foldl_cons]
      have h1 := cstep_ok st g (hgs g (List.mem_cons_self ..)) w hwlen hagree hval hfan
      have h2 := ih (cstep st g) (fun a ha => hgs a (List.mem_cons_of_mem g ha))
        (fun x => step (w x) g) h1.1 h1.2.1 h1.2.2.1 h1.2.2.2
      exact ⟨fun x i => by rw [List.foldl_cons]; exact h2.1 x i, h2.2⟩
  have f8_nonconst : ∃ x0 x1 : Fin 8 → Bool, f8 x0 = false ∧ f8 x1 = true := by
    refine ⟨fun _ => false, ![true, true, false, false, false, false, false, false], by decide, by decide⟩
  have no_small_compile (gs : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ)
      (st : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate)
      (hgs : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
        PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2)
      (w : (Fin 8 → Bool) → List Bool)
      (hwlen : ∀ x, (w x).length = st.1.length)
      (hagree : ∀ x i, (w x).getD i false = evalS x st.2 (st.1.getD i (Sum.inl false)))
      (hval : ∀ i, validS st.2 (st.1.getD i (Sum.inl false)))
      (hfan : PEqualNP.MetaComplexity.FanInTwo ⟨st.2, 0⟩)
      (hcomp : ∀ x, (gs.foldl step (w x)).getD out false = f8 x) :
      13 ≤ (gs.foldl cstep st).2.length ∧
      (∀ b : Bool, (gs.foldl cstep st).1.getD out (Sum.inl false) ≠ Sum.inl b) := by
    have hok := cfold_ok gs st hgs w hwlen hagree hval hfan
    have hnotconst : ∀ b : Bool, (gs.foldl cstep st).1.getD out (Sum.inl false) ≠ Sum.inl b := by
      intro b hb
      obtain ⟨x0, x1, hx0, hx1⟩ := f8_nonconst
      have e0 := (hcomp x0).symm.trans (hok.1 x0 out)
      have e1 := (hcomp x1).symm.trans (hok.1 x1 out)
      rw [hb] at e0 e1
      simp only [evalS, Sum.elim_inl, id_eq] at e0 e1
      rw [hx0] at e0; rw [hx1] at e1
      cases b
      · cases e1
      · cases e0
    refine ⟨?_, hnotconst⟩
    by_contra hlt
    cases hst : (gs.foldl cstep st).1.getD out (Sum.inl false) with
    | inl b => exact hnotconst b hst
    | inr out' =>
      apply h_sub8
      refine ⟨⟨(gs.foldl cstep st).2, out'⟩, hok.2, by change (gs.foldl cstep st).2.length ≤ 12; omega, ?_⟩
      intro x
      have h1 := (hok.1 x out).symm.trans (hcomp x)
      rw [hst] at h1
      exact h1
  have uses_inl_elim (st : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate)
      (g : PEqualNP.CircuitLowerBounds.Gate)
      (hg : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
        PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2)
      (i : ℕ) (huse : uses g i) (b : Bool) (hinl : st.1.getD i (Sum.inl false) = Sum.inl b) :
      (cstep st g).2.length = st.2.length := by
    rcases st with ⟨wmap, og⟩
    rcases g with ⟨op, ins⟩
    obtain ⟨hopset, hlen2⟩ := hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hopset
    rcases hopset with rfl | rfl | rfl
    · have hi : i ∈ ins := uses_mem (fun h => by cases h) huse
      rcases ins with _ | ⟨a, _ | ⟨c, _ | _⟩⟩
      · simp at hi
      · rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        dsimp only [cstep]
        rcases hi with rfl | rfl
        · rw [hinl]; cases b with | false => rfl | true => cases wmap.getD c (Sum.inl false) with | inl bc => cases bc <;> rfl | inr ic => rfl
        · rw [hinl]
          cases wmap.getD a (Sum.inl false) with
          | inl ba => cases ba with | false => rfl | true => cases b <;> rfl
          | inr ia => cases b <;> rfl
      · simp at hlen2
    · have hi : i ∈ ins := uses_mem (fun h => by cases h) huse
      rcases ins with _ | ⟨a, _ | ⟨c, _ | _⟩⟩
      · simp at hi
      · rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        dsimp only [cstep]
        rcases hi with rfl | rfl
        · rw [hinl]; cases b with | true => rfl | false => cases wmap.getD c (Sum.inl false) with | inl bc => cases bc <;> rfl | inr ic => rfl
        · rw [hinl]
          cases wmap.getD a (Sum.inl false) with
          | inl ba => cases ba with | true => rfl | false => cases b <;> rfl
          | inr ia => cases b <;> rfl
      · simp at hlen2
    · have hi : ins.head? = some i := uses_head rfl huse
      rcases ins with _ | ⟨a, tl⟩
      · simp at hi
      · simp only [List.head?_cons, Option.some.injEq] at hi
        subst hi
        dsimp only [cstep]
        rw [hinl]
        rfl
  have two_elims_bound (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (st : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate)
      (k1 k2 : ℕ) (g1 g2 : PEqualNP.CircuitLowerBounds.Gate)
      (hlt : k1 < k2) (h1 : gs[k1]? = some g1) (h2 : gs[k2]? = some g2)
      (he1 : (cstep ((gs.take k1).foldl cstep st) g1).2.length = ((gs.take k1).foldl cstep st).2.length)
      (he2 : (cstep ((gs.take k2).foldl cstep st) g2).2.length = ((gs.take k2).foldl cstep st).2.length) :
      (gs.foldl cstep st).2.length + 2 ≤ st.2.length + gs.length := by
    have hk2lt : k2 < gs.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at h2; cases h2
    have hsplit2 : gs = gs.take k2 ++ g2 :: gs.drop (k2 + 1) := by
      have hget : gs[k2] = g2 := by simpa [List.getElem?_eq_getElem hk2lt] using h2
      conv_lhs => rw [← List.take_append_drop k2 gs]
      rw [List.drop_eq_getElem_cons hk2lt, hget]
    have hk1lt : k1 < (gs.take k2).length := by simp; omega
    have hsplit1 : gs.take k2 = gs.take k1 ++ g1 :: (gs.take k2).drop (k1 + 1) := by
      have hget : (gs.take k2)[k1] = g1 := by
        have : (gs.take k2)[k1]? = some g1 := by rw [List.getElem?_take_of_lt hlt]; exact h1
        simpa [List.getElem?_eq_getElem hk1lt] using this
      conv_lhs => rw [← List.take_append_drop k1 (gs.take k2)]
      rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hlt), List.drop_eq_getElem_cons hk1lt, hget]
    have hst1 := cfold_og_len (gs.take k1) st
    have hst2 := cfold_og_len ((gs.take k2).drop (k1 + 1)) (cstep ((gs.take k1).foldl cstep st) g1)
    have hst3 := cfold_og_len (gs.drop (k2 + 1)) (cstep ((gs.take k2).foldl cstep st) g2)
    have hfold2 : gs.foldl cstep st =
        (gs.drop (k2 + 1)).foldl cstep (cstep ((gs.take k2).foldl cstep st) g2) := by
      conv_lhs => rw [hsplit2, List.foldl_append, List.foldl_cons]
    have hfold1 : (gs.take k2).foldl cstep st =
        ((gs.take k2).drop (k1 + 1)).foldl cstep (cstep ((gs.take k1).foldl cstep st) g1) := by
      conv_lhs => rw [hsplit1, List.foldl_append, List.foldl_cons]
    rw [hfold2, hfold1]
    rw [hfold1] at he2 hst3
    have hlen1 : (gs.take k1).length = k1 := by simp; omega
    have hlen2 : ((gs.take k2).drop (k1 + 1)).length = k2 - k1 - 1 := by simp; omega
    have hlen3 : (gs.drop (k2 + 1)).length = gs.length - k2 - 1 := by simp; omega
    omega
  have one_elim_bound (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (st : List (Bool ⊕ ℕ) × List PEqualNP.CircuitLowerBounds.Gate)
      (k1 : ℕ) (g1 : PEqualNP.CircuitLowerBounds.Gate)
      (h1 : gs[k1]? = some g1)
      (he1 : (cstep ((gs.take k1).foldl cstep st) g1).2.length = ((gs.take k1).foldl cstep st).2.length) :
      (gs.foldl cstep st).2.length + 1 ≤ st.2.length + gs.length := by
    have hk1lt : k1 < gs.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at h1; cases h1
    have hsplit1 : gs = gs.take k1 ++ g1 :: gs.drop (k1 + 1) := by
      have hget : gs[k1] = g1 := by simpa [List.getElem?_eq_getElem hk1lt] using h1
      conv_lhs => rw [← List.take_append_drop k1 gs]
      rw [List.drop_eq_getElem_cons hk1lt, hget]
    have hst1 := cfold_og_len (gs.take k1) st
    have hst2 := cfold_og_len (gs.drop (k1 + 1)) (cstep ((gs.take k1).foldl cstep st) g1)
    have hfold1 : gs.foldl cstep st =
        (gs.drop (k1 + 1)).foldl cstep (cstep ((gs.take k1).foldl cstep st) g1) := by
      conv_lhs => rw [hsplit1, List.foldl_append, List.foldl_cons]
    rw [hfold1]
    have hlen1 : (gs.take k1).length = k1 := by simp; omega
    have hlen2 : (gs.drop (k1 + 1)).length = gs.length - k1 - 1 := by simp; omega
    omega
  -- Main theorem
  intro C hfan hfirst hfun
  by_contra hsmall
  have hle15 : C.size ≤ 15 := by omega
  obtain ⟨gs, out⟩ := C
  cases gs with
  | nil =>
    have bad := hfirst (fun _ => true)
    change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at bad
    rw [List.getD_eq_default _ _ (by simp)] at bad
    cases bad
  | cons g0 tail =>
    have htail_len : tail.length ≤ 14 := by change (g0 :: tail).length ≤ 15 at hle15; simp at hle15; omega
    have htail_fan : ∀ g ∈ tail,
        g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
          PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2 :=
      fun g hg => hfan g (List.mem_cons_of_mem g0 hg)
    have wire0 (y : Fin 9 → Bool) :
        step (List.ofFn y) g0 = List.ofFn y ++ [y 0 && y 4] := by
      have h := hfirst y
      change (tail.foldl step (step (List.ofFn y) g0)).getD 9 false = _ at h
      rw [kept tail _ 9 (by simp [step])] at h
      have ha : (step (List.ofFn y) g0).getD 9 false =
          g0.op.eval (g0.inputs.map fun i => (List.ofFn y).getD i false) := by
        simp [step]
      rw [ha] at h
      simp only [step, h]
    have eval_tail (y : Fin 9 → Bool) :
        (tail.foldl step (List.ofFn y ++ [y 0 && y 4])).getD out false = f9 y := by
      have h := congrFun hfun y
      change (tail.foldl step (step (List.ofFn y) g0)).getD out false = f9 y at h
      rwa [wire0 y] at h
    let ext4 : (Fin 8 → Bool) → (Fin 9 → Bool) := fun x => ![x 0, x 1, x 2, x 3, false, x 4, x 5, x 6, x 7]
    have ext4_f : ∀ x : Fin 8 → Bool, f9 (ext4 x) = f8 x := by
      intro x; simp [f9, f8, ext4]
    let imap10 : List (Bool ⊕ ℕ) :=
      [Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl false,
       Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inl false]
    have hcomp10 : 13 ≤ (tail.foldl cstep (imap10, [])).2.length ∧
        (∀ b : Bool, (tail.foldl cstep (imap10, [])).1.getD out (Sum.inl false) ≠ Sum.inl b) := by
      apply no_small_compile tail out (imap10, []) htail_fan
        (fun x => List.ofFn (ext4 x) ++ [false])
      · intro x; simp [imap10]
      · intro x i
        rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
          simp [imap10, ext4, evalS, List.ofFn_succ]
      · intro i
        rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
          simp [imap10, validS]
      · intro g hg; cases hg
      · intro x
        have h := eval_tail (ext4 x)
        have h04 : (ext4 x 0 && ext4 x 4) = false := by simp [ext4]
        rw [h04, ext4_f x] at h
        exact h
    have hout4 : out ≠ 4 := by
      intro h; subst h
      have h1 := eval_tail ![false, false, false, false, true, false, false, false, false]
      rw [kept tail _ 4 (by simp)] at h1
      simp [f9, List.ofFn_succ] at h1
    have hout9 : out ≠ 9 := by
      intro h; subst h
      have h1 := eval_tail ![true, true, false, false, false, false, false, false, false]
      rw [kept tail _ 9 (by simp)] at h1
      simp [f9, List.ofFn_succ] at h1
    have hex4 : ∃ k : ℕ, ∃ g : PEqualNP.CircuitLowerBounds.Gate, tail[k]? = some g ∧ uses g 4 := by
      by_contra hno
      push Not at hno
      let y0 : Fin 9 → Bool := ![false, false, false, true, false, false, false, false, false]
      let y1 : Fin 9 → Bool := ![false, false, false, true, true, false, false, false, false]
      have heq := foldl_indep tail (fun i => i = 4)
        (List.ofFn y0 ++ [y0 0 && y0 4]) (List.ofFn y1 ++ [y1 0 && y1 4])
        (by simp)
        (fun i hi => by
          rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
          all_goals simp [y0, y1, List.ofFn_succ] at hi ⊢)
        (fun i hi => by subst hi; simp)
        (fun g hg i hi h4 => by
          subst h4
          obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hg
          exact hno k g hk hi)
        out hout4
      rw [eval_tail y0, eval_tail y1] at heq
      have hne : f9 y0 ≠ f9 y1 := by decide
      exact hne heq
    obtain ⟨k4, g4, hk4, huse4⟩ := hex4
    have h4_elim : (cstep ((tail.take k4).foldl cstep (imap10, [])) g4).2.length =
        ((tail.take k4).foldl cstep (imap10, [])).2.length := by
      apply uses_inl_elim _ g4 (htail_fan g4 (List.mem_of_getElem? hk4)) 4 huse4 false
      rw [cfold_wmap_kept _ (imap10, []) 4 (by simp [imap10])]
      rfl
    have htail14 : tail.length = 14 := by
      have h1 := one_elim_bound tail (imap10, []) k4 g4 hk4 h4_elim
      simp only [List.length_nil, zero_add] at h1
      omega
    have no_other_elim (j : ℕ) (gj : PEqualNP.CircuitLowerBounds.Gate) (hne : j ≠ k4)
        (hj : tail[j]? = some gj)
        (hej : (cstep ((tail.take j).foldl cstep (imap10, [])) gj).2.length =
          ((tail.take j).foldl cstep (imap10, [])).2.length) : False := by
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · have h := two_elims_bound tail (imap10, []) j k4 gj g4 hlt hj hk4 hej h4_elim
        simp only [List.length_nil, zero_add] at h; omega
      · have h := two_elims_bound tail (imap10, []) k4 j g4 gj hgt hk4 hj h4_elim hej
        simp only [List.length_nil, zero_add] at h; omega
    have no_other_49 (j : ℕ) (gj : PEqualNP.CircuitLowerBounds.Gate) (hne : j ≠ k4)
        (hj : tail[j]? = some gj) : ¬ uses gj 4 ∧ ¬ uses gj 9 := by
      constructor
      · intro hu
        apply no_other_elim j gj hne hj
        apply uses_inl_elim _ gj (htail_fan gj (List.mem_of_getElem? hj)) 4 hu false
        rw [cfold_wmap_kept _ (imap10, []) 4 (by simp [imap10])]; rfl
      · intro hu
        apply no_other_elim j gj hne hj
        apply uses_inl_elim _ gj (htail_fan gj (List.mem_of_getElem? hj)) 9 hu false
        rw [cfold_wmap_kept _ (imap10, []) 9 (by simp [imap10])]; rfl
    have hg4_no9 : ¬ uses g4 9 := by
      intro huse9
      have hk4lt : k4 < tail.length := by
        by_contra h; rw [List.getElem?_eq_none (by omega)] at hk4; cases hk4
      have hg4_inl : ∃ b : Bool,
          (cstep ((tail.take k4).foldl cstep (imap10, [])) g4).1.getD (10 + k4) (Sum.inl false) = Sum.inl b := by
        let st4 := (tail.take k4).foldl cstep (imap10, [])
        have hstlen : st4.1.length = 10 + k4 := by
          dsimp only [st4]; rw [cfold_wmap_len]; simp [imap10]; omega
        have hget4 : st4.1.getD 4 (Sum.inl false) = Sum.inl false := by
          dsimp only [st4]; rw [cfold_wmap_kept _ (imap10, []) 4 (by simp [imap10])]; rfl
        have hget9 : st4.1.getD 9 (Sum.inl false) = Sum.inl false := by
          dsimp only [st4]; rw [cfold_wmap_kept _ (imap10, []) 9 (by simp [imap10])]; rfl
        have hat (s : Bool ⊕ ℕ) : (st4.1 ++ [s]).getD (10 + k4) (Sum.inl false) = s := by
          rw [← hstlen]; simp [List.getD_eq_getElem?_getD]
        obtain ⟨hopset, hlen2⟩ := htail_fan g4 (List.mem_of_getElem? hk4)
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hopset
        rcases g4 with ⟨op4, ins4⟩
        change ∃ b : Bool, (cstep st4 ⟨op4, ins4⟩).1.getD (10 + k4) (Sum.inl false) = Sum.inl b
        rcases hopset with rfl | rfl | rfl
        · have hi4 : 4 ∈ ins4 := uses_mem (fun h => by cases h) huse4
          have hi9 : 9 ∈ ins4 := uses_mem (fun h => by cases h) huse9
          rcases ins4 with _ | ⟨a, _ | ⟨c, _ | _⟩⟩
          · simp at hi4
          · simp at hi4 hi9; omega
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi4 hi9
            rcases hi4 with h4 | h4 <;> rcases hi9 with h9 | h9
            · omega
            · subst h4; subst h9; exact ⟨false, by dsimp only [cstep]; rw [hget4, hget9]; exact hat _⟩
            · subst h4; subst h9; exact ⟨false, by dsimp only [cstep]; rw [hget4, hget9]; exact hat _⟩
            · omega
          · simp at hlen2
        · have hi4 : 4 ∈ ins4 := uses_mem (fun h => by cases h) huse4
          have hi9 : 9 ∈ ins4 := uses_mem (fun h => by cases h) huse9
          rcases ins4 with _ | ⟨a, _ | ⟨c, _ | _⟩⟩
          · simp at hi4
          · simp at hi4 hi9; omega
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi4 hi9
            rcases hi4 with h4 | h4 <;> rcases hi9 with h9 | h9
            · omega
            · subst h4; subst h9; exact ⟨false, by dsimp only [cstep]; rw [hget4, hget9]; exact hat _⟩
            · subst h4; subst h9; exact ⟨false, by dsimp only [cstep]; rw [hget4, hget9]; exact hat _⟩
            · omega
          · simp at hlen2
        · have h1 : ins4.head? = some 4 := uses_head rfl huse4
          have h2 : ins4.head? = some 9 := uses_head rfl huse9
          rw [h1] at h2; simp at h2
      obtain ⟨b4, hb4⟩ := hg4_inl
      have h10k4_final : (tail.foldl cstep (imap10, [])).1.getD (10 + k4) (Sum.inl false) = Sum.inl b4 := by
        have hsplit : tail = tail.take k4 ++ g4 :: tail.drop (k4 + 1) := by
          have hget : tail[k4] = g4 := by simpa [List.getElem?_eq_getElem hk4lt] using hk4
          conv_lhs => rw [← List.take_append_drop k4 tail]
          rw [List.drop_eq_getElem_cons hk4lt, hget]
        conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
        rw [cfold_wmap_kept _ _ (10 + k4) (by rw [cstep_wmap_len, cfold_wmap_len]; simp [imap10]; omega)]
        exact hb4
      have hout_ne : out ≠ 10 + k4 := by
        intro h; subst h; exact hcomp10.2 b4 h10k4_final
      have hno_read : ∀ j : ℕ, ∀ gj : PEqualNP.CircuitLowerBounds.Gate,
          k4 < j → tail[j]? = some gj → ¬ uses gj (10 + k4) := by
        intro j gj hgt hj hu
        apply no_other_elim j gj (by omega) hj
        apply uses_inl_elim _ gj (htail_fan gj (List.mem_of_getElem? hj)) (10 + k4) hu b4
        have hsplitj : tail.take j = tail.take k4 ++ g4 :: (tail.take j).drop (k4 + 1) := by
          have hk4ltj : k4 < (tail.take j).length := by simp; omega
          have hget : (tail.take j)[k4] = g4 := by
            have : (tail.take j)[k4]? = some g4 := by rw [List.getElem?_take_of_lt hgt]; exact hk4
            simpa [List.getElem?_eq_getElem hk4ltj] using this
          conv_lhs => rw [← List.take_append_drop k4 (tail.take j)]
          rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hgt), List.drop_eq_getElem_cons hk4ltj, hget]
        rw [hsplitj, List.foldl_append, List.foldl_cons,
          cfold_wmap_kept _ _ (10 + k4) (by rw [cstep_wmap_len, cfold_wmap_len]; simp [imap10]; omega)]
        exact hb4
      let y0 : Fin 9 → Bool := ![false, false, false, true, false, false, false, false, false]
      let y1 : Fin 9 → Bool := ![false, false, false, true, true, false, false, false, false]
      have hsplit : tail = tail.take k4 ++ g4 :: tail.drop (k4 + 1) := by
        have hget : tail[k4] = g4 := by simpa [List.getElem?_eq_getElem hk4lt] using hk4
        conv_lhs => rw [← List.take_append_drop k4 tail]
        rw [List.drop_eq_getElem_cons hk4lt, hget]
      let p0 := (tail.take k4).foldl step (List.ofFn y0 ++ [y0 0 && y0 4])
      let p1 := (tail.take k4).foldl step (List.ofFn y1 ++ [y1 0 && y1 4])
      have hp0len : p0.length = 10 + k4 := by dsimp only [p0]; rw [wlen]; simp; omega
      have hp1len : p1.length = 10 + k4 := by dsimp only [p1]; rw [wlen]; simp; omega
      have hpre : ∀ i, i ≠ 4 → p0.getD i false = p1.getD i false := by
        apply foldl_indep (tail.take k4) (fun i => i = 4)
        · simp
        · intro i hi
          rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
          all_goals simp [y0, y1, List.ofFn_succ] at hi ⊢
        · intro i hi; subst hi; simp
        · intro g hg i hi h4; subst h4
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
          have hjlt : j < k4 := by
            by_contra h; rw [List.getElem?_eq_none (by simp; omega)] at hj; cases hj
          rw [List.getElem?_take_of_lt hjlt] at hj
          exact (no_other_49 j g (by omega) hj).1 hi
      let w0a := step p0 g4
      let w1a := step p1 g4
      have hlen0a : w0a.length = 10 + k4 + 1 := by
        change (p0 ++ [_]).length = 10 + k4 + 1; simp [hp0len]
      have hlen1a : w1a.length = 10 + k4 + 1 := by
        change (p1 ++ [_]).length = 10 + k4 + 1; simp [hp1len]
      have hpost : ((tail.drop (k4 + 1)).foldl step w0a).getD out false =
          ((tail.drop (k4 + 1)).foldl step w1a).getD out false := by
        apply foldl_indep (tail.drop (k4 + 1)) (fun i => i = 4 ∨ i = 10 + k4) w0a w1a
        · rw [hlen0a, hlen1a]
        · intro i hi
          push Not at hi
          by_cases hlt : i < 10 + k4
          · have hlt0 : i < p0.length := by omega
            have hlt1 : i < p1.length := by omega
            have h0eq : w0a.getD i false = p0.getD i false := by
              change (p0 ++ [_]).getD i false = p0.getD i false
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt0]
            have h1eq : w1a.getD i false = p1.getD i false := by
              change (p1 ++ [_]).getD i false = p1.getD i false
              simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt1]
            rw [h0eq, h1eq]
            exact hpre i hi.1
          · rw [List.getD_eq_default _ _ (by rw [hlen0a]; omega),
                List.getD_eq_default _ _ (by rw [hlen1a]; omega)]
        · intro i hi; rw [hlen0a]; rcases hi with rfl | rfl <;> omega
        · intro g hg i hi hbad
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
          rw [List.getElem?_drop] at hj
          rcases hbad with rfl | rfl
          · exact (no_other_49 (k4 + 1 + j) g (by omega) hj).1 hi
          · exact hno_read (k4 + 1 + j) g (by omega) hj hi
        · exact fun h => by rcases h with h | h; exact hout4 h; exact hout_ne h
      have hev0 := eval_tail y0
      have hev1 := eval_tail y1
      rw [hsplit, List.foldl_append, List.foldl_cons] at hev0 hev1
      change ((tail.drop (k4 + 1)).foldl step w0a).getD out false = f9 y0 at hev0
      change ((tail.drop (k4 + 1)).foldl step w1a).getD out false = f9 y1 at hev1
      rw [hev0, hev1] at hpost
      have hne : f9 y0 ≠ f9 y1 := by decide
      exact hne hpost
    have hno9 : ∀ g ∈ tail, ¬ uses g 9 := by
      intro g hg hu
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
      by_cases hjk : j = k4
      · subst hjk; rw [hk4] at hj; cases hj; exact hg4_no9 hu
      · exact (no_other_49 j g hjk hj).2 hu
    let shiftIdx (i : ℕ) : ℕ := if i < 9 then i else i - 1
    let shiftGate (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
      PEqualNP.CircuitLowerBounds.GateOp.casesOn g.op
        ⟨.and, g.inputs.map shiftIdx⟩
        ⟨.or, g.inputs.map shiftIdx⟩
        ⟨.not, (g.inputs.take 1).map shiftIdx⟩
        (fun m => ⟨.mod m, g.inputs.map shiftIdx⟩)
        ⟨.maj, g.inputs.map shiftIdx⟩
    let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨tail.map shiftGate, shiftIdx out⟩
    have hC'size : C'.size = 14 := by
      change (tail.map shiftGate).length = 14
      simp [htail14]
    have hC'fan : PEqualNP.MetaComplexity.FanInTwo C' := by
      intro g' hg'
      simp only [C', List.mem_map] at hg'
      obtain ⟨g, hg, rfl⟩ := hg'
      obtain ⟨hop, hlen⟩ := htail_fan g hg
      cases h : g.op
      · simp [shiftGate, h, hlen]
      · simp [shiftGate, h, hlen]
      · simp [shiftGate, h]
      · simp [h] at hop
      · simp [h] at hop
    have hC'wires (gs' : List PEqualNP.CircuitLowerBounds.Gate) (w1 w2 : List Bool)
        (hgs' : ∀ g ∈ gs', ¬ uses g 9)
        (hlen : w1.length = w2.length + 1) (hle9 : 9 ≤ w2.length)
        (hrel : ∀ i, i ≠ 9 → w1.getD i false = w2.getD (shiftIdx i) false) :
        ∀ i, i ≠ 9 → (gs'.foldl step w1).getD i false =
          ((gs'.map shiftGate).foldl step w2).getD (shiftIdx i) false := by
      induction gs' generalizing w1 w2 with
      | nil => exact hrel
      | cons g gs' ih =>
        rw [List.map_cons, List.foldl_cons, List.foldl_cons]
        have hgno9 := hgs' g (List.mem_cons_self ..)
        have hvaleq : g.op.eval (g.inputs.map fun i => w1.getD i false) =
            (shiftGate g).op.eval ((shiftGate g).inputs.map fun i => w2.getD i false) := by
          cases hop : g.op with
          | not =>
            rcases hins : g.inputs with _ | ⟨a, tl⟩
            · dsimp only [shiftGate]; rw [hop, hins]; rfl
            · have ha9 : a ≠ 9 := fun ha => hgno9 (Or.inl ⟨hop, by simp [hins, ha]⟩)
              dsimp only [shiftGate]; rw [hop, hins]
              change (!(w1.getD a false)) = (!(w2.getD (shiftIdx a) false))
              rw [hrel a ha9]
          | and =>
            simp only [shiftGate, hop, List.map_map, Function.comp_def]
            congr 1
            apply List.map_congr_left
            intro a ha
            exact hrel a (fun h9 => hgno9 (Or.inr ⟨by simp [hop], h9 ▸ ha⟩))
          | or =>
            simp only [shiftGate, hop, List.map_map, Function.comp_def]
            congr 1
            apply List.map_congr_left
            intro a ha
            exact hrel a (fun h9 => hgno9 (Or.inr ⟨by simp [hop], h9 ▸ ha⟩))
          | mod m =>
            simp only [shiftGate, hop, List.map_map, Function.comp_def]
            congr 1
            apply List.map_congr_left
            intro a ha
            exact hrel a (fun h9 => hgno9 (Or.inr ⟨by simp [hop], h9 ▸ ha⟩))
          | maj =>
            simp only [shiftGate, hop, List.map_map, Function.comp_def]
            congr 1
            apply List.map_congr_left
            intro a ha
            exact hrel a (fun h9 => hgno9 (Or.inr ⟨by simp [hop], h9 ▸ ha⟩))
        apply ih (step w1 g) (step w2 (shiftGate g))
          (fun a ha => hgs' a (List.mem_cons_of_mem g ha))
          (by simp [step, hlen]) (by simp [step]; omega)
        intro i hi
        by_cases hlt : i < w1.length
        · have hlt2 : shiftIdx i < w2.length := by simp only [shiftIdx]; split_ifs <;> omega
          simp only [step, List.getD_eq_getElem?_getD,
            List.getElem?_append_left hlt, List.getElem?_append_left hlt2]
          simpa [List.getD_eq_getElem?_getD] using hrel i hi
        · by_cases heq : i = w1.length
          · subst heq
            have hsh : shiftIdx w1.length = w2.length := by simp only [shiftIdx]; split_ifs <;> omega
            rw [hsh]
            have h1 := atEnd w1 (g.op.eval (g.inputs.map fun j => w1.getD j false))
            have h2 := atEnd w2 ((shiftGate g).op.eval ((shiftGate g).inputs.map fun j => w2.getD j false))
            exact h1.trans (hvaleq.trans h2.symm)
          · have hge1 : (step w1 g).length ≤ i := by simp [step]; omega
            have hge2 : (step w2 (shiftGate g)).length ≤ shiftIdx i := by
              simp only [step, List.length_append, List.length_cons, List.length_nil, shiftIdx]
              split_ifs <;> omega
            rw [List.getD_eq_default _ _ hge1, List.getD_eq_default _ _ hge2]
    have hC'fun : PEqualNP.MetaComplexity.circuitFun 9 C' = f9 := by
      funext y
      have h1 := hC'wires tail (List.ofFn y ++ [y 0 && y 4]) (List.ofFn y) hno9
        (by simp) (by simp)
        (fun i hi => by
          by_cases hlt : i < 9
          · simp only [shiftIdx, hlt, ↓reduceIte, List.getD_eq_getElem?_getD,
              List.getElem?_append_left (by simp; omega : i < (List.ofFn y).length)]
          · have hge1 : (List.ofFn y ++ [y 0 && y 4]).length ≤ i := by simp; omega
            have hge2 : (List.ofFn y).length ≤ shiftIdx i := by simp [shiftIdx, hlt]; omega
            rw [List.getD_eq_default _ _ hge1, List.getD_eq_default _ _ hge2])
        out hout9
      exact h1.symm.trans (eval_tail y)
    have hnorm_v (v : ℕ) (hv : v < 9)
        (ext : (Fin 8 → Bool) → (Fin 9 → Bool))
        (imap : List (Bool ⊕ ℕ))
        (himap_len : imap.length = 9)
        (himap_v : imap.getD v (Sum.inl false) = Sum.inl false)
        (himap_other : ∀ i, i < 9 → i ≠ v → ∃ j, imap.getD i (Sum.inl false) = Sum.inr j ∧ j < 8)
        (hagree0 : ∀ x i, (List.ofFn (ext x)).getD i false = evalS x [] (imap.getD i (Sum.inl false)))
        (hext_f : ∀ x, f9 (ext x) = f8 x)
        (hsep : ∀ u : Fin 9, u.val ≠ v →
          ∃ y0 y1 : Fin 9 → Bool,
            (∀ i : Fin 9, i.val ≠ v → y0 i = y1 i) ∧
            y0 u = true ∧ f9 y0 ≠ f9 y1)
        (hout_v : C'.output ≠ v) :
        ∃ k : ℕ, ∃ g : PEqualNP.CircuitLowerBounds.Gate,
          C'.gates[k]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          (∃ u : ℕ, 9 ≤ u ∧ u < 9 + k ∧ (g.inputs = [v, u] ∨ g.inputs = [u, v])) ∧
          (∀ j : ℕ, ∀ h : PEqualNP.CircuitLowerBounds.Gate,
            j ≠ k → C'.gates[j]? = some h →
            (h.op = PEqualNP.CircuitLowerBounds.GateOp.not → h.inputs.head? ≠ some v) ∧
            (h.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → v ∉ h.inputs)) := by
      have hcomp9 : 13 ≤ (C'.gates.foldl cstep (imap, [])).2.length ∧
          (∀ b : Bool, (C'.gates.foldl cstep (imap, [])).1.getD C'.output (Sum.inl false) ≠ Sum.inl b) := by
        apply no_small_compile C'.gates C'.output (imap, []) hC'fan
          (fun x => List.ofFn (ext x))
        · intro x; simp [himap_len]
        · exact hagree0
        · intro i
          by_cases hlt : i < 9
          · by_cases hiv : i = v
            · subst hiv; rw [himap_v]; trivial
            · obtain ⟨j, hj, hj8⟩ := himap_other i hlt hiv
              rw [hj]; simpa [validS] using hj8
          · rw [List.getD_eq_default _ _ (by dsimp; omega)]; trivial
        · intro g hg; cases hg
        · intro x
          have h := congrFun hC'fun (ext x)
          rw [hext_f x] at h
          exact h
      have hexv : ∃ k : ℕ, ∃ g : PEqualNP.CircuitLowerBounds.Gate, C'.gates[k]? = some g ∧ uses g v := by
        by_contra hno
        push Not at hno
        let u0 : Fin 9 := ⟨if v = 0 then 1 else 0, by split_ifs <;> omega⟩
        have hu0 : u0.val ≠ v := by simp only [u0]; split_ifs <;> omega
        obtain ⟨y0, y1, hyeq, _, hyne⟩ := hsep u0 hu0
        have heq := foldl_indep C'.gates (fun i => i = v) (List.ofFn y0) (List.ofFn y1)
          (by simp)
          (fun i hi => by
            by_cases hlt : i < 9
            · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some]
              exact hyeq ⟨i, hlt⟩ hi
            · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
          (fun i hi => by subst hi; simp [hv])
          (fun g hg i hi hv' => by
            subst hv'
            obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hg
            exact hno k g hk hi)
          C'.output hout_v
        have h0 := congrFun hC'fun y0
        have h1 := congrFun hC'fun y1
        change (C'.gates.foldl step (List.ofFn y0)).getD C'.output false = f9 y0 at h0
        change (C'.gates.foldl step (List.ofFn y1)).getD C'.output false = f9 y1 at h1
        rw [h0, h1] at heq
        exact hyne heq
      obtain ⟨kv, gv, hkv, husev⟩ := hexv
      have hkv_lt : kv < C'.gates.length := by
        by_contra h; rw [List.getElem?_eq_none (by omega)] at hkv; cases hkv
      have hv_elim : (cstep ((C'.gates.take kv).foldl cstep (imap, [])) gv).2.length =
          ((C'.gates.take kv).foldl cstep (imap, [])).2.length := by
        apply uses_inl_elim _ gv (hC'fan gv (List.mem_of_getElem? hkv)) v husev false
        rw [cfold_wmap_kept _ (imap, []) v (by dsimp; omega)]
        exact himap_v
      have hno_other_elim (j : ℕ) (gj : PEqualNP.CircuitLowerBounds.Gate) (hne : j ≠ kv)
          (hj : C'.gates[j]? = some gj)
          (hej : (cstep ((C'.gates.take j).foldl cstep (imap, [])) gj).2.length =
            ((C'.gates.take j).foldl cstep (imap, [])).2.length) : False := by
        have hlen14 : C'.gates.length = 14 := hC'size
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · have h := two_elims_bound C'.gates (imap, []) j kv gj gv hlt hj hkv hej hv_elim
          simp only [List.length_nil, zero_add] at h; omega
        · have h := two_elims_bound C'.gates (imap, []) kv j gv gj hgt hkv hj hv_elim hej
          simp only [List.length_nil, zero_add] at h; omega
      have hno_other_v (j : ℕ) (gj : PEqualNP.CircuitLowerBounds.Gate) (hne : j ≠ kv)
          (hj : C'.gates[j]? = some gj) : ¬ uses gj v := by
        intro hu
        apply hno_other_elim j gj hne hj
        apply uses_inl_elim _ gj (hC'fan gj (List.mem_of_getElem? hj)) v hu false
        rw [cfold_wmap_kept _ (imap, []) v (by dsimp; omega)]
        exact himap_v
      have hgv_not_inl : ∀ b : Bool,
          (cstep ((C'.gates.take kv).foldl cstep (imap, [])) gv).1.getD (9 + kv) (Sum.inl false) ≠ Sum.inl b := by
        intro b hb
        have hfinal : (C'.gates.foldl cstep (imap, [])).1.getD (9 + kv) (Sum.inl false) = Sum.inl b := by
          have hsplit : C'.gates = C'.gates.take kv ++ gv :: C'.gates.drop (kv + 1) := by
            have hget : C'.gates[kv] = gv := by simpa [List.getElem?_eq_getElem hkv_lt] using hkv
            conv_lhs => rw [← List.take_append_drop kv C'.gates]
            rw [List.drop_eq_getElem_cons hkv_lt, hget]
          conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
          rw [cfold_wmap_kept _ _ (9 + kv) (by rw [cstep_wmap_len, cfold_wmap_len]; simp [himap_len]; omega)]
          exact hb
        have hout_ne : C'.output ≠ 9 + kv := fun h => hcomp9.2 b (h ▸ hfinal)
        have hno_read : ∀ j : ℕ, ∀ gj : PEqualNP.CircuitLowerBounds.Gate,
            kv < j → C'.gates[j]? = some gj → ¬ uses gj (9 + kv) := by
          intro j gj hgt hj hu
          apply hno_other_elim j gj (by omega) hj
          apply uses_inl_elim _ gj (hC'fan gj (List.mem_of_getElem? hj)) (9 + kv) hu b
          have hsplitj : C'.gates.take j = C'.gates.take kv ++ gv :: (C'.gates.take j).drop (kv + 1) := by
            have hltj : kv < (C'.gates.take j).length := by simp; omega
            have hget : (C'.gates.take j)[kv] = gv := by
              have : (C'.gates.take j)[kv]? = some gv := by rw [List.getElem?_take_of_lt hgt]; exact hkv
              simpa [List.getElem?_eq_getElem hltj] using this
            conv_lhs => rw [← List.take_append_drop kv (C'.gates.take j)]
            rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hgt), List.drop_eq_getElem_cons hltj, hget]
          rw [hsplitj, List.foldl_append, List.foldl_cons,
            cfold_wmap_kept _ _ (9 + kv) (by rw [cstep_wmap_len, cfold_wmap_len]; simp [himap_len]; omega)]
          exact hb
        let u0 : Fin 9 := ⟨if v = 0 then 1 else 0, by split_ifs <;> omega⟩
        have hu0 : u0.val ≠ v := by simp only [u0]; split_ifs <;> omega
        obtain ⟨y0, y1, hyeq, _, hyne⟩ := hsep u0 hu0
        have hsplit : C'.gates = C'.gates.take kv ++ gv :: C'.gates.drop (kv + 1) := by
          have hget : C'.gates[kv] = gv := by simpa [List.getElem?_eq_getElem hkv_lt] using hkv
          conv_lhs => rw [← List.take_append_drop kv C'.gates]
          rw [List.drop_eq_getElem_cons hkv_lt, hget]
        let p0 := (C'.gates.take kv).foldl step (List.ofFn y0)
        let p1 := (C'.gates.take kv).foldl step (List.ofFn y1)
        have hp0len : p0.length = 9 + kv := by dsimp only [p0]; rw [wlen]; simp; omega
        have hp1len : p1.length = 9 + kv := by dsimp only [p1]; rw [wlen]; simp; omega
        have hpre : ∀ i, i ≠ v → p0.getD i false = p1.getD i false := by
          apply foldl_indep (C'.gates.take kv) (fun i => i = v) (List.ofFn y0) (List.ofFn y1)
          · simp
          · intro i hi
            by_cases hlt : i < 9
            · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some]
              exact hyeq ⟨i, hlt⟩ hi
            · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
          · intro i hi; subst hi; simp [hv]
          · intro g hg i hi hv'; subst hv'
            obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
            have hjlt : j < kv := by
              by_contra h; rw [List.getElem?_eq_none (by simp; omega)] at hj; cases hj
            rw [List.getElem?_take_of_lt hjlt] at hj
            exact hno_other_v j g (by omega) hj hi
        let w0a := step p0 gv
        let w1a := step p1 gv
        have hlen0a : w0a.length = 9 + kv + 1 := by change (p0 ++ [_]).length = 9 + kv + 1; simp [hp0len]
        have hlen1a : w1a.length = 9 + kv + 1 := by change (p1 ++ [_]).length = 9 + kv + 1; simp [hp1len]
        have hpost : ((C'.gates.drop (kv + 1)).foldl step w0a).getD C'.output false =
            ((C'.gates.drop (kv + 1)).foldl step w1a).getD C'.output false := by
          apply foldl_indep (C'.gates.drop (kv + 1)) (fun i => i = v ∨ i = 9 + kv) w0a w1a
          · rw [hlen0a, hlen1a]
          · intro i hi; push Not at hi
            by_cases hlt : i < 9 + kv
            · have hlt0 : i < p0.length := by omega
              have hlt1 : i < p1.length := by omega
              have h0eq : w0a.getD i false = p0.getD i false := by
                change (p0 ++ [_]).getD i false = p0.getD i false
                simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt0]
              have h1eq : w1a.getD i false = p1.getD i false := by
                change (p1 ++ [_]).getD i false = p1.getD i false
                simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt1]
              rw [h0eq, h1eq]
              exact hpre i hi.1
            · rw [List.getD_eq_default _ _ (by rw [hlen0a]; omega),
                  List.getD_eq_default _ _ (by rw [hlen1a]; omega)]
          · intro i hi; rw [hlen0a]; rcases hi with rfl | rfl <;> omega
          · intro g hg i hi hbad
            obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
            rw [List.getElem?_drop] at hj
            rcases hbad with rfl | rfl
            · exact hno_other_v (kv + 1 + j) g (by omega) hj hi
            · exact hno_read (kv + 1 + j) g (by omega) hj hi
          · exact fun h => by rcases h with h | h; exact hout_v h; exact hout_ne h
        have h0 := congrFun hC'fun y0
        have h1 := congrFun hC'fun y1
        change (C'.gates.foldl step (List.ofFn y0)).getD C'.output false = f9 y0 at h0
        change (C'.gates.foldl step (List.ofFn y1)).getD C'.output false = f9 y1 at h1
        rw [hsplit, List.foldl_append, List.foldl_cons] at h0 h1
        change ((C'.gates.drop (kv + 1)).foldl step w0a).getD C'.output false = f9 y0 at h0
        change ((C'.gates.drop (kv + 1)).foldl step w1a).getD C'.output false = f9 y1 at h1
        rw [h0, h1] at hpost
        exact hyne hpost
      let stv := (C'.gates.take kv).foldl cstep (imap, [])
      have hstlen : stv.1.length = 9 + kv := by
        dsimp only [stv]; rw [cfold_wmap_len]; simp [himap_len]; omega
      have hgetv : stv.1.getD v (Sum.inl false) = Sum.inl false := by
        dsimp only [stv]; rw [cfold_wmap_kept _ (imap, []) v (by dsimp; omega)]; exact himap_v
      have hatv (s : Bool ⊕ ℕ) : (stv.1 ++ [s]).getD (9 + kv) (Sum.inl false) = s := by
        rw [← hstlen]; simp [List.getD_eq_getElem?_getD]
      have hgv_form : gv.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          ∃ u : ℕ, u < 9 + kv ∧ u ≠ v ∧ (gv.inputs = [v, u] ∨ gv.inputs = [u, v]) := by
        obtain ⟨hopset, hlen2⟩ := hC'fan gv (List.mem_of_getElem? hkv)
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hopset
        have hni : ∀ b : Bool, (cstep stv gv).1.getD (9 + kv) (Sum.inl false) ≠ Sum.inl b := hgv_not_inl
        rcases gv with ⟨opv, insv⟩
        rcases hopset with rfl | rfl | rfl
        · have hiv : v ∈ insv := uses_mem (fun h => by cases h) husev
          rcases insv with _ | ⟨a, _ | ⟨c, _ | _⟩⟩
          · simp at hiv
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hiv; subst hiv
            exact (hni false (by dsimp only [cstep]; rw [hgetv]; exact hatv _)).elim
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hiv
            rcases hiv with rfl | rfl
            · exact (hni false (by dsimp only [cstep]; rw [hgetv]; exact hatv _)).elim
            · exfalso
              cases ha : stv.1.getD a (Sum.inl false) with
              | inl ba => cases ba <;> exact hni false (by dsimp only [cstep]; rw [ha, hgetv]; exact hatv _)
              | inr ia => exact hni false (by dsimp only [cstep]; rw [ha, hgetv]; exact hatv _)
          · simp at hlen2
        · refine ⟨rfl, ?_⟩
          have hiv : v ∈ insv := uses_mem (fun h => by cases h) husev
          rcases insv with _ | ⟨a, _ | ⟨c, _ | _⟩⟩
          · simp at hiv
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hiv; subst hiv
            exact (hni false (by dsimp only [cstep]; rw [hgetv]; exact hatv _)).elim
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hiv
            rcases hiv with rfl | rfl
            · cases hc : stv.1.getD c (Sum.inl false) with
              | inl bc =>
                cases bc <;> exact (hni _ (by dsimp only [cstep]; rw [hgetv, hc]; exact hatv _)).elim
              | inr ic =>
                have hclt : c < 9 + kv := by
                  by_contra hge
                  rw [List.getD_eq_default _ _ (by omega)] at hc; cases hc
                have hcne : c ≠ v := fun h => by subst h; rw [hgetv] at hc; cases hc
                exact ⟨c, hclt, hcne, Or.inl rfl⟩
            · cases ha : stv.1.getD a (Sum.inl false) with
              | inl ba =>
                cases ba with
                | true => exact (hni true (by dsimp only [cstep]; rw [ha]; exact hatv _)).elim
                | false => exact (hni false (by dsimp only [cstep]; rw [ha, hgetv]; exact hatv _)).elim
              | inr ia =>
                have halt : a < 9 + kv := by
                  by_contra hge
                  rw [List.getD_eq_default _ _ (by omega)] at ha; cases ha
                have hane : a ≠ v := fun h => by subst h; rw [hgetv] at ha; cases ha
                exact ⟨a, halt, hane, Or.inr rfl⟩
          · simp at hlen2
        · have hiv : insv.head? = some v := uses_head rfl husev
          rcases insv with _ | ⟨a, tl⟩
          · simp at hiv
          · simp only [List.head?_cons, Option.some.injEq] at hiv; subst hiv
            exact (hni true (by dsimp only [cstep]; rw [hgetv]; exact hatv _)).elim
      obtain ⟨hgv_or, u, hult, hune, hgv_ins⟩ := hgv_form
      have hu9 : 9 ≤ u := by
        by_contra hlt9
        have hlt9' : u < 9 := by omega
        obtain ⟨y0, y1, hyeq, hyu, hyne⟩ := hsep ⟨u, hlt9'⟩ hune
        have hy1u : y1 ⟨u, hlt9'⟩ = true := (hyeq ⟨u, hlt9'⟩ hune).symm.trans hyu
        have hsplit : C'.gates = C'.gates.take kv ++ gv :: C'.gates.drop (kv + 1) := by
          have hget : C'.gates[kv] = gv := by simpa [List.getElem?_eq_getElem hkv_lt] using hkv
          conv_lhs => rw [← List.take_append_drop kv C'.gates]
          rw [List.drop_eq_getElem_cons hkv_lt, hget]
        let p0 := (C'.gates.take kv).foldl step (List.ofFn y0)
        let p1 := (C'.gates.take kv).foldl step (List.ofFn y1)
        have hp0len : p0.length = 9 + kv := by dsimp only [p0]; rw [wlen]; simp; omega
        have hp1len : p1.length = 9 + kv := by dsimp only [p1]; rw [wlen]; simp; omega
        have hpre : ∀ i, i ≠ v → p0.getD i false = p1.getD i false := by
          apply foldl_indep (C'.gates.take kv) (fun i => i = v) (List.ofFn y0) (List.ofFn y1)
          · simp
          · intro i hi
            by_cases hlt : i < 9
            · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some]
              exact hyeq ⟨i, hlt⟩ hi
            · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
          · intro i hi; subst hi; simp [hv]
          · intro g hg i hi hv'; subst hv'
            obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
            have hjlt : j < kv := by
              by_contra h; rw [List.getElem?_eq_none (by simp; omega)] at hj; cases hj
            rw [List.getElem?_take_of_lt hjlt] at hj
            exact hno_other_v j g (by omega) hj hi
        have hget_u0 : p0.getD u false = true := by
          dsimp only [p0]; rw [kept _ _ u (by simp [hlt9'])]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt9', ↓reduceDIte, Option.getD_some]
          exact hyu
        have hget_u1 : p1.getD u false = true := by
          dsimp only [p1]; rw [kept _ _ u (by simp [hlt9'])]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt9', ↓reduceDIte, Option.getD_some]
          exact hy1u
        have hgv_eq :
            gv.op.eval (gv.inputs.map fun i => p0.getD i false) =
            gv.op.eval (gv.inputs.map fun i => p1.getD i false) := by
          rcases hgv_ins with h | h
          · rw [hgv_or, h]
            change (p0.getD v false || (p0.getD u false || false)) =
              (p1.getD v false || (p1.getD u false || false))
            rw [hget_u0, hget_u1]
            simp only [Bool.true_or, Bool.or_true]
          · rw [hgv_or, h]
            change (p0.getD u false || (p0.getD v false || false)) =
              (p1.getD u false || (p1.getD v false || false))
            rw [hget_u0, hget_u1]
            simp only [Bool.true_or]
        let w0a := step p0 gv
        let w1a := step p1 gv
        have hlen0a : w0a.length = 9 + kv + 1 := by change (p0 ++ [_]).length = 9 + kv + 1; simp [hp0len]
        have hlen1a : w1a.length = 9 + kv + 1 := by change (p1 ++ [_]).length = 9 + kv + 1; simp [hp1len]
        have hpost : ((C'.gates.drop (kv + 1)).foldl step w0a).getD C'.output false =
            ((C'.gates.drop (kv + 1)).foldl step w1a).getD C'.output false := by
          apply foldl_indep (C'.gates.drop (kv + 1)) (fun i => i = v) w0a w1a
          · rw [hlen0a, hlen1a]
          · intro i hi
            by_cases hlt : i < 9 + kv
            · have hlt0 : i < p0.length := by omega
              have hlt1 : i < p1.length := by omega
              have h0eq : w0a.getD i false = p0.getD i false := by
                change (p0 ++ [_]).getD i false = p0.getD i false
                simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt0]
              have h1eq : w1a.getD i false = p1.getD i false := by
                change (p1 ++ [_]).getD i false = p1.getD i false
                simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt1]
              rw [h0eq, h1eq]
              exact hpre i hi
            · by_cases heq : i = 9 + kv
              · subst heq
                have ha0 : w0a.getD (9 + kv) false = gv.op.eval (gv.inputs.map fun j => p0.getD j false) := by
                  rw [← hp0len]; exact atEnd p0 _
                have ha1 : w1a.getD (9 + kv) false = gv.op.eval (gv.inputs.map fun j => p1.getD j false) := by
                  rw [← hp1len]; exact atEnd p1 _
                exact ha0.trans (hgv_eq.trans ha1.symm)
              · rw [List.getD_eq_default _ _ (by rw [hlen0a]; omega),
                    List.getD_eq_default _ _ (by rw [hlen1a]; omega)]
          · intro i hi; subst hi; rw [hlen0a]; omega
          · intro g hg i hi hv'; subst hv'
            obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
            rw [List.getElem?_drop] at hj
            exact hno_other_v (kv + 1 + j) g (by omega) hj hi
          · exact hout_v
        have h0 := congrFun hC'fun y0
        have h1 := congrFun hC'fun y1
        change (C'.gates.foldl step (List.ofFn y0)).getD C'.output false = f9 y0 at h0
        change (C'.gates.foldl step (List.ofFn y1)).getD C'.output false = f9 y1 at h1
        rw [hsplit, List.foldl_append, List.foldl_cons] at h0 h1
        change ((C'.gates.drop (kv + 1)).foldl step w0a).getD C'.output false = f9 y0 at h0
        change ((C'.gates.drop (kv + 1)).foldl step w1a).getD C'.output false = f9 y1 at h1
        rw [h0, h1] at hpost
        exact hyne hpost
      refine ⟨kv, gv, hkv, hgv_or, ⟨u, hu9, hult, hgv_ins⟩, ?_⟩
      intro j hj hne hget
      have hno := hno_other_v j hj hne hget
      exact ⟨fun hop hhead => hno (Or.inl ⟨hop, hhead⟩), fun hop hmem => hno (Or.inr ⟨hop, hmem⟩)⟩
    apply h_norm14 C' hC'fan hC'size hC'fun
    intro v hv
    rcases hv with rfl | rfl | rfl
    · let imap4 : List (Bool ⊕ ℕ) :=
        [Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl false,
         Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7]
      apply hnorm_v 4 (by omega) ext4 imap4 rfl rfl
        (fun i hi hne => by rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> first | (simp [imap4] at hi hne ⊢; done) | omega)
        (fun x i => by rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [imap4, ext4, evalS, List.ofFn_succ])
        ext4_f
        (fun u hu => by
          fin_cases u
          · exact ⟨![true, false, false, false, false, false, false, false, false],
              ![true, false, false, false, true, false, false, false, false],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩
          · exact ⟨![false, true, false, true, false, false, false, false, false],
              ![false, true, false, true, true, false, false, false, false],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩
          · exact ⟨![true, false, true, false, false, false, false, false, false],
              ![true, false, true, false, true, false, false, false, false],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩
          · exact ⟨![false, false, false, true, false, false, false, false, false],
              ![false, false, false, true, true, false, false, false, false],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩
          · simp at hu
          · exact ⟨![false, false, false, true, false, true, false, false, false],
              ![false, false, false, true, true, true, false, false, false],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩
          · exact ⟨![true, false, false, false, false, false, true, false, false],
              ![true, false, false, false, true, false, true, false, false],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩
          · exact ⟨![true, false, false, false, false, false, false, true, false],
              ![true, false, false, false, true, false, false, true, false],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩
          · exact ⟨![true, false, false, false, false, false, false, false, true],
              ![true, false, false, false, true, false, false, false, true],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩)
        (fun h => by
          have h1 := congrFun hC'fun ![false, false, false, false, true, false, false, false, false]
          change (C'.gates.foldl step _).getD C'.output false = _ at h1
          rw [h, kept C'.gates _ 4 (by simp)] at h1
          simp [f9, List.ofFn_succ] at h1)
    · let ext6 : (Fin 8 → Bool) → (Fin 9 → Bool) := fun x => ![x 4, x 0, x 1, x 2, x 6, x 7, false, x 5, x 3]
      let imap6 : List (Bool ⊕ ℕ) :=
        [Sum.inr 4, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 6, Sum.inr 7,
         Sum.inl false, Sum.inr 5, Sum.inr 3]
      have ext6_f : ∀ x : Fin 8 → Bool, f9 (ext6 x) = f8 x := by
        intro x
        have h : ∀ a b c d e f g h : Bool,
            f9 ![e, a, b, c, g, h, false, f, d] = f8 ![a, b, c, d, e, f, g, h] := by decide
        have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
          funext i; fin_cases i <;> rfl
        have h6 : ext6 x = ![x 4, x 0, x 1, x 2, x 6, x 7, false, x 5, x 3] := rfl
        rw [h6, h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7), ← hx]
      apply hnorm_v 6 (by omega) ext6 imap6 rfl rfl
        (fun i hi hne => by rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> first | (simp [imap6] at hi hne ⊢; done) | omega)
        (fun x i => by rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [imap6, ext6, evalS, List.ofFn_succ])
        ext6_f
        (fun u hu => by
          fin_cases u
          · exact ⟨![true, false, false, false, false, false, false, false, true],
              ![true, false, false, false, false, false, true, false, true],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩
          · exact ⟨![false, true, false, false, false, false, false, false, false],
              ![false, true, false, false, false, false, true, false, false],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩
          · exact ⟨![false, false, true, false, false, false, false, false, true],
              ![false, false, true, false, false, false, true, false, true],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩
          · exact ⟨![false, true, false, true, false, false, false, false, false],
              ![false, true, false, true, false, false, true, false, false],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩
          · exact ⟨![false, true, false, false, true, false, false, false, false],
              ![false, true, false, false, true, false, true, false, false],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩
          · exact ⟨![false, true, false, false, false, true, false, false, false],
              ![false, true, false, false, false, true, true, false, false],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩
          · simp at hu
          · exact ⟨![false, true, false, false, false, false, false, true, false],
              ![false, true, false, false, false, false, true, true, false],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩
          · exact ⟨![false, false, false, false, false, false, false, false, true],
              ![false, false, false, false, false, false, true, false, true],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩)
        (fun h => by
          have h1 := congrFun hC'fun ![false, false, false, false, false, false, true, false, false]
          change (C'.gates.foldl step _).getD C'.output false = _ at h1
          rw [h, kept C'.gates _ 6 (by simp)] at h1
          simp [f9, List.ofFn_succ] at h1)
    · let ext7 : (Fin 8 → Bool) → (Fin 9 → Bool) := fun x => ![x 7, x 4, x 0, x 1, x 5, x 3, x 6, false, x 2]
      let imap7 : List (Bool ⊕ ℕ) :=
        [Sum.inr 7, Sum.inr 4, Sum.inr 0, Sum.inr 1, Sum.inr 5, Sum.inr 3,
         Sum.inr 6, Sum.inl false, Sum.inr 2]
      have ext7_f : ∀ x : Fin 8 → Bool, f9 (ext7 x) = f8 x := by
        intro x
        have h : ∀ a b c d e f g h : Bool,
            f9 ![h, e, a, b, f, d, g, false, c] = f8 ![a, b, c, d, e, f, g, h] := by decide
        have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
          funext i; fin_cases i <;> rfl
        have h7 : ext7 x = ![x 7, x 4, x 0, x 1, x 5, x 3, x 6, false, x 2] := rfl
        rw [h7, h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7), ← hx]
      apply hnorm_v 7 (by omega) ext7 imap7 rfl rfl
        (fun i hi hne => by rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> first | (simp [imap7] at hi hne ⊢; done) | omega)
        (fun x i => by rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [imap7, ext7, evalS, List.ofFn_succ])
        ext7_f
        (fun u hu => by
          fin_cases u
          · exact ⟨![true, false, true, false, false, false, false, false, false],
              ![true, false, true, false, false, false, false, true, false],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩
          · exact ⟨![false, true, false, false, false, true, false, false, false],
              ![false, true, false, false, false, true, false, true, false],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩
          · exact ⟨![false, false, true, false, false, false, false, false, false],
              ![false, false, true, false, false, false, false, true, false],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩
          · exact ⟨![false, false, false, true, false, true, false, false, false],
              ![false, false, false, true, false, true, false, true, false],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩
          · exact ⟨![false, false, true, false, true, false, false, false, false],
              ![false, false, true, false, true, false, false, true, false],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩
          · exact ⟨![false, false, false, false, false, true, false, false, false],
              ![false, false, false, false, false, true, false, true, false],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩
          · exact ⟨![false, false, true, false, false, false, true, false, false],
              ![false, false, true, false, false, false, true, true, false],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩
          · simp at hu
          · exact ⟨![false, false, true, false, false, false, false, false, true],
              ![false, false, true, false, false, false, false, true, true],
              fun i hi => by fin_cases i <;> simp at hi ⊢, by decide, by decide⟩)
        (fun h => by
          have h1 := congrFun hC'fun ![false, false, false, false, false, false, false, true, false]
          change (C'.gates.foldl step _).getD C'.output false = _ at h1
          rw [h, kept C'.gates _ 7 (by simp)] at h1
          simp [f9, List.ofFn_succ] at h1)
