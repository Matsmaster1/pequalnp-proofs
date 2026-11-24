import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_3124

def F (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
    x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def E : List (Fin 9 × Fin 9) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]

def ind (u v : Fin 9) : Fin 9 → Bool := fun k => decide (k = u) || decide (k = v)

theorem avoid : ∀ a b c d : Fin 9, ∃ e ∈ E,
    (e.1 ≠ a ∧ e.1 ≠ b ∧ e.1 ≠ c ∧ e.1 ≠ d) ∧ (e.2 ≠ a ∧ e.2 ≠ b ∧ e.2 ≠ c ∧ e.2 ≠ d) := by
  decide +kernel

theorem F_edge : ∀ e ∈ E, F (ind e.1 e.2) = true := by
  decide +kernel

theorem F_zero : F (fun _ => false) = false := by
  decide

def base (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [!x 0]

def zv (A : List ℕ) (x : Fin 9 → Bool) : Bool :=
  GateOp.or.eval (A.map fun i => (base x).getD i false)

def inp (A : List ℕ) (x : Fin 9 → Bool) : List Bool := base x ++ [zv A x]

def r (i : ℕ) : Fin 9 := if h : i < 9 then ⟨i, h⟩ else 0

def D (A : List ℕ) (i : ℕ) : Fin 9 × Fin 9 :=
  if i = 10 then (r (A.getD 0 0), r (A.getD 1 0)) else (r i, r i)

theorem base_len (x : Fin 9 → Bool) : (base x).length = 10 := by
  simp [base]

theorem base_get (x y : Fin 9 → Bool) (i : ℕ) (h : x (r i) = y (r i)) :
    (base x).getD i false = (base y).getD i false := by
  by_cases h9 : i < 9
  · have hr : r i = ⟨i, h9⟩ := by simp [r, h9]
    rw [hr] at h
    simp only [base]
    rw [List.getD_append _ _ _ _ (by simpa using h9), List.getD_append _ _ _ _ (by simpa using h9),
      List.getD_eq_getElem _ _ (by simpa using h9), List.getD_eq_getElem _ _ (by simpa using h9),
      List.getElem_ofFn, List.getElem_ofFn]
    exact h
  · by_cases h10 : i = 9
    · subst h10
      have hr : r 9 = 0 := by simp [r]
      rw [hr] at h
      simp [base, h]
    · rw [List.getD_eq_default _ _ (by rw [base_len]; omega),
        List.getD_eq_default _ _ (by rw [base_len]; omega)]

theorem zv_eq (A : List ℕ) (hA : A.length ≤ 2) (x y : Fin 9 → Bool)
    (h1 : x (r (A.getD 0 0)) = y (r (A.getD 0 0)))
    (h2 : x (r (A.getD 1 0)) = y (r (A.getD 1 0))) : zv A x = zv A y := by
  rcases A with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · rfl
  · simp only [List.getD_cons_zero] at h1
    simp only [zv, List.map_cons, List.map_nil]
    rw [base_get x y a h1]
  · simp only [List.getD_cons_zero, List.getD_cons_succ] at h1 h2
    simp only [zv, List.map_cons, List.map_nil]
    rw [base_get x y a h1, base_get x y b h2]
  · simp at hA

theorem inp_get (A : List ℕ) (hA : A.length ≤ 2) (x y : Fin 9 → Bool) (i : ℕ)
    (h1 : x (D A i).1 = y (D A i).1) (h2 : x (D A i).2 = y (D A i).2) :
    (inp A x).getD i false = (inp A y).getD i false := by
  by_cases hi : i < 10
  · have hD : D A i = (r i, r i) := by simp [D]; omega
    rw [hD] at h1
    simp only [inp]
    rw [List.getD_append _ _ _ _ (by rw [base_len]; exact hi),
      List.getD_append _ _ _ _ (by rw [base_len]; exact hi)]
    exact base_get x y i h1
  · by_cases h10 : i = 10
    · subst h10
      simp only [D, ite_true] at h1 h2
      have hz := zv_eq A hA x y h1 h2
      simp [inp, base_len, hz]
    · rw [List.getD_eq_default _ _ (by simp [inp, base_len]; omega),
        List.getD_eq_default _ _ (by simp [inp, base_len]; omega)]

theorem wires_nil (C : Circuit) (h : C.gates = []) (w : List Bool) : C.wires w = w := by
  simp [Circuit.wires, h]

theorem wires_one (C : Circuit) (g : Gate) (h : C.gates = [g]) (w : List Bool) :
    C.wires w = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
  simp [Circuit.wires, h]

theorem gate_eq (A : List ℕ) (hA : A.length ≤ 2) (g : Gate) (hg : g.inputs.length ≤ 2)
    (x y : Fin 9 → Bool)
    (h : ∀ k ∈ [(D A (g.inputs.getD 0 0)).1, (D A (g.inputs.getD 0 0)).2,
      (D A (g.inputs.getD 1 0)).1, (D A (g.inputs.getD 1 0)).2], x k = y k) :
    (g.inputs.map fun i => (inp A x).getD i false) =
      (g.inputs.map fun i => (inp A y).getD i false) := by
  rcases g with ⟨op, ins⟩
  simp only at hg h ⊢
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · rfl
  · simp only [List.getD_cons_zero] at h
    simp only [List.map_cons, List.map_nil]
    rw [inp_get A hA x y a (h _ (by simp)) (h _ (by simp))]
  · simp only [List.getD_cons_zero, List.getD_cons_succ] at h
    simp only [List.map_cons, List.map_nil]
    rw [inp_get A hA x y a (h _ (by simp)) (h _ (by simp)),
      inp_get A hA x y b (h _ (by simp)) (h _ (by simp))]
  · simp at hg

theorem len_le_one (C : Circuit) (h : ¬∃ g : Gate, C.gates[1]? = some g) :
    C.gates = [] ∨ ∃ g, C.gates = [g] := by
  rcases hC : C.gates with _ | ⟨g, _ | ⟨g', t⟩⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨g, rfl⟩
  · exact absurd ⟨g', by simp [hC]⟩ h

theorem same_out (A : List ℕ) (hA : A.length ≤ 2) (C : Circuit) (hC : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (h1 : ¬∃ g : Gate, C.gates[1]? = some g) :
    ∃ a b c d : Fin 9, ∀ x y : Fin 9 → Bool,
      x a = y a → x b = y b → x c = y c → x d = y d → C.eval (inp A x) = C.eval (inp A y) := by
  rcases len_le_one C h1 with h0 | ⟨g, hg⟩
  · refine ⟨(D A C.output).1, (D A C.output).2, 0, 0, fun x y ha hb _ _ => ?_⟩
    simp only [Circuit.eval, wires_nil C h0]
    exact inp_get A hA x y C.output ha hb
  · have hgl : g.inputs.length ≤ 2 := hC g (by simp [hg])
    by_cases ho : C.output = 11
    · refine ⟨(D A (g.inputs.getD 0 0)).1, (D A (g.inputs.getD 0 0)).2,
        (D A (g.inputs.getD 1 0)).1, (D A (g.inputs.getD 1 0)).2, fun x y ha hb hc hd => ?_⟩
      have hm := gate_eq A hA g hgl x y (by simp; exact ⟨ha, hb, hc, hd⟩)
      have hl : ∀ z, (inp A z).length = 11 := fun z => by simp [inp, base_len]
      simp only [Circuit.eval, wires_one C g hg, ho]
      rw [List.getD_append_right _ _ _ _ (by rw [hl]), List.getD_append_right _ _ _ _ (by rw [hl])]
      simp only [hl, Nat.sub_self, List.getD_cons_zero]
      rw [hm]
    · refine ⟨(D A C.output).1, (D A C.output).2, 0, 0, fun x y ha hb _ _ => ?_⟩
      have hl : ∀ z, (inp A z).length = 11 := fun z => by simp [inp, base_len]
      simp only [Circuit.eval, wires_one C g hg]
      by_cases hlt : C.output < 11
      · rw [List.getD_append _ _ _ _ (by rw [hl]; exact hlt),
          List.getD_append _ _ _ _ (by rw [hl]; exact hlt)]
        exact inp_get A hA x y C.output ha hb
      · rw [List.getD_eq_default _ _ (by simp [hl]; omega),
          List.getD_eq_default _ _ (by simp [hl]; omega)]

end PEqualNP.Outside.L_meta_3124

theorem PEqualNP.Outside.L_meta_3124 : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (¬∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[(1 : ℕ)]? = Option.some x6) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro A hA C hC _ h1
  obtain ⟨a, b, c, d, hsame⟩ := PEqualNP.Outside.L_meta_3124.same_out A hA C
    (fun g hg => (hC g hg).2) h1
  obtain ⟨e, he, ⟨h1a, h1b, h1c, h1d⟩, ⟨h2a, h2b, h2c, h2d⟩⟩ :=
    PEqualNP.Outside.L_meta_3124.avoid a b c d
  have hF := PEqualNP.Outside.L_meta_3124.F_edge e he
  let z : Fin 9 → Bool := fun _ => false
  let w := PEqualNP.Outside.L_meta_3124.ind e.1 e.2
  have agree : ∀ k : Fin 9, k ≠ e.1 → k ≠ e.2 → z k = w k := by
    intro k hk1 hk2
    simp [z, w, PEqualNP.Outside.L_meta_3124.ind, hk1, hk2]
  have heq : C.eval (PEqualNP.Outside.L_meta_3124.inp A z) =
      C.eval (PEqualNP.Outside.L_meta_3124.inp A w) :=
    hsame z w (agree a (Ne.symm h1a) (Ne.symm h2a)) (agree b (Ne.symm h1b) (Ne.symm h2b))
      (agree c (Ne.symm h1c) (Ne.symm h2c)) (agree d (Ne.symm h1d) (Ne.symm h2d))
  by_cases hz : C.eval (PEqualNP.Outside.L_meta_3124.inp A z) = PEqualNP.Outside.L_meta_3124.F z
  · refine ⟨w, ?_⟩
    show C.eval (PEqualNP.Outside.L_meta_3124.inp A w) ≠ PEqualNP.Outside.L_meta_3124.F w
    rw [← heq, hz, PEqualNP.Outside.L_meta_3124.F_zero, hF]
    simp
  · exact ⟨z, hz⟩
