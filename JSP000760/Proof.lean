import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
import Mathlib.Data.Set.Card
import Mathlib.Tactic

open SimpleGraph

attribute [local instance] Classical.decEq

local instance : DecidableRel (completeBipartiteGraph (Fin 3) (Fin 3)).Adj :=
  fun u v ↦ inferInstanceAs
    (Decidable (u.isLeft ∧ v.isRight ∨ u.isRight ∧ v.isLeft))

example : (completeGraph (Fin 3)).edgeFinset.card = 3 := by
  rw [card_edgeFinset_top_eq_card_choose_two]
  decide

example : (completeBipartiteGraph (Fin 3) (Fin 3)).edgeFinset.card = 9 := by
  rw [edgeFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  rw [edgeSet_completeBipartiteGraph, Set.ncard_range_of_injective]
  · rw [Nat.card_eq_fintype_card, Fintype.card_prod]
    decide
  · grind [Function.Injective]

variable {V : Type*} [Fintype V] [DecidableEq V]

def edgeSetOn (G : SimpleGraph V) (s : Finset V) : Set (Sym2 V) :=
  G.edgeSet ∩ (s : Set V).sym2

theorem ncard_edgeSetOn (G : SimpleGraph V) (s : Finset V) :
    (edgeSetOn G s).ncard = (G.induce (s : Set V)).edgeSet.ncard := by
  classical
  let f : Sym2 (s : Set V) → Sym2 V :=
    (Function.Embedding.subtype (fun x ↦ x ∈ (s : Set V))).sym2Map
  have hf : Function.Injective f :=
    (Function.Embedding.subtype (fun x ↦ x ∈ (s : Set V))).sym2Map.injective
  have hset : edgeSetOn G s = f '' (G.induce (s : Set V)).edgeSet := by
    ext ⟨u, v⟩
    constructor
    · rintro ⟨huv, hu, hv⟩
      refine ⟨s(⟨u, hu⟩, ⟨v, hv⟩), huv, ?_⟩
      rfl
    · rintro ⟨z, hz, hez⟩
      obtain ⟨u', v'⟩ := z
      change s((u' : V), (v' : V)) = s(u, v) at hez
      rw [Sym2.eq_iff] at hez
      rcases hez with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · subst u
        subst v
        exact ⟨hz, u'.property, v'.property⟩
      · subst u
        subst v
        exact ⟨hz.symm, v'.property, u'.property⟩
  rw [hset, Set.ncard_image_of_injective _ hf]

inductive IsCockadeOn (G : SimpleGraph V) : Finset V → Prop
  | triangle {s : Finset V}
      (e : G.induce (s : Set V) ≃g completeGraph (Fin 3)) : IsCockadeOn G s
  | k33 {s : Finset V}
      (e : G.induce (s : Set V) ≃g completeBipartiteGraph (Fin 3) (Fin 3)) : IsCockadeOn G s
  | glue {a b : Finset V} {x y : V}
      (ha : IsCockadeOn G a) (hb : IsCockadeOn G b)
      (hxy : x ≠ y) (hi : a ∩ b = {x, y}) (hadj : G.Adj x y)
      (hnocross : ∀ {u v}, u ∈ a ∪ b → v ∈ a ∪ b → G.Adj u v →
        (u ∈ a ∧ v ∈ a) ∨ (u ∈ b ∧ v ∈ b)) : IsCockadeOn G (a ∪ b)

omit [Fintype V] in
theorem edgeSetOn_union_of_noCross (G : SimpleGraph V) (a b : Finset V)
    (hnocross : ∀ {u v}, u ∈ a ∪ b → v ∈ a ∪ b → G.Adj u v →
      (u ∈ a ∧ v ∈ a) ∨ (u ∈ b ∧ v ∈ b)) :
    edgeSetOn G (a ∪ b) = edgeSetOn G a ∪ edgeSetOn G b := by
  ext ⟨u, v⟩
  simp only [edgeSetOn, Set.mem_inter_iff, mem_edgeSet, Set.mk_mem_sym2_iff,
    Finset.mem_union, Set.mem_union]
  constructor
  · rintro ⟨huv, hu, hv⟩
    exact (hnocross hu hv huv).imp (⟨huv, ·⟩) (⟨huv, ·⟩)
  · rintro (⟨huv, hu, hv⟩ | ⟨huv, hu, hv⟩)
    · exact ⟨huv, Finset.mem_union.mpr (Or.inl hu), Finset.mem_union.mpr (Or.inl hv)⟩
    · exact ⟨huv, Finset.mem_union.mpr (Or.inr hu), Finset.mem_union.mpr (Or.inr hv)⟩

omit [Fintype V] in
theorem edgeSetOn_inter_eq_singleton (G : SimpleGraph V) (a b : Finset V) {x y : V}
    (hxy : x ≠ y) (hi : a ∩ b = {x, y}) (hadj : G.Adj x y) :
    edgeSetOn G a ∩ edgeSetOn G b = {s(x, y)} := by
  ext ⟨u, v⟩
  simp only [edgeSetOn, Set.mem_inter_iff, mem_edgeSet, Set.mk_mem_sym2_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨huv, hua, hva⟩, _, hub, hvb⟩
    have hu : u = x ∨ u = y := by
      have : u ∈ ({x, y} : Finset V) := hi ▸ Finset.mem_inter.mpr ⟨hua, hub⟩
      simpa using this
    have hv : v = x ∨ v = y := by
      have : v ∈ ({x, y} : Finset V) := hi ▸ Finset.mem_inter.mpr ⟨hva, hvb⟩
      simpa using this
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (G.loopless.irrefl _ huv).elim
    · rfl
    · exact Sym2.eq_swap
    · exact (G.loopless.irrefl _ huv).elim
  · intro huv
    rw [Sym2.eq_iff] at huv
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hmem : (u ∈ a ∩ b) ∧ (v ∈ a ∩ b) := by
        rw [hi]
        simp
      have huab := Finset.mem_inter.mp hmem.1
      have hvab := Finset.mem_inter.mp hmem.2
      exact ⟨⟨hadj, huab.1, hvab.1⟩, hadj, huab.2, hvab.2⟩
    · have hmem : (u ∈ a ∩ b) ∧ (v ∈ a ∩ b) := by
        rw [hi]
        simp
      have huab := Finset.mem_inter.mp hmem.1
      have hvab := Finset.mem_inter.mp hmem.2
      exact ⟨⟨hadj.symm, huab.1, hvab.1⟩, hadj.symm, huab.2, hvab.2⟩

theorem ncard_edgeSet_completeGraph_fin_three :
    (completeGraph (Fin 3)).edgeSet.ncard = 3 := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, ← edgeFinset_card,
    card_edgeFinset_top_eq_card_choose_two]
  decide

theorem ncard_edgeSet_completeBipartite_fin_three :
    (completeBipartiteGraph (Fin 3) (Fin 3)).edgeSet.ncard = 9 := by
  rw [edgeSet_completeBipartiteGraph, Set.ncard_range_of_injective]
  · rw [Nat.card_eq_fintype_card, Fintype.card_prod]
    decide
  · grind [Function.Injective]

theorem IsCockadeOn.card_and_edgeSetOn {G : SimpleGraph V} {s : Finset V}
    (h : IsCockadeOn G s) :
    3 ≤ s.card ∧ (edgeSetOn G s).ncard = 2 * s.card - 3 := by
  induction h
  case triangle t e =>
      have hv : t.card = 3 := by
        calc
          t.card = (t : Set V).ncard := by simp
          _ = Nat.card (t : Set V) := (Nat.card_coe_set_eq _).symm
          _ = Nat.card (Fin 3) := Nat.card_congr e.toEquiv
          _ = 3 := by simp
      have he : (G.induce (t : Set V)).edgeSet.ncard = 3 := by
        calc
          _ = Nat.card (G.induce (t : Set V)).edgeSet := (Nat.card_coe_set_eq _).symm
          _ = Nat.card (completeGraph (Fin 3)).edgeSet := Nat.card_congr e.mapEdgeSet
          _ = (completeGraph (Fin 3)).edgeSet.ncard := Nat.card_coe_set_eq _
          _ = 3 := ncard_edgeSet_completeGraph_fin_three
      rw [ncard_edgeSetOn, hv, he]
      omega
  case k33 t e =>
      have hv : t.card = 6 := by
        calc
          t.card = (t : Set V).ncard := by simp
          _ = Nat.card (t : Set V) := (Nat.card_coe_set_eq _).symm
          _ = Nat.card (Fin 3 ⊕ Fin 3) := Nat.card_congr e.toEquiv
          _ = 6 := by simp
      have he : (G.induce (t : Set V)).edgeSet.ncard = 9 := by
        calc
          _ = Nat.card (G.induce (t : Set V)).edgeSet := (Nat.card_coe_set_eq _).symm
          _ = Nat.card (completeBipartiteGraph (Fin 3) (Fin 3)).edgeSet :=
            Nat.card_congr e.mapEdgeSet
          _ = (completeBipartiteGraph (Fin 3) (Fin 3)).edgeSet.ncard := Nat.card_coe_set_eq _
          _ = 9 := ncard_edgeSet_completeBipartite_fin_three
      rw [ncard_edgeSetOn, hv, he]
      omega
  case glue a b x y ha hb hxy hi hadj hnocross iha ihb =>
      have hi_card : (a ∩ b).card = 2 := by simp [hi, hxy]
      have hab_card := Finset.card_union_add_card_inter a b
      have hedges_union := edgeSetOn_union_of_noCross G a b hnocross
      have hedges_inter := edgeSetOn_inter_eq_singleton G a b hxy hi hadj
      have hedges_card := Set.ncard_union_add_ncard_inter (edgeSetOn G a) (edgeSetOn G b)
      rw [← hedges_union, hedges_inter, Set.ncard_singleton] at hedges_card
      constructor <;> omega

def IsTwoConnectedOn (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ {r u v}, u ∈ s → v ∈ s → u ≠ r → v ≠ r →
    ∃ p : G.Walk u v, p.IsPath ∧ (∀ z ∈ p.support, z ∈ s) ∧ r ∉ p.support

theorem completeBipartite_fin_three_adj_or_common_avoiding :
    ∀ (r u v : Fin 3 ⊕ Fin 3), u ≠ r → v ≠ r → u ≠ v →
      (completeBipartiteGraph (Fin 3) (Fin 3)).Adj u v ∨
        ∃ w, w ≠ r ∧ w ≠ u ∧ w ≠ v ∧
          (completeBipartiteGraph (Fin 3) (Fin 3)).Adj u w ∧
          (completeBipartiteGraph (Fin 3) (Fin 3)).Adj w v := by
  rintro r (u | u) (v | v) hur hvr huv
  · right
    let w : Fin 3 := if r = Sum.inr 0 then 1 else 0
    have hwr : (Sum.inr w : Fin 3 ⊕ Fin 3) ≠ r := by
      simp only [w]
      split
      · rename_i h
        subst r
        decide
      · rename_i h
        exact fun h' ↦ h h'.symm
    exact ⟨Sum.inr w, hwr, by simp, by simp, by simp [completeBipartiteGraph]⟩
  · left
    simp [completeBipartiteGraph]
  · left
    simp [completeBipartiteGraph]
  · right
    let w : Fin 3 := if r = Sum.inl 0 then 1 else 0
    have hwr : (Sum.inl w : Fin 3 ⊕ Fin 3) ≠ r := by
      simp only [w]
      split
      · rename_i h
        subst r
        decide
      · rename_i h
        exact fun h' ↦ h h'.symm
    exact ⟨Sum.inl w, hwr, by simp, by simp, by simp [completeBipartiteGraph]⟩

theorem fin_three_sum_exists_ne_two (u v : Fin 3 ⊕ Fin 3) :
    ∃ r, u ≠ r ∧ v ≠ r := by
  decide +revert

theorem IsCockadeOn.isTwoConnectedOn {G : SimpleGraph V} {s : Finset V}
    (h : IsCockadeOn G s) : IsTwoConnectedOn G s := by
  induction h
  case triangle t e =>
    intro r u v hu hv hur hvr
    by_cases huv : u = v
    · subst v
      refine ⟨Walk.nil, by simp, by simp_all, ?_⟩
      simpa using hur.symm
    · have hadjInd : (G.induce (t : Set V)).Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
        apply e.map_rel_iff.mp
        simp [huv]
      have hadj : G.Adj u v := hadjInd
      refine ⟨Walk.cons hadj Walk.nil, ?_, ?_, ?_⟩
      · simpa [huv]
      · simp [hu, hv]
      · simp [hur.symm, hvr.symm]
  case k33 t e =>
    intro r u v hu hv hur hvr
    by_cases huv : u = v
    · subst v
      refine ⟨Walk.nil, by simp, by simp_all, ?_⟩
      simpa using hur.symm
    · obtain ⟨rr, hurr, hvrr, hrr⟩ : ∃ rr : Fin 3 ⊕ Fin 3,
          e ⟨u, hu⟩ ≠ rr ∧ e ⟨v, hv⟩ ≠ rr ∧
            ∀ w, w ≠ rr → ((e.symm w : (t : Set V)) : V) ≠ r := by
        by_cases hrs : r ∈ t
        · refine ⟨e ⟨r, hrs⟩, ?_, ?_, ?_⟩
          · exact fun h ↦ hur (congrArg Subtype.val (e.injective h))
          · exact fun h ↦ hvr (congrArg Subtype.val (e.injective h))
          · intro w hw heq
            apply hw
            calc
              w = e (e.symm w) := (e.apply_symm_apply w).symm
              _ = e ⟨r, hrs⟩ := by congr 1; exact Subtype.ext heq
        · obtain ⟨rr, hurr, hvrr⟩ := fin_three_sum_exists_ne_two (e ⟨u, hu⟩) (e ⟨v, hv⟩)
          exact ⟨rr, hurr, hvrr, fun w _ heq ↦ hrs (heq ▸ (e.symm w).property)⟩
      have huv' : e ⟨u, hu⟩ ≠ e ⟨v, hv⟩ :=
        fun h ↦ huv (congrArg Subtype.val (e.injective h))
      rcases completeBipartite_fin_three_adj_or_common_avoiding
          rr (e ⟨u, hu⟩) (e ⟨v, hv⟩) hurr hvrr huv' with hadj | ⟨w, hwr, hwu, hwv, huw, hwv'⟩
      · have hadjInd : (G.induce (t : Set V)).Adj ⟨u, hu⟩ ⟨v, hv⟩ := e.map_rel_iff.mp hadj
        have hadjG : G.Adj u v := hadjInd
        refine ⟨Walk.cons hadjG Walk.nil, ?_, ?_, ?_⟩
        · simpa [huv]
        · simp [hu, hv]
        · simp [hur.symm, hvr.symm]
      · let z : (t : Set V) := e.symm w
        have hz : (z : V) ∈ t := z.property
        have hzr : (z : V) ≠ r := hrr w hwr
        have hzu : (z : V) ≠ u := by
          intro h
          apply hwu
          calc
            w = e z := (e.apply_symm_apply w).symm
            _ = e ⟨u, hu⟩ := congrArg e (Subtype.ext h)
        have hzv : (z : V) ≠ v := by
          intro h
          apply hwv
          calc
            w = e z := (e.apply_symm_apply w).symm
            _ = e ⟨v, hv⟩ := congrArg e (Subtype.ext h)
        have huzInd : (G.induce (t : Set V)).Adj ⟨u, hu⟩ z := by
          apply e.map_rel_iff.mp
          simpa [z] using huw
        have hzvInd : (G.induce (t : Set V)).Adj z ⟨v, hv⟩ := by
          apply e.map_rel_iff.mp
          simpa [z] using hwv'
        have huz : G.Adj u z := huzInd
        have hzvG : G.Adj z v := hzvInd
        refine ⟨Walk.cons huz (Walk.cons hzvG Walk.nil), ?_, ?_, ?_⟩
        · simp [huv, hzu.symm, hzv]
        · simp [hu, hz, hv]
        · simp [hur.symm, hzr.symm, hvr.symm]
  case glue a b x y ha hb hxy hi hadj hnocross iha ihb =>
    intro r u v hu hv hur hvr
    have hxa : x ∈ a := by
      have : x ∈ a ∩ b := by rw [hi]; simp
      exact Finset.mem_inter.mp this |>.1
    have hxb : x ∈ b := by
      have : x ∈ a ∩ b := by rw [hi]; simp
      exact Finset.mem_inter.mp this |>.2
    have hya : y ∈ a := by
      have : y ∈ a ∩ b := by rw [hi]; simp
      exact Finset.mem_inter.mp this |>.1
    have hyb : y ∈ b := by
      have : y ∈ a ∩ b := by rw [hi]; simp
      exact Finset.mem_inter.mp this |>.2
    have connect_cross (u₀ v₀ : V) (huA : u₀ ∈ a) (hvB : v₀ ∈ b)
        (hu₀r : u₀ ≠ r) (hv₀r : v₀ ≠ r) :
        ∃ p : G.Walk u₀ v₀, p.IsPath ∧ (∀ z ∈ p.support, z ∈ a ∪ b) ∧ r ∉ p.support := by
      let q : V := if r = x then y else x
      have hqA : q ∈ a := by simp only [q]; split <;> simp_all
      have hqB : q ∈ b := by simp only [q]; split <;> simp_all
      have hqr : q ≠ r := by
        simp only [q]
        split
        · rename_i h
          subst r
          exact hxy.symm
        · rename_i h
          exact fun hxr ↦ h hxr.symm
      obtain ⟨pu, hpu, hpuA, hrpu⟩ := iha huA hqA hu₀r hqr
      obtain ⟨pv, hpv, hpvB, hrpv⟩ := ihb hqB hvB hqr hv₀r
      let w := (pu.append pv).bypass
      refine ⟨w, Walk.bypass_isPath _, ?_, ?_⟩
      · intro z hz
        have hz' := (pu.append pv).support_bypass_subset_support hz
        rw [Walk.support_append] at hz'
        rcases List.mem_append.mp hz' with hz' | hz'
        · exact Finset.mem_union.mpr (.inl (hpuA z hz'))
        · exact Finset.mem_union.mpr (.inr (hpvB z (List.mem_of_mem_tail hz')))
      · intro h
        have h' := (pu.append pv).support_bypass_subset_support h
        rw [Walk.support_append] at h'
        rcases List.mem_append.mp h' with h' | h'
        · exact hrpu h'
        · exact hrpv (List.mem_of_mem_tail h')
    rcases Finset.mem_union.mp hu with huA | huB <;>
      rcases Finset.mem_union.mp hv with hvA | hvB
    · obtain ⟨p, hp, hps, hrp⟩ := iha huA hvA hur hvr
      exact ⟨p, hp, fun z hz ↦ Finset.mem_union.mpr (.inl (hps z hz)), hrp⟩
    · exact connect_cross u v huA hvB hur hvr
    · obtain ⟨p, hp, hps, hrp⟩ := connect_cross v u hvA huB hvr hur
      exact ⟨p.reverse, hp.reverse, by simpa using hps, by simpa using hrp⟩
    · obtain ⟨p, hp, hps, hrp⟩ := ihb huB hvB hur hvr
      exact ⟨p, hp, fun z hz ↦ Finset.mem_union.mpr (.inr (hps z hz)), hrp⟩

def HasThreeSpokeCycleTest {W : Type*} (G : SimpleGraph W) : Prop :=
  ∃ (v x : W) (c : G.Walk v v),
    c.IsCycle ∧
      x ∉ c.support ∧
      ∃ a ∈ c.support, ∃ b ∈ c.support, ∃ d ∈ c.support,
        a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
          G.Adj x a ∧ G.Adj x b ∧ G.Adj x d

theorem HasThreeSpokeCycleTest.mono {W : Type*} {G H : SimpleGraph W}
    (hGH : G ≤ H) (hG : HasThreeSpokeCycleTest G) : HasThreeSpokeCycleTest H := by
  obtain ⟨v, x, c, hc, hx, a, ha, b, hb, d, hd, hab, had, hbd, hxa, hxb, hxd⟩ := hG
  refine ⟨v, x, c.mapLe hGH, hc.mapLe hGH, ?_, a, ?_, b, ?_, d, ?_, hab, had, hbd, ?_⟩
  · simpa only [Walk.support_mapLe_eq_support] using hx
  · simpa only [Walk.support_mapLe_eq_support] using ha
  · simpa only [Walk.support_mapLe_eq_support] using hb
  · simpa only [Walk.support_mapLe_eq_support] using hd
  · exact ⟨hGH hxa, hGH hxb, hGH hxd⟩

theorem fin_three_exists_ne_two (u v : Fin 3) :
    ∃ w, w ≠ u ∧ w ≠ v := by
  decide +revert

theorem k33_left_external {W : Type*} {H : SimpleGraph W}
    (f : completeBipartiteGraph (Fin 3) (Fin 3) →g H)
    (hf : Function.Injective f) {u v : Fin 3} (huv : u ≠ v)
    (p : H.Walk (f (Sum.inl u)) (f (Sum.inl v)))
    (hpExternal : ∀ z ∈ p.support, z ∈ Set.range f →
      z = f (Sum.inl u) ∨ z = f (Sum.inl v)) :
    HasThreeSpokeCycleTest H := by
  obtain ⟨w, hwu, hwv⟩ := fin_three_exists_ne_two u v
  let q₀ : (completeBipartiteGraph (Fin 3) (Fin 3)).Walk
      (Sum.inl v) (Sum.inl u) :=
    Walk.cons (show (completeBipartiteGraph (Fin 3) (Fin 3)).Adj
        (Sum.inl v) (Sum.inr 1) by simp [completeBipartiteGraph]) <|
      Walk.cons (show (completeBipartiteGraph (Fin 3) (Fin 3)).Adj
          (Sum.inr 1) (Sum.inl w) by simp [completeBipartiteGraph]) <|
        Walk.cons (show (completeBipartiteGraph (Fin 3) (Fin 3)).Adj
            (Sum.inl w) (Sum.inr 2) by simp [completeBipartiteGraph]) <|
          Walk.cons (show (completeBipartiteGraph (Fin 3) (Fin 3)).Adj
              (Sum.inr 2) (Sum.inl u) by simp [completeBipartiteGraph]) Walk.nil
  let q : H.Walk (f (Sum.inl v)) (f (Sum.inl u)) := q₀.map f
  have hq₀ : q₀.IsPath := by
    simp [q₀, huv.symm, hwu, hwv.symm]
  have hq : q.IsPath := Walk.map_isPath_of_injective hf hq₀
  let p' : H.Walk (f (Sum.inl u)) (f (Sum.inl v)) := p.toPath
  have hp' : p'.IsPath := Walk.bypass_isPath p
  have hp'sub : ∀ z ∈ p'.support, z ∈ p.support := by
    exact fun z hz ↦ p.support_bypass_subset_support hz
  have hdisjoint : p'.support.tail.Disjoint q.support.tail := by
    rw [List.disjoint_left]
    intro z hzp hzq
    have hzq' : z ∈ q₀.support.map f := by
      simpa [q] using List.mem_of_mem_tail hzq
    obtain ⟨z₀, hz₀q, rfl⟩ := List.mem_map.mp hzq'
    have hzrange : f z₀ ∈ Set.range f := ⟨z₀, rfl⟩
    have hzuv := hpExternal (f z₀) (hp'sub _ (List.mem_of_mem_tail hzp)) hzrange
    rcases hzuv with hzu | hzv
    · have hz₀u : z₀ = Sum.inl u := hf hzu
      subst z₀
      have hpN := hp'.support_nodup
      rw [← Walk.cons_tail_support p'] at hpN
      exact (List.nodup_cons.mp hpN).1 hzp
    · have hz₀v : z₀ = Sum.inl v := hf hzv
      subst z₀
      have hzq' : f (Sum.inl v) = f (Sum.inr 1) ∨
          f (Sum.inl v) = f (Sum.inl w) ∨
          f (Sum.inl v) = f (Sum.inr 2) ∨
          f (Sum.inl v) = f (Sum.inl u) := by
        simpa [q, q₀] using hzq
      rcases hzq' with h | h | h | h
      · simpa using hf h
      · exact hwv (Sum.inl.inj (hf h)).symm
      · simpa using hf h
      · exact huv (Sum.inl.inj (hf h)).symm
  have hcycle : (p'.append q).IsCycle := by
    apply hp'.isCycle_append hq hdisjoint
    right
    simp [q, q₀]
  refine ⟨f (Sum.inl u), f (Sum.inr 0), p'.append q, hcycle, ?_,
    f (Sum.inl u), ?_, f (Sum.inl v), ?_, f (Sum.inl w), ?_, ?_, ?_, ?_, ?_⟩
  · intro hc
    rw [Walk.mem_support_append_iff] at hc
    rcases hc with hcp | hcq
    · have hc0 := hpExternal _ (hp'sub _ hcp) ⟨Sum.inr 0, rfl⟩
      rcases hc0 with hc0 | hc0 <;> simpa using hf hc0
    · rw [show q = q₀.map f by rfl, Walk.support_map] at hcq
      obtain ⟨z, hz, hzf⟩ := List.mem_map.mp hcq
      have : z = Sum.inr 0 := hf hzf
      subst z
      simpa [q₀] using hz
  · exact Walk.start_mem_support _
  · rw [Walk.mem_support_append_iff]
    exact Or.inl (Walk.end_mem_support _)
  · rw [Walk.mem_support_append_iff]
    right
    simp [q, q₀]
  · exact fun h ↦ huv (Sum.inl.inj (hf h))
  · exact fun h ↦ hwu (Sum.inl.inj (hf h)).symm
  · exact fun h ↦ hwv (Sum.inl.inj (hf h)).symm
  · exact ⟨f.map_rel (by simp [completeBipartiteGraph]),
      f.map_rel (by simp [completeBipartiteGraph]),
      f.map_rel (by simp [completeBipartiteGraph])⟩

def k33SwapIso : completeBipartiteGraph (Fin 3) (Fin 3) ≃g
    completeBipartiteGraph (Fin 3) (Fin 3) where
  __ := Equiv.sumComm (Fin 3) (Fin 3)
  map_rel_iff' := by
    rintro (a | a) (b | b) <;> simp [completeBipartiteGraph]

theorem k33_right_external {W : Type*} {H : SimpleGraph W}
    (f : completeBipartiteGraph (Fin 3) (Fin 3) →g H)
    (hf : Function.Injective f) {u v : Fin 3} (huv : u ≠ v)
    (p : H.Walk (f (Sum.inr u)) (f (Sum.inr v)))
    (hpExternal : ∀ z ∈ p.support, z ∈ Set.range f →
      z = f (Sum.inr u) ∨ z = f (Sum.inr v)) :
    HasThreeSpokeCycleTest H := by
  let f' : completeBipartiteGraph (Fin 3) (Fin 3) →g H :=
    f.comp k33SwapIso.toHom
  have hf' : Function.Injective f' := hf.comp k33SwapIso.injective
  apply k33_left_external f' hf' huv p
  rintro z hz ⟨y, rfl⟩
  have hzrange : f (k33SwapIso y) ∈ Set.range f := ⟨k33SwapIso y, rfl⟩
  simpa [f', k33SwapIso] using hpExternal _ hz hzrange

theorem hasThreeSpokeCycle_of_two_common_neighbors {W : Type*} {H : SimpleGraph W}
    {u v x y : W} (huv : u ≠ v) (hux : u ≠ x) (hvx : v ≠ x)
    (hyu : y ≠ u) (hyv : y ≠ v) (hyx : y ≠ x)
    (p : H.Walk u v) (hxp : x ∉ p.support) (hyp : y ∉ p.support)
    (hxu : H.Adj x u) (hxv : H.Adj x v)
    (hyuAdj : H.Adj y u) (hyvAdj : H.Adj y v) (hyxAdj : H.Adj y x) :
    HasThreeSpokeCycleTest H := by
  let p' : H.Walk u v := p.toPath
  have hp' : p'.IsPath := Walk.bypass_isPath p
  have hxp' : x ∉ p'.support := fun h ↦ hxp (p.support_bypass_subset_support h)
  have hyp' : y ∉ p'.support := fun h ↦ hyp (p.support_bypass_subset_support h)
  let q : H.Walk v u := Walk.cons hxv.symm (Walk.cons hxu Walk.nil)
  have hq : q.IsPath := by
    simpa [q] using And.intro hux.symm (And.intro hvx huv.symm)
  have hdisjoint : p'.support.tail.Disjoint q.support.tail := by
    rw [List.disjoint_left]
    intro z hzp hzq
    have hzq' : z = x ∨ z = u := by simpa [q] using hzq
    rcases hzq' with rfl | rfl
    · exact hxp' (List.mem_of_mem_tail hzp)
    · have hpN := hp'.support_nodup
      rw [← Walk.cons_tail_support p'] at hpN
      exact (List.nodup_cons.mp hpN).1 hzp
  have hcycle : (p'.append q).IsCycle := by
    apply hp'.isCycle_append hq hdisjoint
    right
    simp [q]
  refine ⟨u, y, p'.append q, hcycle, ?_, u, ?_, v, ?_, x, ?_, huv,
    hux, hvx, hyuAdj, hyvAdj, hyxAdj⟩
  · intro hyc
    rw [Walk.mem_support_append_iff] at hyc
    rcases hyc with hyP | hyq
    · exact hyp' hyP
    · have : y = v ∨ y = x ∨ y = u := by simpa [q] using hyq
      rcases this with h | h | h
      · exact hyv h
      · exact hyx h
      · exact hyu h
  · exact Walk.start_mem_support _
  · rw [Walk.mem_support_append_iff]
    exact Or.inl (Walk.end_mem_support _)
  · rw [Walk.mem_support_append_iff]
    right
    simp [q]

def k33FourCycle (i k j l : Fin 3) :
    (completeBipartiteGraph (Fin 3) (Fin 3)).Walk (Sum.inl i) (Sum.inl i) :=
  Walk.cons (show (completeBipartiteGraph (Fin 3) (Fin 3)).Adj
      (Sum.inl i) (Sum.inr j) by simp [completeBipartiteGraph]) <|
    Walk.cons (show (completeBipartiteGraph (Fin 3) (Fin 3)).Adj
        (Sum.inr j) (Sum.inl k) by simp [completeBipartiteGraph]) <|
      Walk.cons (show (completeBipartiteGraph (Fin 3) (Fin 3)).Adj
          (Sum.inl k) (Sum.inr l) by simp [completeBipartiteGraph]) <|
        Walk.cons (show (completeBipartiteGraph (Fin 3) (Fin 3)).Adj
            (Sum.inr l) (Sum.inl i) by simp [completeBipartiteGraph]) Walk.nil

omit [Fintype V] [DecidableEq V] in
theorem k33FourCycle_isCycle {i k j l : Fin 3}
    (hik : i ≠ k) (hjl : j ≠ l) :
    (k33FourCycle i k j l).IsCycle := by
  simp [k33FourCycle, Walk.cons_isCycle_iff, Walk.isPath_def, hik, hik.symm,
    hjl, hjl.symm]

theorem completeBipartite_fin_three_edges_in_cycle
    {a b c d : Fin 3 ⊕ Fin 3}
    (hab : (completeBipartiteGraph (Fin 3) (Fin 3)).Adj a b)
    (hcd : (completeBipartiteGraph (Fin 3) (Fin 3)).Adj c d) :
    ∃ (v : Fin 3 ⊕ Fin 3)
        (p : (completeBipartiteGraph (Fin 3) (Fin 3)).Walk v v),
      p.IsCycle ∧ s(a, b) ∈ p.edges ∧ s(c, d) ∈ p.edges := by
  have build (i i' j j' : Fin 3) :
      ∃ (v : Fin 3 ⊕ Fin 3)
          (p : (completeBipartiteGraph (Fin 3) (Fin 3)).Walk v v),
        p.IsCycle ∧ s(Sum.inl i, Sum.inr j) ∈ p.edges ∧
          s(Sum.inl i', Sum.inr j') ∈ p.edges := by
    by_cases hii : i = i'
    · subst i'
      by_cases hjj : j = j'
      · subst j'
        obtain ⟨m, hmi, _⟩ := fin_three_exists_ne_two i i
        obtain ⟨n, hnj, _⟩ := fin_three_exists_ne_two j j
        refine ⟨Sum.inl i, k33FourCycle i m j n,
          k33FourCycle_isCycle hmi.symm hnj.symm, ?_⟩
        simp [k33FourCycle]
      · obtain ⟨m, hmi, _⟩ := fin_three_exists_ne_two i i
        refine ⟨Sum.inl i, k33FourCycle i m j j',
          k33FourCycle_isCycle hmi.symm hjj, ?_⟩
        simp [k33FourCycle]
    · by_cases hjj : j = j'
      · subst j'
        obtain ⟨n, hnj, _⟩ := fin_three_exists_ne_two j j
        refine ⟨Sum.inl i, k33FourCycle i i' j n,
          k33FourCycle_isCycle hii hnj.symm, ?_⟩
        simp [k33FourCycle]
      · refine ⟨Sum.inl i, k33FourCycle i i' j j',
          k33FourCycle_isCycle hii hjj, ?_⟩
        simp [k33FourCycle]
  have oriented (i j : Fin 3) {c d : Fin 3 ⊕ Fin 3}
      (hcd : (completeBipartiteGraph (Fin 3) (Fin 3)).Adj c d) :
      ∃ (v : Fin 3 ⊕ Fin 3)
          (p : (completeBipartiteGraph (Fin 3) (Fin 3)).Walk v v),
        p.IsCycle ∧ s(Sum.inl i, Sum.inr j) ∈ p.edges ∧ s(c, d) ∈ p.edges := by
    rcases c with i' | j'
    · rcases d with k' | l'
      · simp [completeBipartiteGraph] at hcd
      · exact build i i' j l'
    · rcases d with k' | l'
      · obtain ⟨v, p, hp, hfirst, hsecond⟩ := build i k' j j'
        exact ⟨v, p, hp, hfirst, Sym2.eq_swap ▸ hsecond⟩
      · simp [completeBipartiteGraph] at hcd
  rcases a with i | j
  · rcases b with k | l
    · simp [completeBipartiteGraph] at hab
    · exact oriented i l hcd
  · rcases b with k | l
    · obtain ⟨v, p, hp, hfirst, hsecond⟩ := oriented k j hcd
      exact ⟨v, p, hp, Sym2.eq_swap ▸ hfirst, hsecond⟩
    · simp [completeBipartiteGraph] at hab

omit [Fintype V] in
theorem orient_cycle_at_edge {G : SimpleGraph V} {v x y : V}
    (c : G.Walk v v) (hc : c.IsCycle) (hxy : s(x, y) ∈ c.edges) :
    ∃ r : G.Walk x x, r.IsCycle ∧ r.snd = y ∧
      (∀ z, z ∈ r.support ↔ z ∈ c.support) ∧
      (∀ e, e ∈ r.edges ↔ e ∈ c.edges) := by
  have hx : x ∈ c.support := c.fst_mem_support_of_mem_edges hxy
  let r₀ : G.Walk x x := c.rotate x hx
  have hr₀ : r₀.IsCycle := hc.rotate hx
  have hxy₀ : s(x, y) ∈ r₀.edges := by
    exact (c.rotate_edges x hx).mem_iff.mpr hxy
  have hsupport₀ : ∀ z, z ∈ r₀.support ↔ z ∈ c.support := by
    intro z
    exact c.mem_support_rotate_iff x hx
  have hedges₀ : ∀ e, e ∈ r₀.edges ↔ e ∈ c.edges := by
    intro e
    exact (c.rotate_edges x hx).mem_iff
  by_cases hsnd : r₀.snd = y
  · exact ⟨r₀, hr₀, hsnd, hsupport₀, hedges₀⟩
  · have htail : s(x, y) ∈ r₀.tail.edges := by
      have hnil := hr₀.not_nil
      have hedgesEq : r₀.edges = s(x, r₀.snd) :: r₀.tail.edges := by
        conv_lhs => rw [← r₀.cons_tail_eq hnil]
        rw [Walk.edges_cons]
      have hsplit : s(x, y) = s(x, r₀.snd) ∨ s(x, y) ∈ r₀.tail.edges := by
        simpa only [hedgesEq, List.mem_cons] using hxy₀
      rcases hsplit with hfirst | htail
      · have hcases := Sym2.eq_iff.mp hfirst
        rcases hcases with ⟨_, hy⟩ | ⟨_, hyx⟩
        · exact (hsnd hy.symm).elim
        · have hxyAdj : G.Adj x y := by
            simpa only [mem_edgeSet] using c.edges_subset_edgeSet hxy
          exact (hxyAdj.ne hyx.symm).elim
      · exact htail
    have hypen : y = r₀.penultimate := by
      have := hr₀.isPath_tail.eq_penultimate_of_mem_edges htail
      change y = r₀.tail.getVert (r₀.tail.length - 1) at this
      change y = r₀.getVert (r₀.length - 1)
      rw [Walk.getVert_tail] at this
      have hlen := r₀.length_tail_add_one hr₀.not_nil
      have hthree := hr₀.three_le_length
      have hindex : r₀.tail.length - 1 + 1 = r₀.length - 1 := by omega
      rwa [hindex] at this
    let r : G.Walk x x := r₀.reverse
    refine ⟨r, hr₀.reverse, ?_, ?_, ?_⟩
    · simpa [r, Walk.snd_reverse] using hypen.symm
    · intro z
      simp only [r, Walk.support_reverse, List.mem_reverse]
      exact hsupport₀ z
    · intro e
      simp only [r, Walk.edges_reverse, List.mem_reverse]
      exact hedges₀ e

def triangleCycle : (completeGraph (Fin 3)).Walk 0 0 :=
  Walk.cons (show (completeGraph (Fin 3)).Adj 0 1 by simp) <|
    Walk.cons (show (completeGraph (Fin 3)).Adj 1 2 by simp) <|
      Walk.cons (show (completeGraph (Fin 3)).Adj 2 0 by simp) Walk.nil

omit [Fintype V] [DecidableEq V] in
theorem triangleCycle_isCycle : triangleCycle.IsCycle := by
  simp [triangleCycle, Walk.cons_isCycle_iff, Walk.isPath_def]

theorem IsCockadeOn.edges_in_cycle {G : SimpleGraph V} {s : Finset V}
    (hc : IsCockadeOn G s) {a b c d : V}
    (ha : a ∈ s) (hb : b ∈ s) (hcMem : c ∈ s) (hd : d ∈ s)
    (hab : G.Adj a b) (hcd : G.Adj c d) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧
      s(a, b) ∈ p.edges ∧ s(c, d) ∈ p.edges ∧
      ∀ z ∈ p.support, z ∈ s := by
  induction hc generalizing a b c d with
  | triangle e =>
      rename_i t
      let f : completeGraph (Fin 3) →g G :=
        ((SimpleGraph.Embedding.induce (t : Set V)).comp
          e.symm.toEmbedding).toHom
      have hf : Function.Injective f :=
        ((SimpleGraph.Embedding.induce (t : Set V)).comp
          e.symm.toEmbedding).injective
      let A := e ⟨a, ha⟩
      let B := e ⟨b, hb⟩
      let C := e ⟨c, hcMem⟩
      let D := e ⟨d, hd⟩
      have hfA : f A = a := by simp [f, A]
      have hfB : f B = b := by simp [f, B]
      have hfC : f C = c := by simp [f, C]
      have hfD : f D = d := by simp [f, D]
      have hAB : A ≠ B := fun h ↦ hab.ne (by simpa [hfA, hfB] using congrArg f h)
      have hCD : C ≠ D := fun h ↦ hcd.ne (by simpa [hfC, hfD] using congrArg f h)
      have edge_mem (u v : Fin 3) (huv : u ≠ v) : s(u, v) ∈ triangleCycle.edges := by
        fin_cases u <;> fin_cases v <;> simp_all [triangleCycle]
      let p : G.Walk (f 0) (f 0) := triangleCycle.map f
      refine ⟨f 0, p, triangleCycle_isCycle.map hf, ?_, ?_, ?_⟩
      · change s(a, b) ∈ (triangleCycle.map f).edges
        rw [show s(a, b) = Sym2.map f s(A, B) by simp [hfA, hfB],
          Walk.edges_map]
        exact List.mem_map.mpr ⟨s(A, B), edge_mem A B hAB, rfl⟩
      · change s(c, d) ∈ (triangleCycle.map f).edges
        rw [show s(c, d) = Sym2.map f s(C, D) by simp [hfC, hfD],
          Walk.edges_map]
        exact List.mem_map.mpr ⟨s(C, D), edge_mem C D hCD, rfl⟩
      · intro z hz
        change z ∈ (triangleCycle.map f).support at hz
        rw [Walk.support_map] at hz
        obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
        simp [f]
  | k33 e =>
      rename_i t
      let f : completeBipartiteGraph (Fin 3) (Fin 3) →g G :=
        ((SimpleGraph.Embedding.induce (t : Set V)).comp
          e.symm.toEmbedding).toHom
      have hf : Function.Injective f :=
        ((SimpleGraph.Embedding.induce (t : Set V)).comp
          e.symm.toEmbedding).injective
      let A := e ⟨a, ha⟩
      let B := e ⟨b, hb⟩
      let C := e ⟨c, hcMem⟩
      let D := e ⟨d, hd⟩
      have hfA : f A = a := by simp [f, A]
      have hfB : f B = b := by simp [f, B]
      have hfC : f C = c := by simp [f, C]
      have hfD : f D = d := by simp [f, D]
      have hAB : (completeBipartiteGraph (Fin 3) (Fin 3)).Adj A B := by
        apply e.toHom.map_rel
        exact hab
      have hCD : (completeBipartiteGraph (Fin 3) (Fin 3)).Adj C D := by
        apply e.toHom.map_rel
        exact hcd
      obtain ⟨v₀, q, hq, hqAB, hqCD⟩ :=
        completeBipartite_fin_three_edges_in_cycle hAB hCD
      let p : G.Walk (f v₀) (f v₀) := q.map f
      refine ⟨f v₀, p, hq.map hf, ?_, ?_, ?_⟩
      · change s(a, b) ∈ (q.map f).edges
        rw [show s(a, b) = Sym2.map f s(A, B) by simp [hfA, hfB],
          Walk.edges_map]
        exact List.mem_map.mpr ⟨s(A, B), hqAB, rfl⟩
      · change s(c, d) ∈ (q.map f).edges
        rw [show s(c, d) = Sym2.map f s(C, D) by simp [hfC, hfD],
          Walk.edges_map]
        exact List.mem_map.mpr ⟨s(C, D), hqCD, rfl⟩
      · intro z hz
        change z ∈ (q.map f).support at hz
        rw [Walk.support_map] at hz
        obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
        simp [f]
  | glue hleft hright hxy hi hadj hnocross ihleft ihright =>
      rename_i left right x y
      have hxLeft : x ∈ left := (Finset.mem_inter.mp (by rw [hi]; simp)).1
      have hyLeft : y ∈ left := (Finset.mem_inter.mp (by rw [hi]; simp)).1
      have hxRight : x ∈ right := (Finset.mem_inter.mp (by rw [hi]; simp)).2
      have hyRight : y ∈ right := (Finset.mem_inter.mp (by rw [hi]; simp)).2
      have pair_mem_left {u v : V} (huv : s(u, v) = s(x, y)) :
          u ∈ left ∧ v ∈ left := by
        rw [Sym2.eq_iff] at huv
        rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hxLeft, hyLeft⟩
        · exact ⟨hyLeft, hxLeft⟩
      have pair_mem_right {u v : V} (huv : s(u, v) = s(x, y)) :
          u ∈ right ∧ v ∈ right := by
        rw [Sym2.eq_iff] at huv
        rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hxRight, hyRight⟩
        · exact ⟨hyRight, hxRight⟩
      have cross {a₀ b₀ c₀ d₀ : V}
          (haL : a₀ ∈ left) (hbL : b₀ ∈ left)
          (hcR : c₀ ∈ right) (hdR : d₀ ∈ right)
          (hab₀ : G.Adj a₀ b₀) (hcd₀ : G.Adj c₀ d₀) :
          ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧
            s(a₀, b₀) ∈ p.edges ∧ s(c₀, d₀) ∈ p.edges ∧
            ∀ z ∈ p.support, z ∈ left ∪ right := by
        by_cases habSep : s(a₀, b₀) = s(x, y)
        · have habR := pair_mem_right habSep
          obtain ⟨v, p, hp, hpAB, hpCD, hpMem⟩ :=
            ihright habR.1 habR.2 hcR hdR hab₀ hcd₀
          exact ⟨v, p, hp, hpAB, hpCD,
            fun z hz ↦ Finset.mem_union.mpr (.inr (hpMem z hz))⟩

        by_cases hcdSep : s(c₀, d₀) = s(x, y)
        · have hcdL := pair_mem_left hcdSep
          obtain ⟨v, p, hp, hpAB, hpCD, hpMem⟩ :=
            ihleft haL hbL hcdL.1 hcdL.2 hab₀ hcd₀
          exact ⟨v, p, hp, hpAB, hpCD,
            fun z hz ↦ Finset.mem_union.mpr (.inl (hpMem z hz))⟩
        obtain ⟨vL, cL, hcL, hABcL, hXYcL, hcLMem⟩ :=
          ihleft haL hbL hxLeft hyLeft hab₀ hadj
        obtain ⟨vR, cR, hcRcycle, hCDcR, hXYcR, hcRMem⟩ :=
          ihright hcR hdR hxRight hyRight hcd₀ hadj
        obtain ⟨rL, hrL, hrLsnd, hrLSupport, hrLEdges⟩ :=
          orient_cycle_at_edge cL hcL hXYcL
        obtain ⟨rR, hrR, hrRsnd, hrRSupport, hrREdges⟩ :=
          orient_cycle_at_edge cR hcRcycle hXYcR
        let pL : G.Walk y x := rL.tail.copy hrLsnd rfl
        let pR : G.Walk y x := rR.tail.copy hrRsnd rfl
        have hpL : pL.IsPath := by
          simpa [pL] using hrL.isPath_tail
        have hpR : pR.IsPath := by
          simpa [pR] using hrR.isPath_tail
        have hpLMem : ∀ z ∈ pL.support, z ∈ left := by
          intro z hz
          have hzTail : z ∈ rL.tail.support := by simpa [pL] using hz
          have hzCycle : z ∈ rL.support := by
            rw [← rL.cons_tail_support]
            right
            rw [← rL.support_tail_of_not_nil hrL.not_nil]
            exact hzTail
          exact hcLMem z ((hrLSupport z).mp hzCycle)
        have hpRMem : ∀ z ∈ pR.support, z ∈ right := by
          intro z hz
          have hzTail : z ∈ rR.tail.support := by simpa [pR] using hz
          have hzCycle : z ∈ rR.support := by
            rw [← rR.cons_tail_support]
            right
            rw [← rR.support_tail_of_not_nil hrR.not_nil]
            exact hzTail
          exact hcRMem z ((hrRSupport z).mp hzCycle)
        have hABtail : s(a₀, b₀) ∈ rL.tail.edges := by
          have hABrL := (hrLEdges s(a₀, b₀)).mpr hABcL
          have hedgesEq : rL.edges = s(x, y) :: rL.tail.edges := by
            conv_lhs => rw [← rL.cons_tail_eq hrL.not_nil]
            simp only [Walk.edges_cons, hrLsnd]
          rw [hedgesEq, List.mem_cons] at hABrL
          exact hABrL.resolve_left habSep
        have hCDtail : s(c₀, d₀) ∈ rR.tail.edges := by
          have hCDrR := (hrREdges s(c₀, d₀)).mpr hCDcR
          have hedgesEq : rR.edges = s(x, y) :: rR.tail.edges := by
            conv_lhs => rw [← rR.cons_tail_eq hrR.not_nil]
            simp only [Walk.edges_cons, hrRsnd]
          rw [hedgesEq, List.mem_cons] at hCDrR
          exact hCDrR.resolve_left hcdSep
        have hdisjoint : pL.reverse.support.tail.Disjoint pR.support.tail := by
          rw [List.disjoint_left]
          intro z hzL hzR
          have hzLFull : z ∈ pL.reverse.support := List.mem_of_mem_tail hzL
          have hzPL : z ∈ pL.support := by
            simpa only [Walk.support_reverse, List.mem_reverse] using hzLFull
          have hzPR : z ∈ pR.support := List.mem_of_mem_tail hzR
          have hzInter : z ∈ left ∩ right :=
            Finset.mem_inter.mpr ⟨hpLMem z hzPL, hpRMem z hzPR⟩
          have hzPair : z = x ∨ z = y := by
            have : z ∈ ({x, y} : Finset V) := hi ▸ hzInter
            simpa using this
          rcases hzPair with rfl | rfl
          · have hn := hpL.reverse.support_nodup
            rw [← Walk.cons_tail_support pL.reverse] at hn
            exact (List.nodup_cons.mp hn).1 hzL
          · have hn := hpR.support_nodup
            rw [← Walk.cons_tail_support pR] at hn
            exact (List.nodup_cons.mp hn).1 hzR
        let p : G.Walk x x := pL.reverse.append pR
        have hpCycle : p.IsCycle := by
          apply hpL.reverse.isCycle_append hpR hdisjoint
          left
          rw [Walk.length_reverse]
          rw [show pL.length = rL.tail.length by simp [pL]]
          have hlen := rL.length_tail_add_one hrL.not_nil
          have hthree := hrL.three_le_length
          omega
        refine ⟨x, p, hpCycle, ?_, ?_, ?_⟩
        · change s(a₀, b₀) ∈ (pL.reverse.append pR).edges
          rw [Walk.edges_append, List.mem_append]
          left
          change s(a₀, b₀) ∈ pL.reverse.edges
          simpa only [pL, Walk.edges_reverse, Walk.edges_copy,
            List.mem_reverse] using hABtail
        · change s(c₀, d₀) ∈ (pL.reverse.append pR).edges
          rw [Walk.edges_append, List.mem_append]
          right
          change s(c₀, d₀) ∈ pR.edges
          simpa only [pR, Walk.edges_copy] using hCDtail
        · intro z hz
          change z ∈ (pL.reverse.append pR).support at hz
          rw [Walk.mem_support_append_iff] at hz
          rcases hz with hzL | hzR
          · have hzPL : z ∈ pL.support := by
              simpa only [Walk.support_reverse, List.mem_reverse] using hzL
            exact Finset.mem_union.mpr (.inl (hpLMem z hzPL))
          · exact Finset.mem_union.mpr (.inr (hpRMem z hzR))
      have habSide := hnocross ha hb hab
      have hcdSide := hnocross hcMem hd hcd
      rcases habSide with habLeft | habRight
      · rcases hcdSide with hcdLeft | hcdRight
        · obtain ⟨v, p, hp, hpAB, hpCD, hpMem⟩ :=
            ihleft habLeft.1 habLeft.2 hcdLeft.1 hcdLeft.2 hab hcd
          exact ⟨v, p, hp, hpAB, hpCD,
            fun z hz ↦ Finset.mem_union.mpr (.inl (hpMem z hz))⟩
        · exact cross habLeft.1 habLeft.2 hcdRight.1 hcdRight.2 hab hcd
      · rcases hcdSide with hcdLeft | hcdRight
        · obtain ⟨v, p, hp, hpCD, hpAB, hpMem⟩ :=
            cross hcdLeft.1 hcdLeft.2 habRight.1 habRight.2 hcd hab
          exact ⟨v, p, hp, hpAB, hpCD, hpMem⟩
        · obtain ⟨v, p, hp, hpAB, hpCD, hpMem⟩ :=
            ihright habRight.1 habRight.2 hcdRight.1 hcdRight.2 hab hcd
          exact ⟨v, p, hp, hpAB, hpCD,
            fun z hz ↦ Finset.mem_union.mpr (.inr (hpMem z hz))⟩

theorem IsTwoConnectedOn.exists_path_to_avoiding_vertex_and_edge
    {G : SimpleGraph V} {s : Finset V} (hconn : IsTwoConnectedOn G s)
    {a b t r : V} (ha : a ∈ s) (hb : b ∈ s) (ht : t ∈ s)
    (hab : G.Adj a b) (htr : t ≠ r) :
    ∃ q : V, (q = a ∨ q = b) ∧
      ∃ p : G.Walk q t, p.IsPath ∧
        (∀ z ∈ p.support, z ∈ s) ∧ r ∉ p.support ∧
        s(a, b) ∉ p.edges := by
  by_cases har : a = r
  · have hbr : b ≠ r := by
      intro h
      apply hab.ne
      exact har.trans h.symm
    obtain ⟨p, hp, hpMem, hrp⟩ := hconn hb ht hbr htr
    refine ⟨b, Or.inr rfl, p, hp, hpMem, hrp, ?_⟩
    intro hedge
    have haSupport : a ∈ p.support := p.fst_mem_support_of_mem_edges hedge
    exact hrp (har ▸ haSupport)
  · obtain ⟨p, hp, hpMem, hrp⟩ := hconn ha ht har htr
    by_cases hedge : s(a, b) ∈ p.edges
    · have hbsnd : b = p.snd := hp.eq_snd_of_mem_edges hedge
      have hnil : ¬p.Nil := by
        intro hpNil
        have hempty : p.edges = [] := Walk.edges_eq_nil.mpr hpNil
        simpa [hempty] using hedge
      let q : G.Walk b t := p.tail.copy hbsnd.symm rfl
      have hqPath : q.IsPath := by simpa [q] using hp.tail
      have hqMem : ∀ z ∈ q.support, z ∈ s := by
        intro z hz
        have hzTail : z ∈ p.tail.support := by simpa [q] using hz
        apply hpMem z
        rw [← p.cons_tail_support]
        right
        rw [← p.support_tail_of_not_nil hnil]
        exact hzTail
      have hrq : r ∉ q.support := by
        intro hz
        have hzTail : r ∈ p.tail.support := by simpa [q] using hz
        apply hrp
        rw [← p.cons_tail_support]
        right
        rw [← p.support_tail_of_not_nil hnil]
        exact hzTail
      have hedgeTail : s(a, b) ∉ p.tail.edges := by
        have hn := hp.isTrail.edges_nodup
        rw [← p.cons_tail_eq hnil, Walk.edges_cons] at hn
        exact (List.nodup_cons.mp (by simpa only [hbsnd] using hn)).1
      refine ⟨b, Or.inr rfl, q, hqPath, hqMem, hrq, ?_⟩
      simpa only [q, Walk.edges_copy] using hedgeTail
    · exact ⟨a, Or.inl rfl, p, hp, hpMem, hrp, hedge⟩

omit [Fintype V] in
theorem replace_cycle_edge_by_two {H G : SimpleGraph V} {v a b d : V}
    (c : H.Walk v v) (hc : c.IsCycle) (hab : s(a, b) ∈ c.edges)
    (hkeep : ∀ e, e ∈ c.edges → e ≠ s(a, b) → e ∈ G.edgeSet)
    (had : G.Adj a d) (hdb : G.Adj d b) (hdc : d ∉ c.support) :
    ∃ r : G.Walk a a, r.IsCycle ∧ d ∈ r.support ∧
      (∀ z, z ∈ c.support → z ∈ r.support) ∧
      (∀ z, z ∈ r.support → z ∈ c.support ∨ z = d) := by
  obtain ⟨q, hq, hqsnd, hqSupport, hqEdges⟩ := orient_cycle_at_edge c hc hab
  have habTail : s(a, b) ∉ q.tail.edges := by
    have hn := hq.isTrail.edges_nodup
    rw [← q.cons_tail_eq hq.not_nil, Walk.edges_cons] at hn
    exact (List.nodup_cons.mp (by simpa only [hqsnd] using hn)).1
  have htailEdges : ∀ e, e ∈ q.tail.edges → e ∈ G.edgeSet := by
    intro e he
    apply hkeep e
    · apply (hqEdges e).mp
      rw [← q.cons_tail_eq hq.not_nil, Walk.edges_cons, List.mem_cons]
      exact Or.inr he
    · intro heq
      exact habTail (heq ▸ he)
  let tailG : G.Walk b a := (q.tail.copy hqsnd rfl).transfer G (by
    intro e he
    apply htailEdges e
    simpa only [Walk.edges_copy] using he)
  have htailPath : tailG.IsPath := by
    apply Walk.IsPath.transfer
    simpa [tailG] using hq.isPath_tail
  let front : G.Walk a b := Walk.cons had (Walk.cons hdb Walk.nil)
  have hfrontPath : front.IsPath := by
    have habNe : a ≠ b := by
      have : H.Adj a b := by simpa only [mem_edgeSet] using c.edges_subset_edgeSet hab
      exact this.ne
    simp [front, habNe, had.ne, hdb.ne]
  have hdisjoint : front.support.tail.Disjoint tailG.support.tail := by
    rw [List.disjoint_left]
    intro z hzFront hzTail
    have hzCases : z = d ∨ z = b := by simpa [front] using hzFront
    rcases hzCases with hzd | hzb
    · apply hdc
      rw [← hzd]
      apply (hqSupport z).mp
      have hzTailG : z ∈ tailG.support := List.mem_of_mem_tail hzTail
      have hzTailQ : z ∈ q.tail.support := by simpa [tailG] using hzTailG
      rw [← q.cons_tail_support]
      right
      rw [← q.support_tail_of_not_nil hq.not_nil]
      exact hzTailQ
    · subst z
      have hn := htailPath.support_nodup
      rw [← Walk.cons_tail_support tailG] at hn
      exact (List.nodup_cons.mp hn).1 hzTail
  let r : G.Walk a a := front.append tailG
  have hrCycle : r.IsCycle := by
    apply hfrontPath.isCycle_append htailPath hdisjoint
    left
    simp [front]
  refine ⟨r, hrCycle, ?_, ?_, ?_⟩
  · change d ∈ (front.append tailG).support
    rw [Walk.mem_support_append_iff]
    left
    simp [front]
  · intro z hzc
    have hzq : z ∈ q.support := (hqSupport z).mpr hzc
    have hzTail : z ∈ q.tail.support := by
      by_cases hza : z = a
      · subst z
        exact Walk.end_mem_support _
      · have hzTailList : z ∈ q.support.tail := by
          have : z ∈ a :: q.support.tail := by
            rw [q.cons_tail_support]
            exact hzq
          rcases List.mem_cons.mp this with hza' | hz
          · exact (hza hza').elim
          · exact hz
        rw [q.support_tail_of_not_nil hq.not_nil]
        exact hzTailList
    have hzTailG : z ∈ tailG.support := by simpa [tailG] using hzTail
    change z ∈ (front.append tailG).support
    rw [Walk.mem_support_append_iff]
    exact Or.inr hzTailG
  · intro z hzr
    change z ∈ (front.append tailG).support at hzr
    rw [Walk.mem_support_append_iff] at hzr
    rcases hzr with hzFront | hzTail
    · have hzCases : z = a ∨ z = d ∨ z = b := by simpa [front] using hzFront
      rcases hzCases with rfl | rfl | rfl
      · exact Or.inl (c.fst_mem_support_of_mem_edges hab)
      · exact Or.inr rfl
      · exact Or.inl (c.snd_mem_support_of_mem_edges hab)
    · left
      apply (hqSupport z).mp
      have hzTailQ : z ∈ q.tail.support := by simpa [tailG] using hzTail
      rw [← q.cons_tail_support]
      right
      rw [← q.support_tail_of_not_nil hq.not_nil]
      exact hzTailQ

theorem IsCockadeOn.hasThreeSpokeCycle_of_external
    {G H : SimpleGraph V} {s : Finset V} (hc : IsCockadeOn G s)
    (hGH : ∀ {x y}, x ∈ s → y ∈ s → G.Adj x y → H.Adj x y)
    {u v : V} (hu : u ∈ s) (hv : v ∈ s) (huv : u ≠ v)
    (hnadj : ¬G.Adj u v) (p : H.Walk u v)
    (hpExternal : ∀ z ∈ p.support, z ∈ s → z = u ∨ z = v) :
    HasThreeSpokeCycleTest H := by
  induction hc generalizing u v with
  | triangle e =>
      rename_i t
      exfalso
      apply hnadj
      have huv' : (⟨u, hu⟩ : (t : Set V)) ≠ ⟨v, hv⟩ :=
        fun h ↦ huv (congrArg Subtype.val h)
      have hadjTop : (completeGraph (Fin 3)).Adj (e ⟨u, hu⟩) (e ⟨v, hv⟩) := by
        exact (top_adj _ _).mpr (e.injective.ne huv')
      exact e.map_rel_iff.mp hadjTop
  | k33 e =>
      rename_i t
      let f₀ : completeBipartiteGraph (Fin 3) (Fin 3) ↪g G :=
        (SimpleGraph.Embedding.induce (t : Set V)).comp e.symm.toEmbedding
      let f : completeBipartiteGraph (Fin 3) (Fin 3) →g H :=
        ⟨fun z ↦ f₀ z, by
          intro x y hxy
          apply hGH (by simp [f₀]) (by simp [f₀])
          exact f₀.toHom.map_rel hxy⟩
      have hf : Function.Injective f := f₀.injective
      let A := e ⟨u, hu⟩
      let B := e ⟨v, hv⟩
      have hfu : f A = u := by simp [f, f₀, A]
      have hfv : f B = v := by simp [f, f₀, B]
      let p' : H.Walk (f A) (f B) := p.copy hfu.symm hfv.symm
      have hp'External : ∀ z ∈ p'.support, z ∈ Set.range f →
          z = f A ∨ z = f B := by
        rintro z hzp ⟨z₀, rfl⟩
        have hzp' : f z₀ ∈ p.support := by simpa [p'] using hzp
        have hz₀t : ((e.symm z₀ : (t : Set V)) : V) ∈ t := (e.symm z₀).property
        have hzt : f z₀ ∈ t := by simpa [f, f₀] using hz₀t
        simpa [hfu, hfv] using hpExternal (f z₀) hzp' hzt
      rcases hA : A with U | U <;> rcases hB : B with W | W
      · let pL : H.Walk (f (Sum.inl U)) (f (Sum.inl W)) :=
          p'.copy (congrArg f hA) (congrArg f hB)
        have hpLExternal : ∀ z ∈ pL.support, z ∈ Set.range f →
            z = f (Sum.inl U) ∨ z = f (Sum.inl W) := by
          intro z hzp hzrange
          have hzp' : z ∈ p'.support := by simpa [pL] using hzp
          simpa [hA, hB] using hp'External z hzp' hzrange
        apply k33_left_external f hf ?_ pL hpLExternal
        intro h
        apply huv
        calc
          u = f (Sum.inl U) := by rw [← hA]; exact hfu.symm
          _ = f (Sum.inl W) := congrArg f (congrArg Sum.inl h)
          _ = v := by rw [← hB]; exact hfv
      · exfalso
        apply hnadj
        have hf₀u : f₀ (Sum.inl U) = u := by simpa [f, hA] using hfu
        have hf₀v : f₀ (Sum.inr W) = v := by simpa [f, hB] using hfv
        simpa [hf₀u, hf₀v] using f₀.toHom.map_rel (by simp [completeBipartiteGraph] :
          (completeBipartiteGraph (Fin 3) (Fin 3)).Adj (Sum.inl U) (Sum.inr W))
      · exfalso
        apply hnadj
        have hf₀u : f₀ (Sum.inr U) = u := by simpa [f, hA] using hfu
        have hf₀v : f₀ (Sum.inl W) = v := by simpa [f, hB] using hfv
        simpa [hf₀u, hf₀v] using f₀.toHom.map_rel (by simp [completeBipartiteGraph] :
          (completeBipartiteGraph (Fin 3) (Fin 3)).Adj (Sum.inr U) (Sum.inl W))
      · let pR : H.Walk (f (Sum.inr U)) (f (Sum.inr W)) :=
          p'.copy (congrArg f hA) (congrArg f hB)
        have hpRExternal : ∀ z ∈ pR.support, z ∈ Set.range f →
            z = f (Sum.inr U) ∨ z = f (Sum.inr W) := by
          intro z hzp hzrange
          have hzp' : z ∈ p'.support := by simpa [pR] using hzp
          simpa [hA, hB] using hp'External z hzp' hzrange
        apply k33_right_external f hf ?_ pR hpRExternal
        intro h
        apply huv
        calc
          u = f (Sum.inr U) := by rw [← hA]; exact hfu.symm
          _ = f (Sum.inr W) := congrArg f (congrArg Sum.inr h)
          _ = v := by rw [← hB]; exact hfv
  | glue ha hb hxy hi hadj hnocross iha ihb =>
      rename_i a b x y
      have hxa : x ∈ a := (Finset.mem_inter.mp (by rw [hi]; simp)).1
      have hxb : x ∈ b := (Finset.mem_inter.mp (by rw [hi]; simp)).2
      have hya : y ∈ a := (Finset.mem_inter.mp (by rw [hi]; simp)).1
      have hyb : y ∈ b := (Finset.mem_inter.mp (by rw [hi]; simp)).2
      have hiYX : a ∩ b = {y, x} := by simpa [Finset.pair_comm] using hi
      have cross (u₀ v₀ : V) (huA : u₀ ∈ a) (huB : u₀ ∉ b)
          (hvB : v₀ ∈ b) (hvA : v₀ ∉ a) (huv₀ : u₀ ≠ v₀)
          (hnadj₀ : ¬G.Adj u₀ v₀) (p₀ : H.Walk u₀ v₀)
          (hp₀External : ∀ z ∈ p₀.support, z ∈ a ∪ b → z = u₀ ∨ z = v₀) :
          HasThreeSpokeCycleTest H := by
        have extendA (t r : V) (htA : t ∈ a) (htB : t ∈ b)
            (hrA : r ∈ a) (hrB : r ∈ b) (htr : t ≠ r)
            (hiTR : a ∩ b = {t, r}) (hnut : ¬G.Adj u₀ t) :
            HasThreeSpokeCycleTest H := by
          have hvr : v₀ ≠ r := fun h ↦ hvA (h.symm ▸ hrA)
          obtain ⟨q, hq, hqB, hrq⟩ :=
            IsCockadeOn.isTwoConnectedOn hb hvB htB hvr htr
          have hqEdges : ∀ e, e ∈ q.edges → e ∈ H.edgeSet := by
            rintro ⟨z, w⟩ hzw
            apply hGH (Finset.mem_union.mpr (.inr (hqB z
              (q.fst_mem_support_of_mem_edges hzw))))
              (Finset.mem_union.mpr (.inr (hqB w
                (q.snd_mem_support_of_mem_edges hzw))))
            simpa only [mem_edgeSet] using q.edges_subset_edgeSet hzw
          let qH : H.Walk v₀ t := q.transfer H hqEdges
          let w : H.Walk u₀ t := p₀.append qH
          have hut : u₀ ≠ t := fun h ↦ huB (h.symm ▸ htB)
          apply iha (fun hx hy hxy ↦ hGH (Finset.mem_union.mpr (.inl hx))
            (Finset.mem_union.mpr (.inl hy)) hxy) huA htA hut hnut w
          intro z hzw hza
          rw [Walk.mem_support_append_iff] at hzw
          rcases hzw with hzp | hzq
          · rcases hp₀External z hzp (Finset.mem_union.mpr (.inl hza)) with hzu | hzv
            · exact Or.inl hzu
            · exact (hvA (hzv ▸ hza)).elim
          · have hzq' : z ∈ q.support := by
              change z ∈ (q.transfer H hqEdges).support at hzq
              simpa only [Walk.support_transfer] using hzq
            have hzb : z ∈ b := hqB z hzq'
            have hztr : z = t ∨ z = r := by
              have : z ∈ ({t, r} : Finset V) := hiTR ▸ Finset.mem_inter.mpr ⟨hza, hzb⟩
              simpa using this
            rcases hztr with hzt | hzr
            · exact Or.inr hzt
            · exact (hrq (hzr ▸ hzq')).elim
        have extendB (t r : V) (htA : t ∈ a) (htB : t ∈ b)
            (hrA : r ∈ a) (hrB : r ∈ b) (htr : t ≠ r)
            (hiTR : a ∩ b = {t, r}) (hnvt : ¬G.Adj v₀ t) :
            HasThreeSpokeCycleTest H := by
          have hur : u₀ ≠ r := fun h ↦ huB (h.symm ▸ hrB)
          obtain ⟨q, hq, hqA, hrq⟩ :=
            IsCockadeOn.isTwoConnectedOn ha huA htA hur htr
          have hqEdges : ∀ e, e ∈ q.edges → e ∈ H.edgeSet := by
            rintro ⟨z, w⟩ hzw
            apply hGH (Finset.mem_union.mpr (.inl (hqA z
              (q.fst_mem_support_of_mem_edges hzw))))
              (Finset.mem_union.mpr (.inl (hqA w
                (q.snd_mem_support_of_mem_edges hzw))))
            simpa only [mem_edgeSet] using q.edges_subset_edgeSet hzw
          let qH : H.Walk u₀ t := q.transfer H hqEdges
          let w : H.Walk v₀ t := p₀.reverse.append qH
          have hvt : v₀ ≠ t := fun h ↦ hvA (h.symm ▸ htA)
          apply ihb (fun hx hy hxy ↦ hGH (Finset.mem_union.mpr (.inr hx))
            (Finset.mem_union.mpr (.inr hy)) hxy) hvB htB hvt hnvt w
          intro z hzw hzb
          rw [Walk.mem_support_append_iff] at hzw
          rcases hzw with hzp | hzq
          · have hzp' : z ∈ p₀.support := by simpa using hzp
            rcases hp₀External z hzp' (Finset.mem_union.mpr (.inr hzb)) with hzu | hzv
            · exact (huB (hzu ▸ hzb)).elim
            · exact Or.inl hzv
          · have hzq' : z ∈ q.support := by
              change z ∈ (q.transfer H hqEdges).support at hzq
              simpa only [Walk.support_transfer] using hzq
            have hza : z ∈ a := hqA z hzq'
            have hztr : z = t ∨ z = r := by
              have : z ∈ ({t, r} : Finset V) := hiTR ▸ Finset.mem_inter.mpr ⟨hza, hzb⟩
              simpa using this
            rcases hztr with hzt | hzr
            · exact Or.inr hzt
            · exact (hrq (hzr ▸ hzq')).elim
        by_cases hux : G.Adj u₀ x
        · by_cases huy : G.Adj u₀ y
          · by_cases hvx : G.Adj v₀ x
            · by_cases hvy : G.Adj v₀ y
              · have hxp : x ∉ p₀.support := by
                  intro hxP
                  rcases hp₀External x hxP (Finset.mem_union.mpr (.inl hxa)) with hxu | hxv
                  · exact huB (hxu ▸ hxb)
                  · exact hvA (hxv ▸ hxa)
                have hyp : y ∉ p₀.support := by
                  intro hyP
                  rcases hp₀External y hyP (Finset.mem_union.mpr (.inl hya)) with hyu | hyv
                  · exact huB (hyu ▸ hyb)
                  · exact hvA (hyv ▸ hya)
                apply hasThreeSpokeCycle_of_two_common_neighbors huv₀
                  (fun h ↦ huB (h ▸ hxb)) (fun h ↦ hvA (h ▸ hxa))
                  (fun h ↦ huB (h ▸ hyb)) (fun h ↦ hvA (h ▸ hya)) hxy.symm
                  p₀ hxp hyp
                · exact hGH (Finset.mem_union.mpr (.inl hxa))
                    (Finset.mem_union.mpr (.inl huA)) hux.symm
                · exact hGH (Finset.mem_union.mpr (.inl hxa))
                    (Finset.mem_union.mpr (.inr hvB)) hvx.symm
                · exact hGH (Finset.mem_union.mpr (.inl hya))
                    (Finset.mem_union.mpr (.inl huA)) huy.symm
                · exact hGH (Finset.mem_union.mpr (.inl hya))
                    (Finset.mem_union.mpr (.inr hvB)) hvy.symm
                · exact hGH (Finset.mem_union.mpr (.inl hya))
                    (Finset.mem_union.mpr (.inl hxa)) hadj.symm
              · exact extendB y x hya hyb hxa hxb hxy.symm hiYX hvy
            · exact extendB x y hxa hxb hya hyb hxy hi hvx
          · exact extendA y x hya hyb hxa hxb hxy.symm hiYX huy
        · exact extendA x y hxa hxb hya hyb hxy hi hux
      by_cases huA : u ∈ a
      · by_cases hvA : v ∈ a
        · exact iha (fun hx hy hxy ↦ hGH (Finset.mem_union.mpr (.inl hx))
              (Finset.mem_union.mpr (.inl hy)) hxy) huA hvA huv hnadj p fun z hz hza ↦
            hpExternal z hz (Finset.mem_union.mpr (.inl hza))
        · have hvB : v ∈ b := (Finset.mem_union.mp hv).resolve_left hvA
          by_cases huB : u ∈ b
          · exact ihb (fun hx hy hxy ↦ hGH (Finset.mem_union.mpr (.inr hx))
                (Finset.mem_union.mpr (.inr hy)) hxy) huB hvB huv hnadj p fun z hz hzb ↦
              hpExternal z hz (Finset.mem_union.mpr (.inr hzb))
          · exact cross u v huA huB hvB hvA huv hnadj p hpExternal
      · have huB : u ∈ b := (Finset.mem_union.mp hu).resolve_left huA
        by_cases hvB : v ∈ b
        · exact ihb (fun hx hy hxy ↦ hGH (Finset.mem_union.mpr (.inr hx))
              (Finset.mem_union.mpr (.inr hy)) hxy) huB hvB huv hnadj p fun z hz hzb ↦
            hpExternal z hz (Finset.mem_union.mpr (.inr hzb))
        · have hvA : v ∈ a := (Finset.mem_union.mp hv).resolve_right hvB
          apply cross v u hvA hvB huB huA huv.symm (fun h ↦ hnadj h.symm) p.reverse
          intro z hz hzab
          have hz' : z ∈ p.support := by simpa using hz
          exact (hpExternal z hz' hzab).symm

theorem IsCockadeOn.hasThreeSpokeCycle_of_replace_edge
    {H G : SimpleGraph V} {s : Finset V} (hcockade : IsCockadeOn H s)
    {a b c d : V} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hd : d ∉ s) (hab : H.Adj a b) (hac : ¬H.Adj a c)
    (hbc : ¬H.Adj b c)
    (hkeep : ∀ {u v}, u ∈ s → v ∈ s → H.Adj u v →
      s(u, v) ≠ s(a, b) → G.Adj u v)
    (hda : G.Adj d a) (hdb : G.Adj d b) (hdc : G.Adj d c) :
    HasThreeSpokeCycleTest G := by
  induction hcockade generalizing a b c d with
  | triangle e =>
      rename_i t
      exfalso
      apply hac
      have hacNe : a ≠ c := by
        intro heq
        subst c
        exact hbc hab.symm
      have htop : (completeGraph (Fin 3)).Adj (e ⟨a, ha⟩) (e ⟨c, hc⟩) :=
        (top_adj _ _).mpr (e.injective.ne (fun h ↦ hacNe (congrArg Subtype.val h)))
      exact e.map_rel_iff.mp htop
  | k33 e =>
      rename_i t
      let A := e ⟨a, ha⟩
      let B := e ⟨b, hb⟩
      let C := e ⟨c, hc⟩
      have hAB : (completeBipartiteGraph (Fin 3) (Fin 3)).Adj A B :=
        e.toHom.map_rel hab
      have hAC : ¬(completeBipartiteGraph (Fin 3) (Fin 3)).Adj A C := by
        intro h
        exact hac (e.map_rel_iff.mp h)
      have hBC : ¬(completeBipartiteGraph (Fin 3) (Fin 3)).Adj B C := by
        intro h
        exact hbc (e.map_rel_iff.mp h)
      rcases A with A | A <;> rcases B with B | B <;> rcases C with C | C <;>
        simp [completeBipartiteGraph] at hAB hAC hBC
  | glue hleft hright hxy hi hadj hnocross ihleft ihright =>
      rename_i left right x y
      have hxLeft : x ∈ left := (Finset.mem_inter.mp (by rw [hi]; simp)).1
      have hyLeft : y ∈ left := (Finset.mem_inter.mp (by rw [hi]; simp)).1
      have hxRight : x ∈ right := (Finset.mem_inter.mp (by rw [hi]; simp)).2
      have hyRight : y ∈ right := (Finset.mem_inter.mp (by rw [hi]; simp)).2
      have crossCase (P Q : Finset V) (hP : IsCockadeOn H P)
          (hQ : IsCockadeOn H Q) (hiPQ : P ∩ Q = {x, y})
          (hPsub : P ⊆ left ∪ right) (hQsub : Q ⊆ left ∪ right)
          (haP : a ∈ P) (hbP : b ∈ P) (hcQ : c ∈ Q) (hcNotP : c ∉ P)
          (hnotBothQ : ¬(a ∈ Q ∧ b ∈ Q)) : HasThreeSpokeCycleTest G := by
        have hxP : x ∈ P := (Finset.mem_inter.mp (by rw [hiPQ]; simp)).1
        have hyP : y ∈ P := (Finset.mem_inter.mp (by rw [hiPQ]; simp)).1
        have hxQ : x ∈ Q := (Finset.mem_inter.mp (by rw [hiPQ]; simp)).2
        have hyQ : y ∈ Q := (Finset.mem_inter.mp (by rw [hiPQ]; simp)).2
        have hQkeep : ∀ {u v}, u ∈ Q → v ∈ Q → H.Adj u v → G.Adj u v := by
          intro u v huQ hvQ huv
          apply hkeep (hQsub huQ) (hQsub hvQ) huv
          intro heq
          apply hnotBothQ
          rw [Sym2.eq_iff] at heq
          rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨huQ, hvQ⟩
          · exact ⟨hvQ, huQ⟩
        have externalAt (t r : V) (htP : t ∈ P) (htQ : t ∈ Q)
            (hrP : r ∈ P) (htr : t ≠ r)
            (hpair : (t = x ∧ r = y) ∨ (t = y ∧ r = x))
            (hct : ¬H.Adj c t) :
            HasThreeSpokeCycleTest G := by
          obtain ⟨q, hq, p, hp, hpMem, hrp, hpNoEdge⟩ :=
            IsTwoConnectedOn.exists_path_to_avoiding_vertex_and_edge
              hP.isTwoConnectedOn haP hbP htP hab htr
          have hpEdges : ∀ e, e ∈ p.edges → e ∈ G.edgeSet := by
            rintro ⟨u, v⟩ huvEdge
            have huP := hpMem u (p.fst_mem_support_of_mem_edges huvEdge)
            have hvP := hpMem v (p.snd_mem_support_of_mem_edges huvEdge)
            apply hkeep (hPsub huP) (hPsub hvP)
            · simpa only [mem_edgeSet] using p.edges_subset_edgeSet huvEdge
            · intro heq
              exact hpNoEdge (heq ▸ huvEdge)
          let pG : G.Walk q t := p.transfer G hpEdges
          have hdq : G.Adj d q := by
            rcases hq with rfl | rfl
            · exact hda
            · exact hdb
          let w : G.Walk c t := Walk.cons hdc.symm (Walk.cons hdq pG)
          have hctNe : c ≠ t := fun heq ↦ hcNotP (heq ▸ htP)
          apply hQ.hasThreeSpokeCycle_of_external hQkeep hcQ htQ hctNe hct w
          intro z hzw hzQ
          have hzCases : z = c ∨ z = d ∨ z ∈ pG.support := by
            simpa [w] using hzw
          rcases hzCases with rfl | rfl | hzPath
          · exact Or.inl rfl
          · exact (hd (hQsub hzQ)).elim
          · have hzPPath : z ∈ p.support := by simpa [pG] using hzPath
            have hzP : z ∈ P := hpMem z hzPPath
            have hzPair : z = x ∨ z = y := by
              have : z ∈ ({x, y} : Finset V) :=
                hiPQ ▸ Finset.mem_inter.mpr ⟨hzP, hzQ⟩
              simpa using this
            have hzr : r ∉ p.support := hrp
            rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · rcases hzPair with rfl | rfl
              · exact Or.inr rfl
              · exact (hzr hzPPath).elim
            · rcases hzPair with rfl | rfl
              · exact (hzr hzPPath).elim
              · exact Or.inr rfl
        by_cases hcx : H.Adj c x
        · by_cases hcy : H.Adj c y
          · obtain ⟨v, cyc, hcyc, habCyc, hxyCyc, hcycMem⟩ :=
              hP.edges_in_cycle haP hbP hxP hyP hab hadj
            have hcycKeep : ∀ e, e ∈ cyc.edges → e ≠ s(a, b) → e ∈ G.edgeSet := by
              rintro ⟨u, v⟩ huvEdge huvNe
              have huP := hcycMem u (cyc.fst_mem_support_of_mem_edges huvEdge)
              have hvP := hcycMem v (cyc.snd_mem_support_of_mem_edges huvEdge)
              exact hkeep (hPsub huP) (hPsub hvP)
                (by simpa only [mem_edgeSet] using cyc.edges_subset_edgeSet huvEdge) huvNe
            have hdcyc : d ∉ cyc.support := by
              intro hdc'
              exact hd (hPsub (hcycMem d hdc'))
            obtain ⟨rim, hrim, hdRim, hOldRim, hRimOld⟩ :=
              replace_cycle_edge_by_two cyc hcyc habCyc hcycKeep hda.symm hdb hdcyc
            have hxCyc : x ∈ cyc.support := cyc.fst_mem_support_of_mem_edges hxyCyc
            have hyCyc : y ∈ cyc.support := cyc.snd_mem_support_of_mem_edges hxyCyc
            have hcRim : c ∉ rim.support := by
              intro hcr
              rcases hRimOld c hcr with hcOld | hcdEq
              · exact hcNotP (hcycMem c hcOld)
              · exact hd (hcdEq.symm ▸ hQsub hcQ)
            have hcxG : G.Adj c x := hQkeep hcQ hxQ hcx
            have hcyG : G.Adj c y := hQkeep hcQ hyQ hcy
            refine ⟨a, c, rim, hrim, hcRim, x, hOldRim x hxCyc,
              y, hOldRim y hyCyc, d, hdRim, hxy, ?_, ?_, hcxG, hcyG, hdc.symm⟩
            · intro hxd
              exact hd (hxd.symm ▸ hPsub hxP)
            · intro hyd
              exact hd (hyd.symm ▸ hPsub hyP)
          · exact externalAt y x hyP hyQ hxP hxy.symm
              (Or.inr ⟨rfl, rfl⟩) hcy
        · exact externalAt x y hxP hxQ hyP hxy
            (Or.inl ⟨rfl, rfl⟩) hcx
      have habSide := hnocross ha hb hab
      rcases habSide with habLeft | habRight
      · by_cases hcLeft : c ∈ left
        · apply ihleft habLeft.1 habLeft.2 hcLeft
            (fun hdl ↦ hd (Finset.mem_union.mpr (.inl hdl)))
            hab hac hbc
          · intro u v hu hv huv hne
            exact hkeep (Finset.mem_union.mpr (.inl hu))
              (Finset.mem_union.mpr (.inl hv)) huv hne
          · exact hda
          · exact hdb
          · exact hdc
        · have hcRight : c ∈ right := (Finset.mem_union.mp hc).resolve_left hcLeft
          by_cases habBothRight : a ∈ right ∧ b ∈ right
          · apply ihright habBothRight.1 habBothRight.2 hcRight
              (fun hdr ↦ hd (Finset.mem_union.mpr (.inr hdr))) hab hac hbc
            · intro u v hu hv huv hne
              exact hkeep (Finset.mem_union.mpr (.inr hu))
                (Finset.mem_union.mpr (.inr hv)) huv hne
            · exact hda
            · exact hdb
            · exact hdc
          · exact crossCase left right hleft hright hi Finset.subset_union_left
              Finset.subset_union_right habLeft.1 habLeft.2 hcRight hcLeft habBothRight
      · by_cases hcRight : c ∈ right
        · apply ihright habRight.1 habRight.2 hcRight
            (fun hdr ↦ hd (Finset.mem_union.mpr (.inr hdr)))
            hab hac hbc
          · intro u v hu hv huv hne
            exact hkeep (Finset.mem_union.mpr (.inr hu))
              (Finset.mem_union.mpr (.inr hv)) huv hne
          · exact hda
          · exact hdb
          · exact hdc
        · have hcLeft : c ∈ left := (Finset.mem_union.mp hc).resolve_right hcRight
          by_cases habBothLeft : a ∈ left ∧ b ∈ left
          · apply ihleft habBothLeft.1 habBothLeft.2 hcLeft
              (fun hdl ↦ hd (Finset.mem_union.mpr (.inl hdl))) hab hac hbc
            · intro u v hu hv huv hne
              exact hkeep (Finset.mem_union.mpr (.inl hu))
                (Finset.mem_union.mpr (.inl hv)) huv hne
            · exact hda
            · exact hdb
            · exact hdc
          · have hiSwap : right ∩ left = {x, y} := by
              simpa [Finset.inter_comm] using hi
            exact crossCase right left hright hleft hiSwap Finset.subset_union_right
              Finset.subset_union_left habRight.1 habRight.2 hcLeft hcRight habBothLeft

theorem IsCockadeOn.hasThreeSpokeCycle_of_extra_edge
    {G H : SimpleGraph V} {s : Finset V} (hc : IsCockadeOn H s)
    (hHG : H ≤ G) {u v : V} (hu : u ∈ s) (hv : v ∈ s)
    (huv : G.Adj u v) (hnuv : ¬H.Adj u v) :
    HasThreeSpokeCycleTest G := by
  have hne : u ≠ v := huv.ne
  let p : G.Walk u v := Walk.cons huv Walk.nil
  apply hc.hasThreeSpokeCycle_of_external (fun _ _ h ↦ hHG h) hu hv hne hnuv p
  intro z hz _
  simpa [p] using hz

theorem IsCockadeOn.hasThreeSpokeCycle_of_lt
    {G H : SimpleGraph V} (hc : IsCockadeOn H Finset.univ) (hHG : H < G) :
    HasThreeSpokeCycleTest G := by
  have hnle : ¬G ≤ H := hHG.2
  change ¬(∀ u v, G.Adj u v → H.Adj u v) at hnle
  push_neg at hnle
  obtain ⟨u, v, huv, hnuv⟩ := hnle
  exact hc.hasThreeSpokeCycle_of_extra_edge hHG.1 (by simp) (by simp) huv hnuv

theorem exists_le_edgeFinset_card_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : k ≤ G.edgeFinset.card) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.edgeSet.ncard = k := by
  classical
  obtain ⟨t, ht, htcard⟩ := Finset.exists_subset_card_eq hk
  let H : SimpleGraph V := fromEdgeSet (t : Set (Sym2 V))
  have htdiag : Disjoint (t : Set (Sym2 V)) Sym2.diagSet := by
    rw [Set.disjoint_left]
    intro e het hediag
    exact G.not_isDiag_of_mem_edgeFinset (ht het) hediag
  have hHedges : H.edgeSet = (t : Set (Sym2 V)) := by simp [H, htdiag]
  refine ⟨H, ?_, ?_⟩
  · rw [← edgeSet_subset_edgeSet, hHedges]
    intro e he
    exact mem_edgeFinset.mp (ht (by simpa using he))
  · rw [hHedges, Set.ncard_coe_finset, htcard]

theorem hasThreeSpokeCycle_of_extremal_classification (G : SimpleGraph V)
    [DecidableRel G.Adj] (hV : 2 ≤ Fintype.card V)
    (hE : 2 * Fintype.card V - 2 ≤ G.edgeFinset.card)
    (hclass : ∀ H : SimpleGraph V,
      H.edgeSet.ncard = 2 * Fintype.card V - 3 →
      ¬HasThreeSpokeCycleTest H → IsCockadeOn H Finset.univ) :
    HasThreeSpokeCycleTest G := by
  classical
  have hk : 2 * Fintype.card V - 3 ≤ G.edgeFinset.card := by omega
  obtain ⟨H, hHG, hHcard⟩ := exists_le_edgeFinset_card_eq G hk
  by_cases hHw : HasThreeSpokeCycleTest H
  · exact hHw.mono hHG
  · have hc : IsCockadeOn H Finset.univ := hclass H hHcard hHw
    apply hc.hasThreeSpokeCycle_of_lt
    refine ⟨hHG, ?_⟩
    intro hGH
    have heq : H = G := le_antisymm hHG hGH
    subst H
    have hGcard : G.edgeFinset.card = 2 * Fintype.card V - 3 := by
      have hn : (G.edgeFinset : Set (Sym2 V)).ncard =
          2 * Fintype.card V - 3 := by
        simpa only [coe_edgeFinset] using hHcard
      rw [Set.ncard_coe_finset] at hn
      exact hn
    omega

structure SeparationOn (G : SimpleGraph V) (s a b : Finset V) : Prop where
  union_eq : a ∪ b = s
  left_nonempty : (a \ b).Nonempty
  right_nonempty : (b \ a).Nonempty
  no_cross : ∀ {u v}, u ∈ a ∪ b → v ∈ a ∪ b → G.Adj u v →
    (u ∈ a ∧ v ∈ a) ∨ (u ∈ b ∧ v ∈ b)

structure TwoSeparationOn (G : SimpleGraph V) (s : Finset V) where
  leftSet : Finset V
  rightSet : Finset V
  sepX : V
  sepY : V
  separation : SeparationOn G s leftSet rightSet
  ne : sepX ≠ sepY
  inter_eq : leftSet ∩ rightSet = {sepX, sepY}
  leftPath : G.Walk sepX sepY
  leftPath_mem : ∀ z ∈ leftPath.support, z ∈ leftSet
  rightPath : G.Walk sepX sepY
  rightPath_mem : ∀ z ∈ rightPath.support, z ∈ rightSet

omit [Fintype V] in
theorem SeparationOn.left_ssubset {G : SimpleGraph V} {s a b : Finset V}
    (h : SeparationOn G s a b) : a ⊂ s := by
  rw [← h.union_eq]
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, ?_⟩
  obtain ⟨v, hv⟩ := h.right_nonempty
  have ⟨hvb, hva⟩ := Finset.mem_sdiff.mp hv
  intro heq
  have : v ∈ a := heq ▸ Finset.mem_union_right a hvb
  exact hva this

omit [Fintype V] in
theorem SeparationOn.right_ssubset {G : SimpleGraph V} {s a b : Finset V}
    (h : SeparationOn G s a b) : b ⊂ s := by
  rw [← h.union_eq]
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_right, ?_⟩
  obtain ⟨v, hv⟩ := h.left_nonempty
  have ⟨hva, hvb⟩ := Finset.mem_sdiff.mp hv
  intro heq
  have : v ∈ b := heq ▸ Finset.mem_union_left b hva
  exact hvb this

omit [Fintype V] in
theorem edgeSetOn_inter_eq_empty_of_card_le_one (G : SimpleGraph V) (t : Finset V)
    (ht : t.card ≤ 1) : edgeSetOn G t = ∅ := by
  ext ⟨u, v⟩
  simp only [edgeSetOn, Set.mem_inter_iff, mem_edgeSet, Set.mk_mem_sym2_iff,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨huv, hu, hv⟩
  have huv_ne : u ≠ v := huv.ne
  have htwo : 2 ≤ t.card := by
    have hsub : ({u, v} : Finset V) ⊆ t := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    simpa [huv_ne] using Finset.card_le_card hsub
  omega

omit [Fintype V] in
theorem edgeSetOn_inter (G : SimpleGraph V) (a b : Finset V) :
    edgeSetOn G a ∩ edgeSetOn G b = edgeSetOn G (a ∩ b) := by
  ext ⟨u, v⟩
  simp only [edgeSetOn, Set.mem_inter_iff, mem_edgeSet, Set.mk_mem_sym2_iff,
    Finset.coe_inter, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨huv, hua, hva⟩, _, hub, hvb⟩
    exact ⟨huv, ⟨hua, hub⟩, ⟨hva, hvb⟩⟩
  · rintro ⟨huv, ⟨hua, hub⟩, ⟨hva, hvb⟩⟩
    exact ⟨⟨huv, hua, hva⟩, huv, hub, hvb⟩

omit [Fintype V] in
theorem edgeSetOn_inter_eq_empty_of_pair_nonadj (G : SimpleGraph V)
    {a b : Finset V} {x y : V} (hi : a ∩ b = {x, y}) (hnadj : ¬G.Adj x y) :
    edgeSetOn G a ∩ edgeSetOn G b = ∅ := by
  ext ⟨u, v⟩
  simp only [edgeSetOn, Set.mem_inter_iff, mem_edgeSet, Set.mk_mem_sym2_iff,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨huv, hua, hva⟩, _, hub, hvb⟩
  have hu : u = x ∨ u = y := by
    have : u ∈ ({x, y} : Finset V) := hi ▸ Finset.mem_inter.mpr ⟨hua, hub⟩
    simpa using this
  have hv : v = x ∨ v = y := by
    have : v ∈ ({x, y} : Finset V) := hi ▸ Finset.mem_inter.mpr ⟨hva, hvb⟩
    simpa using this
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact G.loopless.irrefl _ huv
  · exact hnadj huv
  · exact hnadj huv.symm
  · exact G.loopless.irrefl _ huv

theorem SeparationOn.edge_count_identity {G : SimpleGraph V} {s a b : Finset V}
    (h : SeparationOn G s a b) :
    (edgeSetOn G s).ncard + (edgeSetOn G a ∩ edgeSetOn G b).ncard =
      (edgeSetOn G a).ncard + (edgeSetOn G b).ncard := by
  have hu := edgeSetOn_union_of_noCross G a b h.no_cross
  have hc := Set.ncard_union_add_ncard_inter (edgeSetOn G a) (edgeSetOn G b)
  rw [h.union_eq] at hu
  exact (congrArg
    (fun q : Set (Sym2 V) ↦ q.ncard + (edgeSetOn G a ∩ edgeSetOn G b).ncard) hu).trans hc

omit [Fintype V] in
theorem TwoSeparationOn.left_members {G : SimpleGraph V} {s : Finset V}
    (h : TwoSeparationOn G s) : h.sepX ∈ h.leftSet ∧ h.sepY ∈ h.leftSet := by
  have hx : h.sepX ∈ h.leftSet ∩ h.rightSet := by rw [h.inter_eq]; simp
  have hy : h.sepY ∈ h.leftSet ∩ h.rightSet := by rw [h.inter_eq]; simp
  exact ⟨(Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hy).1⟩

omit [Fintype V] in
theorem TwoSeparationOn.right_members {G : SimpleGraph V} {s : Finset V}
    (h : TwoSeparationOn G s) : h.sepX ∈ h.rightSet ∧ h.sepY ∈ h.rightSet := by
  have hx : h.sepX ∈ h.leftSet ∩ h.rightSet := by rw [h.inter_eq]; simp
  have hy : h.sepY ∈ h.leftSet ∩ h.rightSet := by rw [h.inter_eq]; simp
  exact ⟨(Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hy).2⟩

omit [Fintype V] in
theorem TwoSeparationOn.rightPath_external_left {G : SimpleGraph V} {s : Finset V}
    (h : TwoSeparationOn G s) :
    ∀ z ∈ h.rightPath.support, z ∈ h.leftSet → z = h.sepX ∨ z = h.sepY := by
  intro z hz hzl
  have hzr := h.rightPath_mem z hz
  have : z ∈ ({h.sepX, h.sepY} : Finset V) :=
    h.inter_eq ▸ Finset.mem_inter.mpr ⟨hzl, hzr⟩
  simpa using this

omit [Fintype V] in
theorem TwoSeparationOn.leftPath_external_right {G : SimpleGraph V} {s : Finset V}
    (h : TwoSeparationOn G s) :
    ∀ z ∈ h.leftPath.support, z ∈ h.rightSet → z = h.sepX ∨ z = h.sepY := by
  intro z hz hzr
  have hzl := h.leftPath_mem z hz
  have : z ∈ ({h.sepX, h.sepY} : Finset V) :=
    h.inter_eq ▸ Finset.mem_inter.mpr ⟨hzl, hzr⟩
  simpa using this

theorem exists_le_edgeSetOn_ncard_eq (G : SimpleGraph V) (s : Finset V)
    {k : ℕ} (hk : k ≤ (edgeSetOn G s).ncard) :
    ∃ H : SimpleGraph V, H ≤ G ∧ (edgeSetOn H s).ncard = k := by
  classical
  let E : Finset (Sym2 V) := (Set.toFinite (edgeSetOn G s)).toFinset
  have hEcard : E.card = (edgeSetOn G s).ncard := by
    rw [Set.ncard_eq_toFinset_card (edgeSetOn G s)]
  obtain ⟨t, htE, htcard⟩ := Finset.exists_subset_card_eq (hEcard ▸ hk)
  let H : SimpleGraph V := fromEdgeSet (t : Set (Sym2 V))
  have htG : (t : Set (Sym2 V)) ⊆ G.edgeSet := by
    intro e het
    have heE : e ∈ E := htE (by simpa using het)
    have heOn : e ∈ edgeSetOn G s := by simpa [E] using heE
    exact heOn.1
  have htdiag : Disjoint (t : Set (Sym2 V)) Sym2.diagSet := by
    rw [Set.disjoint_left]
    intro e het hediag
    exact G.not_isDiag_of_mem_edgeSet (htG het) hediag
  have hHedges : H.edgeSet = (t : Set (Sym2 V)) := by simp [H, htdiag]
  have htOn : (t : Set (Sym2 V)) ⊆ (s : Set V).sym2 := by
    intro e het
    have heE : e ∈ E := htE (by simpa using het)
    have heOn : e ∈ edgeSetOn G s := by simpa [E] using heE
    exact heOn.2
  have hHon : edgeSetOn H s = (t : Set (Sym2 V)) := by
    rw [edgeSetOn, hHedges, Set.inter_eq_left]
    exact htOn
  refine ⟨H, ?_, ?_⟩
  · rw [← edgeSet_subset_edgeSet, hHedges]
    exact htG
  · rw [hHon, Set.ncard_coe_finset, htcard]

theorem IsCockadeOn.hasThreeSpokeCycle_of_more_edges
    {G H : SimpleGraph V} {s : Finset V} (hc : IsCockadeOn H s) (hHG : H ≤ G)
    (hcard : (edgeSetOn H s).ncard < (edgeSetOn G s).ncard) :
    HasThreeSpokeCycleTest G := by
  have hsub : edgeSetOn H s ⊆ edgeSetOn G s := by
    rintro ⟨u, v⟩ ⟨huv, hu, hv⟩
    exact ⟨hHG huv, hu, hv⟩
  have hss : edgeSetOn H s ⊂ edgeSetOn G s := by
    refine ⟨hsub, ?_⟩
    intro hrev
    have heq := Set.Subset.antisymm hsub hrev
    rw [heq] at hcard
    omega
  obtain ⟨e, heG, heH⟩ := Set.exists_of_ssubset hss
  obtain ⟨u, v⟩ := e
  have huvG : G.Adj u v := heG.1
  have huvH : ¬H.Adj u v := fun h ↦ heH ⟨h, heG.2.1, heG.2.2⟩
  exact hc.hasThreeSpokeCycle_of_extra_edge hHG heG.2.1 heG.2.2 huvG huvH

theorem ncard_edgeSetOn_le_choose (G : SimpleGraph V) (s : Finset V) :
    (edgeSetOn G s).ncard ≤ s.card.choose 2 := by
  classical
  let K : SimpleGraph (s : Set V) := G.induce (s : Set V)
  letI : DecidableRel K.Adj := Classical.decRel _
  have hk := K.card_edgeFinset_le_card_choose_two
  have hcard : Fintype.card (s : Set V) = s.card := by simp
  have hn : K.edgeSet.ncard = K.edgeFinset.card := by
    have hco : (K.edgeFinset : Set (Sym2 (s : Set V))).ncard = K.edgeSet.ncard := by simp
    rw [Set.ncard_coe_finset] at hco
    exact hco.symm
  rw [ncard_edgeSetOn, hn]
  simpa [hcard] using hk

def HasLowSeparationOn (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∃ a b, SeparationOn G s a b ∧ (a ∩ b).card ≤ 1

def ReachableOnAvoiding (G : SimpleGraph V) (s forbidden : Finset V) (u v : V) : Prop :=
  ∃ p : G.Walk u v, ∀ z ∈ p.support, z ∈ s ∧ z ∉ forbidden

omit [Fintype V] in
theorem ReachableOnAvoiding.refl {G : SimpleGraph V} {s forbidden : Finset V} {u : V}
    (hus : u ∈ s) (huf : u ∉ forbidden) : ReachableOnAvoiding G s forbidden u u := by
  refine ⟨Walk.nil, ?_⟩
  simpa using And.intro hus huf

omit [Fintype V] in
theorem ReachableOnAvoiding.symm {G : SimpleGraph V} {s forbidden : Finset V} {u v : V}
    (h : ReachableOnAvoiding G s forbidden u v) :
    ReachableOnAvoiding G s forbidden v u := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p.reverse, ?_⟩
  intro z hz
  exact hp z (by simpa using hz)

omit [Fintype V] in
theorem ReachableOnAvoiding.trans {G : SimpleGraph V} {s forbidden : Finset V}
    {u v w : V} (huv : ReachableOnAvoiding G s forbidden u v)
    (hvw : ReachableOnAvoiding G s forbidden v w) :
    ReachableOnAvoiding G s forbidden u w := by
  obtain ⟨p, hp⟩ := huv
  obtain ⟨q, hq⟩ := hvw
  refine ⟨p.append q, ?_⟩
  intro z hz
  rw [Walk.mem_support_append_iff] at hz
  exact hz.elim (hp z) (hq z)

omit [Fintype V] in
theorem ReachableOnAvoiding.of_adj_right {G : SimpleGraph V} {s forbidden : Finset V}
    {u v w : V} (huv : ReachableOnAvoiding G s forbidden u v)
    (hvw : G.Adj v w) (hws : w ∈ s) (hwf : w ∉ forbidden) :
    ReachableOnAvoiding G s forbidden u w := by
  apply huv.trans
  refine ⟨Walk.cons hvw Walk.nil, ?_⟩
  intro z hz
  obtain ⟨p, hp⟩ := huv
  have hvok := hp _ (Walk.end_mem_support p)
  have : z = v ∨ z = w := by simpa using hz
  rcases this with rfl | rfl
  · exact hvok
  · exact ⟨hws, hwf⟩

omit [Fintype V] in
theorem ReachableOnAvoiding.to_support {G : SimpleGraph V} {s forbidden : Finset V}
    {u v z : V} (h : ReachableOnAvoiding G s forbidden u v)
    (p : G.Walk u v) (hp : ∀ w ∈ p.support, w ∈ s ∧ w ∉ forbidden)
    (hz : z ∈ p.support) : ReachableOnAvoiding G s forbidden u z := by
  refine ⟨p.takeUntil z hz, ?_⟩
  intro w hw
  exact hp w (p.support_takeUntil_subset_support hz hw)

theorem separationOn_of_not_reachableOnAvoiding (G : SimpleGraph V)
    (s forbidden : Finset V) {u v : V}
    (hus : u ∈ s) (huf : u ∉ forbidden)
    (hvs : v ∈ s) (hvf : v ∉ forbidden)
    (huv : ¬ReachableOnAvoiding G s forbidden u v) :
    ∃ a b, SeparationOn G s a b ∧ a ∩ b = s ∩ forbidden ∧
      ∀ z, z ∈ s → z ∉ forbidden →
        (z ∈ a \ b ↔ ReachableOnAvoiding G s forbidden u z) := by
  classical
  let r : Finset V := s.filter (ReachableOnAvoiding G s forbidden u)
  let f : Finset V := s ∩ forbidden
  let a : Finset V := r ∪ f
  let b : Finset V := (s \ r) ∪ f
  have hr_sub : r ⊆ s := by intro z hz; exact (Finset.mem_filter.mp hz).1
  have hr_avoid : ∀ {z}, z ∈ r → z ∉ forbidden := by
    intro z hz hzf
    have hzreach := (Finset.mem_filter.mp hz).2
    obtain ⟨p, hp⟩ := hzreach
    exact (hp z (Walk.end_mem_support p)).2 hzf
  have hu_r : u ∈ r := by
    simp only [r, Finset.mem_filter]
    exact ⟨hus, ReachableOnAvoiding.refl hus huf⟩
  have hv_nr : v ∉ r := by
    intro hvr
    exact huv (Finset.mem_filter.mp hvr).2
  have hf_sub : f ⊆ s := Finset.inter_subset_left
  have hab_union : a ∪ b = s := by
    ext z
    simp only [a, b, f, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · intro hz
      rcases hz with hza | hzb
      · rcases hza with hzr | ⟨hzs, _⟩
        · exact hr_sub hzr
        · exact hzs
      · rcases hzb with ⟨hzs, _⟩ | ⟨hzs, _⟩ <;> exact hzs
    · intro hzs
      by_cases hzr : z ∈ r
      · exact Or.inl (Or.inl hzr)
      · exact Or.inr (Or.inl ⟨hzs, hzr⟩)
  have hab_inter : a ∩ b = f := by
    ext z
    simp only [a, b, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨hzr | hzf, ⟨_, hnzr⟩ | hzf'⟩
      · exact (hnzr hzr).elim
      · exact hzf'
      · exact hzf
      · exact hzf
    · intro hzf
      exact ⟨Or.inr hzf, Or.inr hzf⟩
  have hu_adiff : u ∈ a \ b := by
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_union_left f hu_r, ?_⟩
    intro hub
    rcases Finset.mem_union.mp hub with hub | huf'
    · exact (Finset.mem_sdiff.mp hub).2 hu_r
    · exact huf (Finset.mem_inter.mp huf').2
  have hv_bdiff : v ∈ b \ a := by
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_union_left f (Finset.mem_sdiff.mpr ⟨hvs, hv_nr⟩), ?_⟩
    intro hva
    rcases Finset.mem_union.mp hva with hvr | hvf'
    · exact hv_nr hvr
    · exact hvf (Finset.mem_inter.mp hvf').2
  have hno_cross : ∀ {x y}, x ∈ a ∪ b → y ∈ a ∪ b → G.Adj x y →
      (x ∈ a ∧ y ∈ a) ∨ (x ∈ b ∧ y ∈ b) := by
    intro x y hx hy hxy
    have hxs : x ∈ s := hab_union ▸ hx
    have hys : y ∈ s := hab_union ▸ hy
    by_cases hxf : x ∈ forbidden
    · have hxf' : x ∈ f := Finset.mem_inter.mpr ⟨hxs, hxf⟩
      by_cases hya : y ∈ a
      · exact Or.inl ⟨Finset.mem_union_right r hxf', hya⟩
      · exact Or.inr ⟨Finset.mem_union_right (s \ r) hxf',
          (Finset.mem_union.mp (hab_union.symm ▸ hy)).resolve_left hya⟩
    · by_cases hyf : y ∈ forbidden
      · have hyf' : y ∈ f := Finset.mem_inter.mpr ⟨hys, hyf⟩
        by_cases hxa : x ∈ a
        · exact Or.inl ⟨hxa, Finset.mem_union_right r hyf'⟩
        · exact Or.inr ⟨(Finset.mem_union.mp (hab_union.symm ▸ hx)).resolve_left hxa,
            Finset.mem_union_right (s \ r) hyf'⟩
      · by_cases hxr : x ∈ r
        · have hyr : y ∈ r := by
            simp only [r, Finset.mem_filter]
            refine ⟨hys, ?_⟩
            exact ((Finset.mem_filter.mp hxr).2).of_adj_right hxy hys hyf
          exact Or.inl ⟨Finset.mem_union_left f hxr, Finset.mem_union_left f hyr⟩
        · have hyr : y ∉ r := by
            intro hyr
            have hxreach := ((Finset.mem_filter.mp hyr).2).of_adj_right hxy.symm hxs hxf
            exact hxr (Finset.mem_filter.mpr ⟨hxs, hxreach⟩)
          exact Or.inr ⟨Finset.mem_union_left f (Finset.mem_sdiff.mpr ⟨hxs, hxr⟩),
            Finset.mem_union_left f (Finset.mem_sdiff.mpr ⟨hys, hyr⟩)⟩
  have hcomponent : ∀ z, z ∈ s → z ∉ forbidden →
      (z ∈ a \ b ↔ ReachableOnAvoiding G s forbidden u z) := by
    intro z hzs hzf
    constructor
    · intro hz
      have hza := (Finset.mem_sdiff.mp hz).1
      rcases Finset.mem_union.mp hza with hzr | hzf'
      · exact (Finset.mem_filter.mp hzr).2
      · exact (hzf (Finset.mem_inter.mp hzf').2).elim
    · intro hzreach
      have hzr : z ∈ r := Finset.mem_filter.mpr ⟨hzs, hzreach⟩
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_union_left f hzr, ?_⟩
      intro hzb
      rcases Finset.mem_union.mp hzb with hzsr | hzf'
      · exact (Finset.mem_sdiff.mp hzsr).2 hzr
      · exact hzf (Finset.mem_inter.mp hzf').2
  refine ⟨a, b, ⟨hab_union, ⟨u, hu_adiff⟩, ⟨v, hv_bdiff⟩, hno_cross⟩, ?_,
    hcomponent⟩
  simpa [f] using hab_inter

omit [Fintype V] in
theorem SeparationOn.symm {G : SimpleGraph V} {s a b : Finset V}
    (h : SeparationOn G s a b) : SeparationOn G s b a := by
  refine ⟨Finset.union_comm a b ▸ h.union_eq, h.right_nonempty, h.left_nonempty, ?_⟩
  intro u v hu hv huv
  exact (h.no_cross (Finset.union_comm b a ▸ hu) (Finset.union_comm b a ▸ hv) huv).symm

theorem reachableOnAvoiding_of_noLowSeparation {G : SimpleGraph V} {s forbidden : Finset V}
    (hnlow : ¬HasLowSeparationOn G s) (hf : forbidden.card ≤ 1)
    {u v : V} (hus : u ∈ s) (huf : u ∉ forbidden)
    (hvs : v ∈ s) (hvf : v ∉ forbidden) :
    ReachableOnAvoiding G s forbidden u v := by
  by_contra huv
  obtain ⟨a, b, hsep, hinter, _⟩ :=
    separationOn_of_not_reachableOnAvoiding G s forbidden hus huf hvs hvf huv
  apply hnlow
  refine ⟨a, b, hsep, ?_⟩
  rw [hinter]
  exact (Finset.card_le_card Finset.inter_subset_right).trans hf

theorem SeparationOn.exists_adj_leftDiff_of_inter_pair
    {G : SimpleGraph V} {s a b : Finset V} {x y : V}
    (h : SeparationOn G s a b) (hxy : x ≠ y) (hi : a ∩ b = {x, y})
    (hnlow : ¬HasLowSeparationOn G s) :
    ∃ z ∈ a \ b, G.Adj x z := by
  classical
  by_contra hex
  push Not at hex
  have hxa : x ∈ a := (Finset.mem_inter.mp (by rw [hi]; simp)).1
  have hxb : x ∈ b := (Finset.mem_inter.mp (by rw [hi]; simp)).2
  have hya : y ∈ a := (Finset.mem_inter.mp (by rw [hi]; simp)).1
  have hyb : y ∈ b := (Finset.mem_inter.mp (by rw [hi]; simp)).2
  let a' := a.erase x
  have hunion : a' ∪ b = s := by
    rw [← h.union_eq]
    ext z
    simp only [a', Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro (⟨_, hza⟩ | hzb)
      · exact Or.inl hza
      · exact Or.inr hzb
    · rintro (hza | hzb)
      · by_cases hzx : z = x
        · subst z
          exact Or.inr hxb
        · exact Or.inl ⟨hzx, hza⟩
      · exact Or.inr hzb
  have hleft : (a' \ b).Nonempty := by
    obtain ⟨z, hz⟩ := h.left_nonempty
    have ⟨hza, hzb⟩ := Finset.mem_sdiff.mp hz
    have hzx : z ≠ x := fun hzx ↦ hzb (hzx ▸ hxb)
    exact ⟨z, Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hzx, hza⟩, hzb⟩⟩
  have hright : (b \ a').Nonempty := by
    obtain ⟨z, hz⟩ := h.right_nonempty
    have ⟨hzb, hza⟩ := Finset.mem_sdiff.mp hz
    exact ⟨z, Finset.mem_sdiff.mpr ⟨hzb, fun hza' ↦ hza (Finset.mem_erase.mp hza').2⟩⟩
  have hnocross : ∀ {u v}, u ∈ a' ∪ b → v ∈ a' ∪ b → G.Adj u v →
      (u ∈ a' ∧ v ∈ a') ∨ (u ∈ b ∧ v ∈ b) := by
    intro u v hu hv huv
    have hu' : u ∈ a ∪ b := h.union_eq.symm ▸ (hunion ▸ hu)
    have hv' : v ∈ a ∪ b := h.union_eq.symm ▸ (hunion ▸ hv)
    rcases h.no_cross hu' hv' huv with haa | hbb
    · by_cases hux : u = x
      · subst u
        by_cases hvb : v ∈ b
        · exact Or.inr ⟨hxb, hvb⟩
        · have hvdiff : v ∈ a \ b := Finset.mem_sdiff.mpr ⟨haa.2, hvb⟩
          exact (hex v hvdiff huv).elim
      · by_cases hvx : v = x
        · subst v
          by_cases hub : u ∈ b
          · exact Or.inr ⟨hub, hxb⟩
          · have hudiff : u ∈ a \ b := Finset.mem_sdiff.mpr ⟨haa.1, hub⟩
            exact (hex u hudiff huv.symm).elim
        · exact Or.inl ⟨Finset.mem_erase.mpr ⟨hux, haa.1⟩,
            Finset.mem_erase.mpr ⟨hvx, haa.2⟩⟩
    · exact Or.inr hbb
  have hinter : a' ∩ b = {y} := by
    ext z
    simp only [a', Finset.mem_inter, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hzx, hza⟩, hzb⟩
      have hz : z = x ∨ z = y := by
        have : z ∈ ({x, y} : Finset V) := hi ▸ Finset.mem_inter.mpr ⟨hza, hzb⟩
        simpa using this
      exact hz.resolve_left hzx
    · rintro rfl
      exact ⟨⟨hxy.symm, hya⟩, hyb⟩
  apply hnlow
  refine ⟨a', b, ⟨hunion, hleft, hright, hnocross⟩, ?_⟩
  rw [hinter]
  simp

theorem componentPath_of_noLowSeparation
    {G : SimpleGraph V} {s a b : Finset V} {x y root : V}
    (hsep : SeparationOn G s a b) (hxy : x ≠ y) (hi : a ∩ b = {x, y})
    (hnlow : ¬HasLowSeparationOn G s)
    (hcomponent : ∀ z, z ∈ s → z ∉ ({x, y} : Finset V) →
      (z ∈ a \ b ↔ ReachableOnAvoiding G s {x, y} root z)) :
    ∃ p : G.Walk x y, ∀ z ∈ p.support, z ∈ a := by
  obtain ⟨rx, hrx, hxrx⟩ :=
    hsep.exists_adj_leftDiff_of_inter_pair hxy hi hnlow
  obtain ⟨ry, hry, hyry⟩ :=
    hsep.exists_adj_leftDiff_of_inter_pair hxy.symm
      (by simpa [Finset.pair_comm] using hi) hnlow
  have hxs : x ∈ a := (Finset.mem_inter.mp (by rw [hi]; simp)).1
  have hys : y ∈ a := (Finset.mem_inter.mp (by rw [hi]; simp)).1
  have hrxs : rx ∈ s := by
    rw [← hsep.union_eq]
    exact Finset.mem_union_left b (Finset.mem_sdiff.mp hrx).1
  have hrys : ry ∈ s := by
    rw [← hsep.union_eq]
    exact Finset.mem_union_left b (Finset.mem_sdiff.mp hry).1
  have hrxf : rx ∉ ({x, y} : Finset V) := by
    intro h
    have : rx = x ∨ rx = y := by simpa using h
    rcases this with rfl | rfl
    · exact (Finset.mem_sdiff.mp hrx).2
        (Finset.mem_inter.mp (by rw [hi]; simp)).2
    · exact (Finset.mem_sdiff.mp hrx).2
        (Finset.mem_inter.mp (by rw [hi]; simp)).2
  have hryf : ry ∉ ({x, y} : Finset V) := by
    intro h
    have : ry = x ∨ ry = y := by simpa using h
    rcases this with rfl | rfl
    · exact (Finset.mem_sdiff.mp hry).2
        (Finset.mem_inter.mp (by rw [hi]; simp)).2
    · exact (Finset.mem_sdiff.mp hry).2
        (Finset.mem_inter.mp (by rw [hi]; simp)).2
  have hrootrx := (hcomponent rx hrxs hrxf).mp hrx
  have hrootry := (hcomponent ry hrys hryf).mp hry
  obtain ⟨prx, hprx⟩ := hrootrx
  obtain ⟨pry, hpry⟩ := hrootry
  let mid : G.Walk rx ry := prx.reverse.append pry
  have hmid_mem : ∀ z ∈ mid.support, z ∈ a := by
    intro z hz
    change z ∈ (prx.reverse.append pry).support at hz
    rw [Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · have hz' : z ∈ prx.support := by simpa using hz
      have hzok := hprx z hz'
      exact (Finset.mem_sdiff.mp ((hcomponent z hzok.1 hzok.2).mpr
        (ReachableOnAvoiding.to_support ⟨prx, hprx⟩ prx hprx hz'))).1
    · have hzok := hpry z hz
      exact (Finset.mem_sdiff.mp ((hcomponent z hzok.1 hzok.2).mpr
        (ReachableOnAvoiding.to_support ⟨pry, hpry⟩ pry hpry hz))).1
  let p : G.Walk x y := Walk.cons hxrx (mid.append (Walk.cons hyry.symm Walk.nil))
  refine ⟨p, ?_⟩
  intro z hz
  have hz' : z = x ∨ z ∈ mid.support ∨ z = ry ∨ z = y := by
    simpa [p] using hz
  rcases hz' with rfl | hz | rfl | rfl
  · exact hxs
  · exact hmid_mem z hz
  · exact (Finset.mem_sdiff.mp hry).1
  · exact hys

theorem twoSeparationOn_of_not_reachable_pair
    {G : SimpleGraph V} {s : Finset V} {x y u v : V}
    (hnlow : ¬HasLowSeparationOn G s)
    (hxy : x ≠ y) (hxs : x ∈ s) (hys : y ∈ s)
    (hus : u ∈ s) (huf : u ∉ ({x, y} : Finset V))
    (hvs : v ∈ s) (hvf : v ∉ ({x, y} : Finset V))
    (huv : ¬ReachableOnAvoiding G s {x, y} u v) :
    Nonempty (TwoSeparationOn G s) := by
  obtain ⟨a, b, hsep, hinter, hcomponent⟩ :=
    separationOn_of_not_reachableOnAvoiding G s {x, y} hus huf hvs hvf huv
  have hsinter : s ∩ ({x, y} : Finset V) = {x, y} := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact fun h ↦ h.2
    · intro hz
      rcases hz with rfl | rfl
      · exact ⟨hxs, Or.inl rfl⟩
      · exact ⟨hys, Or.inr rfl⟩
  have hi : a ∩ b = {x, y} := hinter.trans hsinter
  obtain ⟨leftPath, hleftPath⟩ :=
    componentPath_of_noLowSeparation hsep hxy hi hnlow hcomponent
  have hvu : ¬ReachableOnAvoiding G s {x, y} v u := by
    intro h
    exact huv h.symm
  obtain ⟨c, d, hsep2, hinter2, hcomponent2⟩ :=
    separationOn_of_not_reachableOnAvoiding G s {x, y} hvs hvf hus huf hvu
  have hi2 : c ∩ d = {x, y} := hinter2.trans hsinter
  obtain ⟨rightPath, hrightPathC⟩ :=
    componentPath_of_noLowSeparation hsep2 hxy hi2 hnlow hcomponent2
  have hrightPath : ∀ z ∈ rightPath.support, z ∈ b := by
    intro z hz
    have hzc : z ∈ c := hrightPathC z hz
    have hzs : z ∈ s := by
      rw [← hsep2.union_eq]
      exact Finset.mem_union_left d hzc
    by_cases hzf : z ∈ ({x, y} : Finset V)
    · have hzxy : z = x ∨ z = y := by simpa using hzf
      rcases hzxy with rfl | rfl
      · exact (Finset.mem_inter.mp (by rw [hi]; simp)).2
      · exact (Finset.mem_inter.mp (by rw [hi]; simp)).2
    · by_contra hzb
      have hza : z ∈ a := by
        have : z ∈ a ∪ b := hsep.union_eq.symm ▸ hzs
        exact (Finset.mem_union.mp this).resolve_right hzb
      have hzab : z ∈ a \ b := Finset.mem_sdiff.mpr ⟨hza, hzb⟩
      have huz := (hcomponent z hzs hzf).mp hzab
      have hzd : z ∉ d := by
        intro hzd
        have : z ∈ ({x, y} : Finset V) := hi2 ▸ Finset.mem_inter.mpr ⟨hzc, hzd⟩
        exact hzf this
      have hzcd : z ∈ c \ d := Finset.mem_sdiff.mpr ⟨hzc, hzd⟩
      have hvz := (hcomponent2 z hzs hzf).mp hzcd
      exact huv (huz.trans hvz.symm)
  exact ⟨{
    leftSet := a
    rightSet := b
    sepX := x
    sepY := y
    separation := hsep
    ne := hxy
    inter_eq := hi
    leftPath := leftPath
    leftPath_mem := hleftPath
    rightPath := rightPath
    rightPath_mem := hrightPath
  }⟩

theorem reachableOnAvoiding_of_no_small_separation
    {G : SimpleGraph V} {s forbidden : Finset V}
    (hnlow : ¬HasLowSeparationOn G s)
    (hntwo : ¬Nonempty (TwoSeparationOn G s))
    (hf : forbidden.card ≤ 2)
    {u v : V} (hus : u ∈ s) (huf : u ∉ forbidden)
    (hvs : v ∈ s) (hvf : v ∉ forbidden) :
    ReachableOnAvoiding G s forbidden u v := by
  by_cases hf1 : forbidden.card ≤ 1
  · exact reachableOnAvoiding_of_noLowSeparation hnlow hf1 hus huf hvs hvf
  · by_contra huv
    obtain ⟨a, b, hsep, hinter, _⟩ :=
      separationOn_of_not_reachableOnAvoiding G s forbidden hus huf hvs hvf huv
    have hinter_le : (s ∩ forbidden).card ≤ forbidden.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hinter_two : (s ∩ forbidden).card = 2 := by
      by_contra hi
      apply hnlow
      refine ⟨a, b, hsep, ?_⟩
      rw [hinter]
      omega
    have hf_two : forbidden.card = 2 := by omega
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hf_two
    have hs_pair : s ∩ ({x, y} : Finset V) = {x, y} := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
      simpa [hinter_two, hxy]
    have hxs : x ∈ s := by
      have : x ∈ s ∩ ({x, y} : Finset V) := by rw [hs_pair]; simp
      exact (Finset.mem_inter.mp this).1
    have hys : y ∈ s := by
      have : y ∈ s ∩ ({x, y} : Finset V) := by rw [hs_pair]; simp
      exact (Finset.mem_inter.mp this).1
    apply hntwo
    exact twoSeparationOn_of_not_reachable_pair hnlow hxy hxs hys
      hus huf hvs hvf huv

theorem isCockadeOn_of_card_three_of_edge_count
    (G : SimpleGraph V) (s : Finset V) (hs : s.card = 3)
    (hE : (edgeSetOn G s).ncard = 3) : IsCockadeOn G s := by
  classical
  let K : SimpleGraph (s : Set V) := G.induce (s : Set V)
  letI : DecidableRel K.Adj := Classical.decRel _
  have hKn : K.edgeSet.ncard = 3 := by simpa [K, ncard_edgeSetOn] using hE
  have hKcard : K.edgeFinset.card = 3 := by
    have hn : (K.edgeFinset : Set (Sym2 (s : Set V))).ncard = K.edgeSet.ncard := by simp
    rw [Set.ncard_coe_finset, hKn] at hn
    exact hn
  have htopcard : (⊤ : SimpleGraph (s : Set V)).edgeFinset.card = 3 := by
    rw [card_edgeFinset_top_eq_card_choose_two]
    simpa [hs]
  have hfin : K.edgeFinset = (⊤ : SimpleGraph (s : Set V)).edgeFinset := by
    apply Finset.eq_of_subset_of_card_le (edgeFinset_mono le_top)
    omega
  have htop : K = ⊤ := edgeFinset_inj.mp hfin
  apply IsCockadeOn.triangle
  change K ≃g completeGraph (Fin 3)
  rw [htop]
  exact SimpleGraph.Iso.completeGraph (Finset.equivFinOfCardEq hs)

private def finSixToThreeSum : Fin 6 → Fin 3 ⊕ Fin 3 :=
  ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 1, Sum.inl 2, Sum.inr 2]

private def finThreeSumToSix : Fin 3 ⊕ Fin 3 → Fin 6 :=
  Sum.elim ![0, 2, 4] ![1, 3, 5]

private def finSixEquivThreeSum : Fin 6 ≃ Fin 3 ⊕ Fin 3 where
  toFun := finSixToThreeSum
  invFun := finThreeSumToSix
  left_inv := by decide
  right_inv := by decide

private def turanSixTwoIsoK33 : turanGraph 6 2 ≃g
    completeBipartiteGraph (Fin 3) (Fin 3) where
  __ := finSixEquivThreeSum
  map_rel_iff' := by decide

theorem isCockadeOn_of_card_six_of_edge_count_of_cliqueFree
    (G : SimpleGraph V) (s : Finset V) (hs : s.card = 6)
    (hE : (edgeSetOn G s).ncard = 9)
    (hcf : (G.induce (s : Set V)).CliqueFree 3) : IsCockadeOn G s := by
  classical
  let K : SimpleGraph (s : Set V) := G.induce (s : Set V)
  letI : DecidableRel K.Adj := Classical.decRel _
  have hKn : K.edgeSet.ncard = 9 := by
    simpa [K, ncard_edgeSetOn] using hE
  have hKcard : K.edgeFinset.card = 9 := by
    have hn : (K.edgeFinset : Set (Sym2 (s : Set V))).ncard = K.edgeSet.ncard := by simp
    rw [Set.ncard_coe_finset, hKn] at hn
    exact hn
  have hcard : Fintype.card (s : Set V) = 6 := by simpa using hs
  have hmax : K.IsTuranMaximal 2 := by
    refine ⟨hcf, ?_⟩
    intro H _ hH
    have hbound := hH.card_edgeFinset_le (r := 2)
    simp only [hcard] at hbound
    norm_num at hbound ⊢
    omega
  obtain ⟨e⟩ := (isTuranMaximal_iff_nonempty_iso_turanGraph (G := K)
    (r := 2) (by omega)).mp hmax
  rw [hcard] at e
  have e' : K ≃g turanGraph 6 2 := e
  exact IsCockadeOn.k33 (e'.trans turanSixTwoIsoK33)

noncomputable def neighborFinsetOn (G : SimpleGraph V) (s : Finset V) (x : V) : Finset V :=
  @Finset.filter V (G.Adj x) (Classical.decPred _) s

theorem three_le_card_neighborFinsetOn_of_no_small_separation
    {G : SimpleGraph V} {s : Finset V}
    (hs4 : 4 ≤ s.card)
    (hnlow : ¬HasLowSeparationOn G s)
    (hntwo : ¬Nonempty (TwoSeparationOn G s))
    {x : V} (hxs : x ∈ s) :
    3 ≤ (neighborFinsetOn G s x).card := by
  classical
  by_contra hdeg
  have hdeg2 : (neighborFinsetOn G s x).card ≤ 2 := by omega
  have hins : (insert x (neighborFinsetOn G s x)).card ≤ 3 := by
    calc
      _ ≤ (neighborFinsetOn G s x).card + 1 := Finset.card_insert_le _ _
      _ ≤ 3 := by omega
  have hnsub : ¬s ⊆ insert x (neighborFinsetOn G s x) := by
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨v, hvs, hvnot⟩ := Finset.not_subset.mp hnsub
  have hvx : v ≠ x := by
    intro h
    exact hvnot (Finset.mem_insert.mpr (Or.inl h))
  have hvn : v ∉ neighborFinsetOn G s x := by
    intro h
    exact hvnot (Finset.mem_insert_of_mem h)
  have hxn : x ∉ neighborFinsetOn G s x := by
    simp [neighborFinsetOn]
  have hreach := reachableOnAvoiding_of_no_small_separation hnlow hntwo hdeg2
    hxs hxn hvs hvn
  obtain ⟨p, hp⟩ := hreach
  have hxv : x ≠ v := fun h ↦ hvx h.symm
  have hpnon : ¬ p.Nil := Walk.not_nil_of_ne hxv
  have hadj : G.Adj x p.snd := p.adj_snd hpnon
  have hsnd := hp p.snd (List.mem_of_mem_tail (p.snd_mem_tail_support hpnon))
  exact hsnd.2 (Finset.mem_filter.mpr ⟨hsnd.1, hadj⟩)

theorem exists_card_neighborFinsetOn_eq_three_of_core_exact
    {G : SimpleGraph V} {s : Finset V}
    (hs4 : 4 ≤ s.card)
    (hnlow : ¬HasLowSeparationOn G s)
    (hntwo : ¬Nonempty (TwoSeparationOn G s))
    (hE : (edgeSetOn G s).ncard = 2 * s.card - 3) :
    ∃ x ∈ s, (neighborFinsetOn G s x).card = 3 := by
  classical
  letI : Fintype (s : Set V) := FinsetCoe.fintype s
  let K : SimpleGraph (s : Set V) := G.induce (s : Set V)
  letI : DecidableRel K.Adj := Classical.decRel _
  have degree_eq (x : s) : K.degree x = (neighborFinsetOn G s x).card := by
    change (K.neighborFinset x).card = (neighborFinsetOn G s x).card
    refine Finset.card_bij (s := K.neighborFinset x)
      (t := neighborFinsetOn G s x) (fun y _ ↦ (y : V)) ?_ ?_ ?_
    · intro y hy
      exact Finset.mem_filter.mpr ⟨y.property, by
        simpa [K] using ((K.mem_neighborFinset x y).mp hy)⟩
    · intro y₁ _ y₂ _ h
      exact Subtype.ext h
    · intro y hy
      have hy' := Finset.mem_filter.mp hy
      refine ⟨⟨y, hy'.1⟩, ?_, rfl⟩
      apply (K.mem_neighborFinset x ⟨y, hy'.1⟩).mpr
      simpa [K] using hy'.2
  have hdeg (x : s) : 3 ≤ K.degree x := by
    have hx := three_le_card_neighborFinsetOn_of_no_small_separation hs4 hnlow hntwo x.property
    rw [degree_eq]
    exact hx
  by_contra hex
  push Not at hex
  have hdeg4 (x : s) : 4 ≤ K.degree x := by
    have hx3 := hdeg x
    have hxne : K.degree x ≠ 3 := by
      intro hx
      exact hex x x.property ((degree_eq x).symm.trans hx)
    omega
  have hsum_lower : 4 * s.card ≤ ∑ x : s, K.degree x := by
    calc
      4 * s.card = ∑ _x : s, 4 := by simp [Nat.mul_comm]
      _ ≤ ∑ x : s, K.degree x := Finset.sum_le_sum fun x _ ↦ hdeg4 x
  have hsum : (∑ x : s, K.degree x) = 2 * K.edgeFinset.card :=
    K.sum_degrees_eq_twice_card_edges
  have hKedges : K.edgeFinset.card = 2 * s.card - 3 := by
    have hn : (K.edgeFinset : Set (Sym2 (s : Set V))).ncard = K.edgeSet.ncard := by simp
    rw [Set.ncard_coe_finset] at hn
    rw [hn, ← ncard_edgeSetOn]
    exact hE
  omega

omit [Fintype V] in
theorem exists_cycle_of_edge_and_avoiding_path
    {G : SimpleGraph V} {b c e : V}
    (hbc : G.Adj b c) (hbe : G.Adj b e) (hec : e ≠ c)
    (p : G.Walk e c) (hp : p.IsPath) (hbp : b ∉ p.support) :
    ∃ z : G.Walk b b, z.IsCycle ∧ s(b, c) ∈ z.edges ∧
      ∀ v ∈ z.support, v = b ∨ v ∈ p.support := by
  let q : G.Walk b c := Walk.cons hbe p
  have hq : q.IsPath := by
    exact hp.cons hbp
  let r : G.Walk b c := Walk.cons hbc Walk.nil
  have hr : r.IsPath := by simp [r, hbc.ne]
  have hdisjoint : r.support.tail.Disjoint q.reverse.support.tail := by
    rw [List.disjoint_left]
    intro v hvr hvq
    have hvc : v = c := by simpa [r] using hvr
    subst v
    have hn := hq.reverse.support_nodup
    rw [← Walk.cons_tail_support q.reverse] at hn
    exact (List.nodup_cons.mp hn).1 hvq
  have hlen : 1 < q.reverse.length := by
    simp only [Walk.length_reverse, q, Walk.length_cons]
    have hpne : p.length ≠ 0 := fun h ↦ hec (p.eq_of_length_eq_zero h)
    have : 0 < p.length := Nat.pos_of_ne_zero hpne
    omega
  have hcycle : (r.append q.reverse).IsCycle :=
    hr.isCycle_append hq.reverse hdisjoint (Or.inr hlen)
  refine ⟨r.append q.reverse, hcycle, ?_, ?_⟩
  · simp [r]
  · intro v hv
    rw [Walk.mem_support_append_iff] at hv
    rcases hv with hv | hv
    · have : v = b ∨ v = c := by simpa [r] using hv
      rcases this with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Walk.end_mem_support p)
    · have hvq : v ∈ q.support := by simpa using hv
      have : v = b ∨ v ∈ p.support := by simpa [q] using hvq
      exact this

theorem hasThreeSpokeCycle_of_triangle_of_edge_vertex_cycle
    {G : SimpleGraph V} {s : Finset V}
    (hs4 : 4 ≤ s.card)
    (hnlow : ¬HasLowSeparationOn G s)
    (hntwo : ¬Nonempty (TwoSeparationOn G s))
    {a b c : V} (has : a ∈ s) (hbs : b ∈ s) (hcs : c ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (habAdj : G.Adj a b) (hacAdj : G.Adj a c) (hbcAdj : G.Adj b c)
    (hdirac : ∀ {d : V}, d ∈ s → d ≠ a → d ≠ b → d ≠ c → G.Adj a d →
      ∃ (v : V) (z : G.Walk v v), z.IsCycle ∧ a ∉ z.support ∧
        (∀ w ∈ z.support, w ∈ s) ∧ b ∈ z.support ∧ c ∈ z.support ∧ d ∈ z.support) :
    HasThreeSpokeCycleTest G := by
  classical
  let n := neighborFinsetOn G s a
  have hn3 : 3 ≤ n.card :=
    three_le_card_neighborFinsetOn_of_no_small_separation hs4 hnlow hntwo has
  have hbn : b ∈ n := Finset.mem_filter.mpr ⟨hbs, habAdj⟩
  have hcn : c ∈ n := Finset.mem_filter.mpr ⟨hcs, hacAdj⟩
  have hnsub : ¬n ⊆ {b, c} := by
    intro hsub
    have hcard := Finset.card_le_card hsub
    have hpair : ({b, c} : Finset V).card = 2 := Finset.card_pair hbc
    omega
  obtain ⟨d, hdn, hdnot⟩ := Finset.not_subset.mp hnsub
  have hds : d ∈ s := (Finset.mem_filter.mp hdn).1
  have had : G.Adj a d := (Finset.mem_filter.mp hdn).2
  have hdb : d ≠ b := by
    intro h
    exact hdnot (by simp [h])
  have hdc : d ≠ c := by
    intro h
    exact hdnot (by simp [h])
  have hda : d ≠ a := had.ne.symm
  obtain ⟨v, z, hzcycle, haz, hzs, hbz, hcz, hdz⟩ :=
    hdirac hds hda hdb hdc had
  refine ⟨v, a, z, hzcycle, haz, b, hbz, c, hcz, d, hdz,
    hbc, ?_, ?_, habAdj, hacAdj, had⟩
  · exact fun h ↦ hdb h.symm
  · exact fun h ↦ hdc h.symm

/-! The following local cycle-extension lemmas replace the usual two-fan
lemma.  Keeping a distinguished edge on the cycle is exactly what is needed
for the triangle case of Thomassen's argument. -/

omit [Fintype V] in
theorem extend_cycle_preserving_edge
    {G : SimpleGraph V} {s : Finset V} {a b c u v w : V}
    {C : G.Walk w w}
    (hC : C.IsCycle) (haC : a ∉ C.support) (hbcC : s(b, c) ∈ C.edges)
    (huC : u ∈ C.support) (hvC : v ∉ C.support) (huv : G.Adj u v)
    (hCs : ∀ z ∈ C.support, z ∈ s)
    (hreach : ∀ {t}, t ∈ C.support → t ≠ u →
      ReachableOnAvoiding G s {a, u} v t) :
    ∃ (w : V) (D : G.Walk w w), D.IsCycle ∧ a ∉ D.support ∧
      s(b, c) ∈ D.edges ∧ v ∈ D.support ∧
      (∀ z ∈ D.support, z ∈ s) := by
  classical
  have hbc : b ≠ c := by
    exact (C.adj_of_mem_edges hbcC).ne
  have hbC : b ∈ C.support := C.fst_mem_support_of_mem_edges hbcC
  have hcC : c ∈ C.support := C.snd_mem_support_of_mem_edges hbcC
  let t : V := if u = b then c else b
  have htC : t ∈ C.support := by
    simp only [t]
    split <;> assumption
  have htu : t ≠ u := by
    simp only [t]
    split
    · rename_i hub
      subst u
      exact hbc.symm
    · rename_i hub
      exact fun h ↦ hub h.symm
  obtain ⟨q, hqmem⟩ := hreach htC htu
  let q' : G.Walk v t := q.toPath
  have hq' : q'.IsPath := Walk.bypass_isPath q
  have hq's : ∀ z ∈ q'.support, z ∈ s := by
    intro z hz
    exact (hqmem z (q.support_bypass_subset_support hz)).1
  have hq'f : ∀ z ∈ q'.support, z ∉ ({a, u} : Finset V) := by
    intro z hz
    exact (hqmem z (q.support_bypass_subset_support hz)).2
  let P : ℕ → Prop := fun n ↦
    ∃ (x : V) (p : G.Walk v x), x ∈ C.support ∧ p.IsPath ∧
      (∀ z ∈ p.support, z ∈ s) ∧
      (∀ z ∈ p.support, z ∉ ({a, u} : Finset V)) ∧ p.length = n
  have hP : ∃ n, P n :=
    ⟨q'.length, t, q', htC, hq', hq's, hq'f, rfl⟩
  let n := Nat.find hP
  obtain ⟨x, p, hxC, hp, hps, hpf, hplen⟩ := Nat.find_spec hP
  have hnmin {y : V} {r : G.Walk v y} (hyC : y ∈ C.support)
      (hr : r.IsPath) (hrs : ∀ z ∈ r.support, z ∈ s)
      (hrf : ∀ z ∈ r.support, z ∉ ({a, u} : Finset V)) :
      n ≤ r.length := by
    exact Nat.find_min' hP ⟨y, r, hyC, hr, hrs, hrf, rfl⟩
  have hmeet : ∀ z ∈ p.support, z ∈ C.support → z = x := by
    intro z hzp hzC
    by_contra hzx
    let r := p.takeUntil z hzp
    have hr : r.IsPath := hp.takeUntil hzp
    have hrs : ∀ y ∈ r.support, y ∈ s := by
      intro y hy
      exact hps y (p.support_takeUntil_subset_support hzp hy)
    have hrf : ∀ y ∈ r.support, y ∉ ({a, u} : Finset V) := by
      intro y hy
      exact hpf y (p.support_takeUntil_subset_support hzp hy)
    have hmin := hnmin hzC hr hrs hrf
    have hlt : r.length < p.length := p.length_takeUntil_lt_length hzp hzx
    omega
  have hxu : x ≠ u := by
    intro h
    have := hpf x (Walk.end_mem_support p)
    simp [h] at this
  let R : G.Walk u u := C.rotate u huC
  have hR : R.IsCycle := hC.rotate huC
  have hxR : x ∈ R.support := by
    simpa [R, Walk.support_rotate] using hxC
  let A : G.Walk u x := R.takeUntil x hxR
  let B : G.Walk x u := R.dropUntil x hxR
  have hA : A.IsPath := hR.isPath_takeUntil hxR
  have hAnon : ¬ A.Nil := Walk.not_nil_of_ne hxu.symm
  have hAB : (A.append B).IsCycle := by
    simpa [A, B] using hR
  have hB : B.IsPath := hAB.isPath_of_append_right hAnon
  have hbcR : s(b, c) ∈ R.edges := by
    have hp := C.rotate_edges u huC
    exact hp.mem_iff.mpr hbcC
  have hbcAB : s(b, c) ∈ A.edges ∨ s(b, c) ∈ B.edges := by
    have hABeq : A.append B = R := by
      exact R.take_spec hxR
    have hbcAppend : s(b, c) ∈ (A.append B).edges := by
      rw [hABeq]
      exact hbcR
    simpa [Walk.edges_append] using hbcAppend
  let T : G.Walk x u := if h : s(b, c) ∈ A.edges then A.reverse else B
  have hT : T.IsPath := by
    simp only [T]
    split
    · exact hA.reverse
    · exact hB
  have hbcT : s(b, c) ∈ T.edges := by
    simp only [T]
    split
    · rename_i h
      simpa using h
    · rename_i h
      exact hbcAB.resolve_left h
  have hTs : ∀ z ∈ T.support, z ∈ C.support := by
    intro z hz
    simp only [T] at hz
    split at hz
    · rename_i h
      have hzA : z ∈ A.support := by simpa using hz
      have hzR := R.support_takeUntil_subset_support hxR hzA
      simpa [R, Walk.support_rotate] using hzR
    · have hzR := R.support_dropUntil_subset_support hxR hz
      simpa [R, Walk.support_rotate] using hzR
  have huP : u ∉ p.support := by
    intro h
    exact hpf u h (by simp)
  have hvu : v ≠ u := by
    intro h
    exact huP (h.symm ▸ Walk.start_mem_support p)
  let Q : G.Walk u x := Walk.cons huv p
  have hQ : Q.IsPath := hp.cons huP
  have hdisj : Q.support.tail.Disjoint T.support.tail := by
    rw [List.disjoint_left]
    intro z hzQ hzT
    have hzp : z ∈ p.support := by simpa [Q] using hzQ
    have hzC : z ∈ C.support := hTs z (List.mem_of_mem_tail hzT)
    have hzx : z = x := hmeet z hzp hzC
    subst z
    have hn := hT.support_nodup
    rw [← Walk.cons_tail_support T] at hn
    exact (List.nodup_cons.mp hn).1 hzT
  have hQlen : 1 < Q.length := by
    have hvx : v ≠ x := by
      intro h
      exact hvC (h ▸ hxC)
    have hpnon : 0 < p.length := Nat.pos_of_ne_zero fun h ↦ hvx (p.eq_of_length_eq_zero h)
    simp [Q]
    omega
  have hD : (Q.append T).IsCycle := hQ.isCycle_append hT hdisj (Or.inl hQlen)
  refine ⟨u, Q.append T, hD, ?_, ?_, ?_, ?_⟩
  · intro ha
    rw [Walk.mem_support_append_iff] at ha
    rcases ha with haQ | haT
    · have : a = u ∨ a ∈ p.support := by simpa [Q] using haQ
      rcases this with hau | hap
      · exact haC (hau ▸ huC)
      · exact hpf a hap (by simp)
    · exact haC (hTs a haT)
  · rw [Walk.edges_append]
    exact List.mem_append.mpr (Or.inr hbcT)
  · rw [Walk.mem_support_append_iff]
    left
    simp [Q]
  · intro z hz
    rw [Walk.mem_support_append_iff] at hz
    rcases hz with hzQ | hzT
    · have : z = u ∨ z ∈ p.support := by simpa [Q] using hzQ
      rcases this with rfl | hzp
      · exact hCs _ huC
      · exact hps z hzp
    · exact hCs z (hTs z hzT)

omit [Fintype V] in
theorem IsTwoConnectedOn.extend_cycle_preserving_edge
    {G : SimpleGraph V} {s : Finset V} {b c u v w : V}
    {C : G.Walk w w}
    (hconn : IsTwoConnectedOn G s)
    (hC : C.IsCycle) (hbcC : s(b, c) ∈ C.edges)
    (huC : u ∈ C.support) (hvC : v ∉ C.support) (huv : G.Adj u v)
    (hCs : ∀ z ∈ C.support, z ∈ s) (hvs : v ∈ s) :
    ∃ (w : V) (D : G.Walk w w), D.IsCycle ∧
      s(b, c) ∈ D.edges ∧ v ∈ D.support ∧
      (∀ z ∈ D.support, z ∈ s) := by
  classical
  have hbc : b ≠ c := (C.adj_of_mem_edges hbcC).ne
  have hbC : b ∈ C.support := C.fst_mem_support_of_mem_edges hbcC
  have hcC : c ∈ C.support := C.snd_mem_support_of_mem_edges hbcC
  let t : V := if u = b then c else b
  have htC : t ∈ C.support := by
    simp only [t]
    split <;> assumption
  have htu : t ≠ u := by
    simp only [t]
    split
    · rename_i hub
      subst u
      exact hbc.symm
    · rename_i hub
      exact fun h ↦ hub h.symm
  have hvu : v ≠ u := by
    intro h
    exact hvC (h ▸ huC)
  have hts : t ∈ s := hCs t htC
  obtain ⟨q, hq, hqs, huq⟩ := hconn hvs hts hvu htu
  let P : ℕ → Prop := fun n ↦
    ∃ (x : V) (p : G.Walk v x), x ∈ C.support ∧ p.IsPath ∧
      (∀ z ∈ p.support, z ∈ s) ∧ u ∉ p.support ∧ p.length = n
  have hP : ∃ n, P n := ⟨q.length, t, q, htC, hq, hqs, huq, rfl⟩
  let n := Nat.find hP
  obtain ⟨x, p, hxC, hp, hps, hup, hplen⟩ := Nat.find_spec hP
  have hnmin {y : V} {r : G.Walk v y} (hyC : y ∈ C.support)
      (hr : r.IsPath) (hrs : ∀ z ∈ r.support, z ∈ s)
      (hru : u ∉ r.support) : n ≤ r.length := by
    exact Nat.find_min' hP ⟨y, r, hyC, hr, hrs, hru, rfl⟩
  have hmeet : ∀ z ∈ p.support, z ∈ C.support → z = x := by
    intro z hzp hzC
    by_contra hzx
    let r := p.takeUntil z hzp
    have hr : r.IsPath := hp.takeUntil hzp
    have hrs : ∀ y ∈ r.support, y ∈ s := by
      intro y hy
      exact hps y (p.support_takeUntil_subset_support hzp hy)
    have hru : u ∉ r.support := by
      intro hu
      exact hup (p.support_takeUntil_subset_support hzp hu)
    have hmin := hnmin hzC hr hrs hru
    have hlt : r.length < p.length := p.length_takeUntil_lt_length hzp hzx
    omega
  have hxu : x ≠ u := by
    intro h
    exact hup (h ▸ Walk.end_mem_support p)
  let R : G.Walk u u := C.rotate u huC
  have hR : R.IsCycle := hC.rotate huC
  have hxR : x ∈ R.support := by
    simpa [R, Walk.support_rotate] using hxC
  let A : G.Walk u x := R.takeUntil x hxR
  let B : G.Walk x u := R.dropUntil x hxR
  have hA : A.IsPath := hR.isPath_takeUntil hxR
  have hAnon : ¬A.Nil := Walk.not_nil_of_ne hxu.symm
  have hAB : (A.append B).IsCycle := by
    simpa [A, B] using hR
  have hB : B.IsPath := hAB.isPath_of_append_right hAnon
  have hbcR : s(b, c) ∈ R.edges := by
    exact (C.rotate_edges u huC).mem_iff.mpr hbcC
  have hbcAB : s(b, c) ∈ A.edges ∨ s(b, c) ∈ B.edges := by
    have hABeq : A.append B = R := R.take_spec hxR
    have : s(b, c) ∈ (A.append B).edges := by simpa [hABeq] using hbcR
    simpa [Walk.edges_append] using this
  let T : G.Walk x u := if h : s(b, c) ∈ A.edges then A.reverse else B
  have hT : T.IsPath := by
    simp only [T]
    split
    · exact hA.reverse
    · exact hB
  have hbcT : s(b, c) ∈ T.edges := by
    simp only [T]
    split
    · rename_i h
      simpa using h
    · rename_i h
      exact hbcAB.resolve_left h
  have hTs : ∀ z ∈ T.support, z ∈ C.support := by
    intro z hz
    simp only [T] at hz
    split at hz
    · have hzA : z ∈ A.support := by simpa using hz
      have hzR := R.support_takeUntil_subset_support hxR hzA
      simpa [R, Walk.support_rotate] using hzR
    · have hzR := R.support_dropUntil_subset_support hxR hz
      simpa [R, Walk.support_rotate] using hzR
  let Q : G.Walk u x := Walk.cons huv p
  have hQ : Q.IsPath := hp.cons hup
  have hdisj : Q.support.tail.Disjoint T.support.tail := by
    rw [List.disjoint_left]
    intro z hzQ hzT
    have hzp : z ∈ p.support := by simpa [Q] using hzQ
    have hzC : z ∈ C.support := hTs z (List.mem_of_mem_tail hzT)
    have hzx : z = x := hmeet z hzp hzC
    subst z
    have hn := hT.support_nodup
    rw [← Walk.cons_tail_support T] at hn
    exact (List.nodup_cons.mp hn).1 hzT
  have hQlen : 1 < Q.length := by
    have hvx : v ≠ x := by
      intro h
      exact hvC (h ▸ hxC)
    have hpnon : 0 < p.length := Nat.pos_of_ne_zero fun h ↦ hvx (p.eq_of_length_eq_zero h)
    simp [Q]
    omega
  have hD : (Q.append T).IsCycle := hQ.isCycle_append hT hdisj (Or.inl hQlen)
  refine ⟨u, Q.append T, hD, ?_, ?_, ?_⟩
  · rw [Walk.edges_append]
    exact List.mem_append.mpr (Or.inr hbcT)
  · rw [Walk.mem_support_append_iff]
    left
    simp [Q]
  · intro z hz
    rw [Walk.mem_support_append_iff] at hz
    rcases hz with hzQ | hzT
    · have : z = u ∨ z ∈ p.support := by simpa [Q] using hzQ
      rcases this with rfl | hzp
      · exact hCs _ huC
      · exact hps z hzp
    · exact hCs z (hTs z hzT)

omit [Fintype V] in
theorem Walk.exists_adj_crossing_finset {G : SimpleGraph V} {U : Finset V}
    {x y : V} (p : G.Walk x y) (hx : x ∈ U) (hy : y ∉ U) :
    ∃ u v, u ∈ p.support ∧ v ∈ p.support ∧ G.Adj u v ∧ u ∈ U ∧ v ∉ U := by
  induction p with
  | nil => exact (hy hx).elim
  | @cons u v w huv p ih =>
      by_cases hv : v ∈ U
      · obtain ⟨r, t, hrp, htp, hrt, hrU, htU⟩ := ih hv hy
        exact ⟨r, t, by simp [hrp], by simp [htp], hrt, hrU, htU⟩
      · exact ⟨u, v, by simp, by simp, huv, hx, hv⟩

theorem IsTwoConnectedOn.exists_cycle_containing_edge_and_vertex
    {G : SimpleGraph V} {s : Finset V} (hconn : IsTwoConnectedOn G s)
    {b c d : V} (hbs : b ∈ s) (hds : d ∈ s)
    {C : G.Walk b b} (hC : C.IsCycle) (hbcC : s(b, c) ∈ C.edges)
    (hCs : ∀ z ∈ C.support, z ∈ s) :
    ∃ (w : V) (D : G.Walk w w), D.IsCycle ∧
      s(b, c) ∈ D.edges ∧ d ∈ D.support ∧
      (∀ z ∈ D.support, z ∈ s) := by
  classical
  let Good : V → Prop := fun x ↦
    ∃ (w : V) (D : G.Walk w w), D.IsCycle ∧
      s(b, c) ∈ D.edges ∧ x ∈ D.support ∧
      (∀ z ∈ D.support, z ∈ s)
  let U : Finset V := s.filter Good
  have hbGood : Good b :=
    ⟨b, C, hC, hbcC, Walk.start_mem_support C, hCs⟩
  have hbU : b ∈ U := Finset.mem_filter.mpr ⟨hbs, hbGood⟩
  by_cases hdU : d ∈ U
  · exact (Finset.mem_filter.mp hdU).2
  · have hdc : d ≠ c := by
      intro h
      subst d
      apply hdU
      have hcGood : Good c :=
        ⟨b, C, hC, hbcC, C.snd_mem_support_of_mem_edges hbcC, hCs⟩
      exact Finset.mem_filter.mpr ⟨hds, hcGood⟩
    have hbc : b ≠ c := (C.adj_of_mem_edges hbcC).ne
    obtain ⟨p, hp, hps, hcp⟩ := hconn hbs hds hbc hdc
    obtain ⟨u, v, hup, hvp, huv, huU, hvU⟩ :=
      Walk.exists_adj_crossing_finset p hbU hdU
    have hvs : v ∈ s := hps v hvp
    obtain ⟨wu, Cu, hCu, hbcCu, huCu, hCus⟩ :=
      (Finset.mem_filter.mp huU).2
    have hvCu : v ∉ Cu.support := by
      intro hv
      apply hvU
      exact Finset.mem_filter.mpr ⟨hvs, wu, Cu, hCu, hbcCu, hv, hCus⟩
    obtain ⟨wv, Cv, hCv, hbcCv, hvCv, hCvs⟩ :=
      hconn.extend_cycle_preserving_edge hCu hbcCu huCu hvCu huv hCus hvs
    exfalso
    apply hvU
    exact Finset.mem_filter.mpr ⟨hvs, wv, Cv, hCv, hbcCv, hvCv, hCvs⟩

/-- Replace all edges at `x` by edges from `x` to the vertices in `t`. -/
def coneAt (G : SimpleGraph V) (x : V) (t : Finset V) : SimpleGraph V :=
  { Adj := fun u v ↦ u ≠ v ∧
      ((u ≠ x ∧ v ≠ x ∧ G.Adj u v) ∨
        (u = x ∧ v ∈ t) ∨ (v = x ∧ u ∈ t))
    symm := ⟨by
      intro u v h
      refine ⟨h.1.symm, ?_⟩
      rcases h.2 with h | h | h
      · exact Or.inl ⟨h.2.1, h.1, h.2.2.symm⟩
      · exact Or.inr (Or.inr ⟨h.1, h.2⟩)
      · exact Or.inr (Or.inl ⟨h.1, h.2⟩)⟩
    loopless := ⟨by
      intro u h
      exact h.1 rfl⟩ }

@[simp]
theorem coneAt_adj {G : SimpleGraph V} {x u v : V} {t : Finset V} :
    (coneAt G x t).Adj u v ↔ u ≠ v ∧
      ((u ≠ x ∧ v ≠ x ∧ G.Adj u v) ∨
        (u = x ∧ v ∈ t) ∨ (v = x ∧ u ∈ t)) := Iff.rfl

theorem coneAt_adj_of_original {G : SimpleGraph V} {x u v : V} {t : Finset V}
    (huv : G.Adj u v) (hux : u ≠ x) (hvx : v ≠ x) :
    (coneAt G x t).Adj u v :=
  ⟨huv.ne, Or.inl ⟨hux, hvx, huv⟩⟩

theorem coneAt_adj_center {G : SimpleGraph V} {x z : V} {t : Finset V}
    (hzt : z ∈ t) (hzx : z ≠ x) : (coneAt G x t).Adj x z :=
  ⟨hzx.symm, Or.inr (Or.inl ⟨rfl, hzt⟩)⟩

theorem coneAt_mem_of_adj_center {G : SimpleGraph V} {x z : V} {t : Finset V}
    (h : (coneAt G x t).Adj x z) : z ∈ t := by
  rcases h.2 with h | h | h
  · exact (h.1 rfl).elim
  · exact h.2
  · simpa [h.1] using h.2

theorem Walk.IsPath.extract_between_finset_through
    {G : SimpleGraph V} {a b d : V} {p : G.Walk a b}
    (hp : p.IsPath) {t : Finset V} (hat : a ∈ t) (hbt : b ∈ t)
    (hdt : d ∉ t) (hdp : d ∈ p.support) :
    ∃ z₁ z₂, ∃ q : G.Walk z₁ z₂, z₁ ∈ t ∧ z₂ ∈ t ∧ z₁ ≠ z₂ ∧
      q.IsPath ∧ d ∈ q.support ∧
      (∀ y ∈ q.support, y ∈ p.support) ∧
      (∀ y ∈ q.support, y ∈ t → y = z₁ ∨ y = z₂) := by
  classical
  let L : G.Walk a d := p.takeUntil d hdp
  let R : G.Walk d b := p.dropUntil d hdp
  let LR : G.Walk d a := L.reverse
  have hLRnon : {y ∈ t | y ∈ LR.support}.Nonempty := by
    refine ⟨a, Finset.mem_filter.mpr ⟨hat, ?_⟩⟩
    exact Walk.end_mem_support LR
  obtain ⟨z₁, hz₁t, hz₁LR, hz₁first⟩ :=
    LR.exists_mem_support_forall_mem_support_imp_eq t hLRnon
  have hRnon : {y ∈ t | y ∈ R.support}.Nonempty := by
    refine ⟨b, Finset.mem_filter.mpr ⟨hbt, ?_⟩⟩
    exact Walk.end_mem_support R
  obtain ⟨z₂, hz₂t, hz₂R, hz₂first⟩ :=
    R.exists_mem_support_forall_mem_support_imp_eq t hRnon
  let p₁ : G.Walk d z₁ := LR.takeUntil z₁ hz₁LR
  let p₂ : G.Walk d z₂ := R.takeUntil z₂ hz₂R
  have hp₁ : p₁.IsPath := (hp.takeUntil hdp).reverse.takeUntil hz₁LR
  have hp₂ : p₂.IsPath := (hp.dropUntil hdp).takeUntil hz₂R
  have hsplit : L.append R = p := p.take_spec hdp
  have hsplitPath : (L.append R).IsPath := by simpa [hsplit] using hp
  have hdb : d ≠ b := by
    intro h
    exact hdt (h ▸ hbt)
  have hRnotNil : ¬R.Nil := Walk.not_nil_of_ne hdb
  have hLRdisj : L.support.Disjoint R.tail.support :=
    hsplitPath.disjoint_support_of_append hRnotNil
  have hdisj : p₁.reverse.support.Disjoint p₂.support.tail := by
    rw [List.disjoint_left]
    intro y hyp₁ hyp₂
    have hyLR : y ∈ LR.support :=
      LR.support_takeUntil_subset_support hz₁LR (by simpa [p₁] using hyp₁)
    have hyL : y ∈ L.support := by simpa [LR] using hyLR
    have hyp₂full : y ∈ p₂.support := List.mem_of_mem_tail hyp₂
    have hyR : y ∈ R.support :=
      R.support_takeUntil_subset_support hz₂R hyp₂full
    have hyd : y ≠ d := by
      intro h
      subst y
      have hn := hp₂.support_nodup
      rw [← Walk.cons_tail_support p₂] at hn
      exact (List.nodup_cons.mp hn).1 hyp₂
    have hyRtail : y ∈ R.support.tail := by
      rw [Walk.mem_support_iff] at hyR
      exact hyR.resolve_left hyd
    have hyRtail' : y ∈ R.tail.support := by
      rw [R.support_tail_of_not_nil hRnotNil]
      exact hyRtail
    exact hLRdisj hyL hyRtail'
  have hz₁ne : z₁ ≠ z₂ := by
    intro h
    have hz₁p : z₁ ∈ p₁.reverse.support := by
      simpa [p₁] using Walk.end_mem_support p₁
    have hz₂d : z₂ ≠ d := by
      intro hzd
      exact hdt (hzd ▸ hz₂t)
    have hz₂tail : z₂ ∈ p₂.support.tail := by
      have hz₂p : z₂ ∈ p₂.support := Walk.end_mem_support p₂
      rw [Walk.mem_support_iff] at hz₂p
      exact hz₂p.resolve_left hz₂d
    exact hdisj hz₁p (h ▸ hz₂tail)
  let q : G.Walk z₁ z₂ := p₁.reverse.append p₂
  have hq : q.IsPath := by
    change (p₁.reverse.append p₂).IsPath
    rw [Walk.isPath_def, Walk.support_append, List.nodup_append']
    exact ⟨hp₁.reverse.support_nodup, hp₂.support_nodup.tail, hdisj⟩
  refine ⟨z₁, z₂, q, hz₁t, hz₂t, hz₁ne, hq, ?_, ?_, ?_⟩
  · rw [Walk.mem_support_append_iff]
    left
    exact Walk.end_mem_support p₁.reverse
  · intro y hy
    rw [Walk.mem_support_append_iff] at hy
    rcases hy with hyp₁ | hyp₂
    · have hyp₁' : y ∈ p₁.support := by simpa using hyp₁
      have hyLR := LR.support_takeUntil_subset_support hz₁LR hyp₁'
      have hyL : y ∈ L.support := by simpa [LR] using hyLR
      exact p.support_takeUntil_subset_support hdp hyL
    · have hyR := R.support_takeUntil_subset_support hz₂R hyp₂
      exact p.support_dropUntil_subset_support hdp hyR
  · intro y hy hyt
    rw [Walk.mem_support_append_iff] at hy
    rcases hy with hyp₁ | hyp₂
    · left
      have hyp₁' : y ∈ p₁.support := by simpa using hyp₁
      exact hz₁first y hyt hyp₁'
    · right
      exact hz₂first y hyt hyp₂

theorem Walk.takeUntil_append_of_not_mem_left
    {G : SimpleGraph V} {u v w x : V} (p : G.Walk u v) (q : G.Walk v w)
    (hxq : x ∈ q.support) (hxp : x ∉ p.support) :
    (p.append q).takeUntil x (p.support_subset_support_append_right q hxq) =
      p.append (q.takeUntil x hxq) := by
  induction p with
  | nil => simp
  | @cons a b v hab p ih =>
      have hax : a ≠ x := by
        intro h
        exact hxp (h ▸ Walk.start_mem_support _)
      have hxp' : x ∉ p.support := by
        intro h
        exact hxp (by simp [h])
      calc
        ((Walk.cons hab p).append q).takeUntil x _ =
            Walk.cons hab ((p.append q).takeUntil x _) := by
              exact Walk.takeUntil_cons
                (p := p.append q) (p.support_subset_support_append_right q hxq) hax hab
        _ = Walk.cons hab (p.append (q.takeUntil x hxq)) := by
              rw [ih q hxq hxp']
        _ = (Walk.cons hab p).append (q.takeUntil x hxq) := rfl

theorem Walk.mem_support_takeUntil_of_idxOf_le
    {G : SimpleGraph V} {u v x y : V}
    (p : G.Walk u v) (hx : x ∈ p.support) (hy : y ∈ p.support)
    (h : p.support.idxOf y ≤ p.support.idxOf x) :
    y ∈ (p.takeUntil x hx).support := by
  rw [Walk.takeUntil_eq_take, Walk.support_copy, Walk.support_take]
  rw [List.mem_take_iff_idxOf_lt hy]
  omega

theorem Walk.mem_support_dropUntil_of_idxOf_le
    {G : SimpleGraph V} {u v x y : V}
    (p : G.Walk u v) (hx : x ∈ p.support) (hy : y ∈ p.support)
    (h : p.support.idxOf x ≤ p.support.idxOf y) :
    y ∈ (p.dropUntil x hx).support := by
  rw [Walk.dropUntil_eq_drop, Walk.support_copy,
    Walk.drop_support_eq_support_drop_min]
  have hxle : p.support.idxOf x ≤ p.length := by
    have hxlt := List.idxOf_lt_length_of_mem hx
    rw [Walk.length_support] at hxlt
    omega
  rw [Nat.min_eq_left hxle]
  rw [List.mem_iff_getElem]
  refine ⟨p.support.idxOf y - p.support.idxOf x, ?_, ?_⟩
  · rw [List.length_drop]
    have hylt := List.idxOf_lt_length_of_mem hy
    omega
  · rw [List.getElem_drop]
    have heq : p.support.idxOf x + (p.support.idxOf y - p.support.idxOf x) =
        p.support.idxOf y := Nat.add_sub_of_le h
    simpa [heq] using List.getElem_idxOf (List.idxOf_lt_length_of_mem hy)

theorem isTwoConnectedOn_coneAt_cycle
    {G : SimpleGraph V} {s : Finset V}
    (hnlow : ¬HasLowSeparationOn G s)
    (hntwo : ¬Nonempty (TwoSeparationOn G s))
    {x b c : V} (hxs : x ∈ s)
    {C : G.Walk b b} (hC : C.IsCycle) (hxC : x ∉ C.support)
    (hbcC : s(b, c) ∈ C.edges) (hCs : ∀ z ∈ C.support, z ∈ s) :
    IsTwoConnectedOn (coneAt G x C.support.toFinset) s := by
  classical
  let K := coneAt G x C.support.toFinset
  have hbc : b ≠ c := (C.adj_of_mem_edges hbcC).ne
  have hbC : b ∈ C.support := C.fst_mem_support_of_mem_edges hbcC
  have hcC : c ∈ C.support := C.snd_mem_support_of_mem_edges hbcC
  have pathAvoiding {r u v : V} (hus : u ∈ s) (hvs : v ∈ s)
      (hux : u ≠ x) (hvx : v ≠ x) (hur : u ≠ r) (hvr : v ≠ r) :
      ∃ p : K.Walk u v, p.IsPath ∧ (∀ z ∈ p.support, z ∈ s) ∧
        r ∉ p.support ∧ x ∉ p.support := by
    have hcard : ({x, r} : Finset V).card ≤ 2 := by
      calc
        ({x, r} : Finset V).card ≤ ({r} : Finset V).card + 1 :=
          Finset.card_insert_le _ _
        _ ≤ 2 := by simp
    have huf : u ∉ ({x, r} : Finset V) := by simp [hux, hur]
    have hvf : v ∉ ({x, r} : Finset V) := by simp [hvx, hvr]
    obtain ⟨q, hq⟩ := reachableOnAvoiding_of_no_small_separation
      hnlow hntwo hcard hus huf hvs hvf
    let pG : G.Walk u v := q.toPath
    have hpG : pG.IsPath := Walk.bypass_isPath q
    have hpGs : ∀ z ∈ pG.support, z ∈ s := by
      intro z hz
      exact (hq z (q.support_bypass_subset_support hz)).1
    have hpGf : ∀ z ∈ pG.support, z ∉ ({x, r} : Finset V) := by
      intro z hz
      exact (hq z (q.support_bypass_subset_support hz)).2
    have hpGedges : ∀ e, e ∈ pG.edges → e ∈ K.edgeSet := by
      rintro ⟨a, d⟩ he
      have hadj : G.Adj a d := by
        simpa only [mem_edgeSet] using pG.edges_subset_edgeSet he
      apply coneAt_adj_of_original hadj
      · intro hax
        apply hpGf a (pG.fst_mem_support_of_mem_edges he)
        simp [hax]
      · intro hdx
        apply hpGf d (pG.snd_mem_support_of_mem_edges he)
        simp [hdx]
    let p : K.Walk u v := pG.transfer K hpGedges
    refine ⟨p, ?_, ?_, ?_, ?_⟩
    · exact hpG.transfer hpGedges
    · intro z hz
      apply hpGs z
      simpa [p] using hz
    · intro hr
      apply hpGf r (by simpa [p] using hr)
      simp
    · intro hx
      apply hpGf x (by simpa [p] using hx)
      simp
  have fromCenter {r v : V} (hvs : v ∈ s) (hxr : x ≠ r)
      (hvx : v ≠ x) (hvr : v ≠ r) :
      ∃ p : K.Walk x v, p.IsPath ∧ (∀ z ∈ p.support, z ∈ s) ∧
        r ∉ p.support := by
    let z : V := if r = b then c else b
    have hzC : z ∈ C.support := by
      simp only [z]
      split <;> assumption
    have hzr : z ≠ r := by
      simp only [z]
      split
      · rename_i hrb
        subst r
        exact hbc.symm
      · rename_i hrb
        exact fun h ↦ hrb h.symm
    have hzx : z ≠ x := by
      intro h
      exact hxC (h.symm ▸ hzC)
    have hzs : z ∈ s := hCs z hzC
    obtain ⟨q, hq, hqs, hrq, hxq⟩ :=
      pathAvoiding hzs hvs hzx hvx hzr hvr
    have hxz : K.Adj x z := by
      apply coneAt_adj_center
      · simpa using hzC
      · exact hzx
    let p : K.Walk x v := Walk.cons hxz q
    refine ⟨p, ?_, ?_, ?_⟩
    · exact hq.cons hxq
    · intro y hy
      have : y = x ∨ y ∈ q.support := by simpa [p] using hy
      rcases this with rfl | hyq
      · exact hxs
      · exact hqs y hyq
    · intro hrp
      have : r = x ∨ r ∈ q.support := by simpa [p] using hrp
      rcases this with hrx | hrq'
      · exact hxr hrx.symm
      · exact hrq hrq'
  intro r u v hus hvs hur hvr
  by_cases huv : u = v
  · subst v
    exact ⟨Walk.nil, by simp, by simp [hus], by simpa using Ne.symm hur⟩
  by_cases hux : u = x
  · subst u
    exact fromCenter hvs hur (Ne.symm huv) hvr
  by_cases hvx : v = x
  · subst v
    obtain ⟨p, hp, hps, hrp⟩ := fromCenter hus hvr hux hur
    exact ⟨p.reverse, hp.reverse, by simpa using hps, by simpa using hrp⟩
  obtain ⟨p, hp, hps, hrp, _⟩ :=
    pathAvoiding hus hvs hux hvx hur hvr
  exact ⟨p, hp, hps, hrp⟩

theorem exists_ear_through_vertex_of_core
    {G : SimpleGraph V} {s : Finset V}
    (hnlow : ¬HasLowSeparationOn G s)
    (hntwo : ¬Nonempty (TwoSeparationOn G s))
    {x d b c : V} (hxs : x ∈ s) (hds : d ∈ s) (hdx : d ≠ x)
    {C : G.Walk b b} (hC : C.IsCycle) (hxC : x ∉ C.support)
    (hdC : d ∉ C.support) (hbcC : s(b, c) ∈ C.edges)
    (hCs : ∀ z ∈ C.support, z ∈ s) :
    ∃ z₁ z₂, ∃ q : G.Walk z₁ z₂,
      z₁ ∈ C.support ∧ z₂ ∈ C.support ∧ z₁ ≠ z₂ ∧ q.IsPath ∧
      x ∉ q.support ∧ d ∈ q.support ∧
      (∀ y ∈ q.support, y ∈ s) ∧
      (∀ y ∈ q.support, y ∈ C.support → y = z₁ ∨ y = z₂) := by
  classical
  let K := coneAt G x C.support.toFinset
  have hbc : b ≠ c := (C.adj_of_mem_edges hbcC).ne
  have hbC : b ∈ C.support := C.fst_mem_support_of_mem_edges hbcC
  have hcC : c ∈ C.support := C.snd_mem_support_of_mem_edges hbcC
  have hbx : b ≠ x := fun h ↦ hxC (h ▸ hbC)
  have hcx : c ≠ x := fun h ↦ hxC (h ▸ hcC)
  have hxbK : K.Adj x b := by
    apply coneAt_adj_center
    · simpa using hbC
    · exact hbx
  have hbcK : K.Adj b c := coneAt_adj_of_original
    (C.adj_of_mem_edges hbcC) hbx hcx
  have hcxK : K.Adj c x := (coneAt_adj_center (by simpa using hcC) hcx).symm
  let T : K.Walk x x :=
    Walk.cons hxbK (Walk.cons hbcK (Walk.cons hcxK Walk.nil))
  have hT : T.IsCycle := by
    simp [T, Walk.cons_isCycle_iff, Walk.isPath_def, hbc, hbx, hcx,
      Ne.symm hbc, Ne.symm hbx, Ne.symm hcx]
  have hxbT : s(x, b) ∈ T.edges := by simp [T]
  have hTs : ∀ y ∈ T.support, y ∈ s := by
    intro y hy
    have : y = x ∨ y = b ∨ y = c ∨ y = x := by simpa [T] using hy
    rcases this with h | h | h | h
    · exact h ▸ hxs
    · exact h ▸ hCs b hbC
    · exact h ▸ hCs c hcC
    · exact h ▸ hxs
  have hconnK : IsTwoConnectedOn K s :=
    isTwoConnectedOn_coneAt_cycle hnlow hntwo hxs hC hxC hbcC hCs
  obtain ⟨w, D, hD, hxbD, hdD, hDs⟩ :=
    hconnK.exists_cycle_containing_edge_and_vertex hxs hds hT hxbT hTs
  obtain ⟨r, hr, hrsnd, hrSupport, _⟩ := orient_cycle_at_edge D hD hxbD
  have htailnon : ¬r.tail.Nil := by
    rw [Walk.not_nil_iff_lt_length]
    have hlen := r.length_tail_add_one hr.not_nil
    have hthree := hr.three_le_length
    omega
  let qK : K.Walk b r.tail.penultimate :=
    (r.tail.dropLast).copy hrsnd rfl
  have hqK : qK.IsPath := by
    have := hr.isPath_tail.take (r.tail.length - 1)
    simpa [qK, Walk.dropLast] using this
  have hxqK : x ∉ qK.support := by
    have hn := hr.isPath_tail.support_nodup
    have hsupp := r.tail.support_dropLast_concat htailnon
    rw [← hsupp] at hn
    have hxdrop : x ∉ r.tail.dropLast.support := by
      intro hx
      exact hn.disjoint hx (by simp)
    simpa [qK] using hxdrop
  have hdr : d ∈ r.support := (hrSupport d).mpr hdD
  have hdtail : d ∈ r.tail.support := by
    have : d = x ∨ d ∈ r.tail.support := by
      have hmem : d ∈ x :: r.tail.support := by
        rw [r.cons_support_tail hr.not_nil]
        exact hdr
      simpa using hmem
    exact this.resolve_left hdx
  have hdqK : d ∈ qK.support := by
    have hsupp := r.tail.support_dropLast_concat htailnon
    rw [← hsupp, List.mem_append] at hdtail
    have hdrop : d ∈ r.tail.dropLast.support := by
      rcases hdtail with h | h
      · exact h
      · simp at h
        exact (hdx h).elim
    simpa [qK] using hdrop
  let z : V := r.tail.penultimate
  have hzxK : K.Adj z x := by
    exact r.tail.adj_penultimate htailnon
  have hzC : z ∈ C.support := by
    have : z ∈ C.support.toFinset := coneAt_mem_of_adj_center hzxK.symm
    simpa using this
  have hqKedges : ∀ e, e ∈ qK.edges → e ∈ G.edgeSet := by
    rintro ⟨u, v⟩ he
    have huvK : K.Adj u v := by
      simpa only [mem_edgeSet] using qK.edges_subset_edgeSet he
    have hux : u ≠ x := by
      intro h
      exact hxqK (h ▸ qK.fst_mem_support_of_mem_edges he)
    have hvx : v ≠ x := by
      intro h
      exact hxqK (h ▸ qK.snd_mem_support_of_mem_edges he)
    rcases huvK.2 with huv | huv | huv
    · simpa only [mem_edgeSet] using huv.2.2
    · exact (hux huv.1).elim
    · exact (hvx huv.1).elim
  let qG : G.Walk b z := qK.transfer G hqKedges
  have hqG : qG.IsPath := hqK.transfer hqKedges
  have hxqG : x ∉ qG.support := by simpa [qG] using hxqK
  have hdqG : d ∈ qG.support := by simpa [qG] using hdqK
  obtain ⟨z₁, z₂, q, hz₁C, hz₂C, hz₁z₂, hq, hdq, hqp, hqC⟩ :=
    Walk.IsPath.extract_between_finset_through (t := C.support.toFinset) hqG
      (by simpa using hbC)
      (by simpa using hzC) (by simpa using hdC) hdqG
  refine ⟨z₁, z₂, q, by simpa using hz₁C, by simpa using hz₂C,
    hz₁z₂, hq, ?_, hdq, ?_, ?_⟩
  · intro hxq
    exact hxqG (hqp x hxq)
  · intro y hy
    have hyqG := hqp y hy
    have hyqK : y ∈ qK.support := by simpa [qG] using hyqG
    have hyr : y ∈ r.support := by
      rw [← r.cons_support_tail hr.not_nil]
      right
      have hydrop : y ∈ r.tail.dropLast.support := by simpa [qK] using hyqK
      have hyl : y ∈ r.tail.support.dropLast := by
        rw [← Walk.support_dropLast htailnon]
        exact hydrop
      exact List.mem_of_mem_dropLast hyl
    exact hDs y ((hrSupport y).mp hyr)
  · intro y hy hyC
    have hyfin : y ∈ C.support.toFinset := by simpa using hyC
    exact hqC y hy hyfin

theorem exists_cycle_containing_edge_and_vertex_avoiding
    {G : SimpleGraph V} {s : Finset V} {a b c d : V}
    (hnlow : ¬HasLowSeparationOn G s)
    (hntwo : ¬Nonempty (TwoSeparationOn G s))
    (hbs : b ∈ s) (hds : d ∈ s) (hda : d ≠ a)
    {C : G.Walk b b} (hC : C.IsCycle) (haC : a ∉ C.support)
    (hbcC : s(b, c) ∈ C.edges) (hCs : ∀ z ∈ C.support, z ∈ s) :
    ∃ (w : V) (D : G.Walk w w), D.IsCycle ∧ a ∉ D.support ∧
      s(b, c) ∈ D.edges ∧ d ∈ D.support ∧
      (∀ z ∈ D.support, z ∈ s) := by
  classical
  let Good : V → Prop := fun x ↦
    ∃ (w : V) (D : G.Walk w w), D.IsCycle ∧ a ∉ D.support ∧
      s(b, c) ∈ D.edges ∧ x ∈ D.support ∧
      (∀ z ∈ D.support, z ∈ s)
  let U : Finset V := s.filter Good
  have hbGood : Good b := by
    exact ⟨b, C, hC, haC, hbcC, Walk.start_mem_support C, hCs⟩
  have hbU : b ∈ U := Finset.mem_filter.mpr ⟨hbs, hbGood⟩
  by_cases hdU : d ∈ U
  · exact (Finset.mem_filter.mp hdU).2
  · have hfa : ({a} : Finset V).card ≤ 2 := by simp
    have hbf : b ∉ ({a} : Finset V) := by
      intro h
      have hba : b = a := by simpa using h
      exact haC (hba.symm ▸ Walk.start_mem_support C)
    have hdf : d ∉ ({a} : Finset V) := by simpa [hda]
    obtain ⟨p, hp⟩ := reachableOnAvoiding_of_no_small_separation
      hnlow hntwo hfa hbs hbf hds hdf
    obtain ⟨u, v, hup, hvp, huv, huU, hvU⟩ :=
      Walk.exists_adj_crossing_finset p hbU hdU
    have hus : u ∈ s := (hp u hup).1
    have hvs : v ∈ s := (hp v hvp).1
    have hua : u ≠ a := by
      intro h
      exact (hp u hup).2 (by simp [h])
    have hva : v ≠ a := by
      intro h
      exact (hp v hvp).2 (by simp [h])
    obtain ⟨wu, Cu, hCu, haCu, hbcCu, huCu, hCus⟩ :=
      (Finset.mem_filter.mp huU).2
    have hext : ∀ {t}, t ∈ Cu.support → t ≠ u →
        ReachableOnAvoiding G s {a, u} v t := by
      intro t htCu htu
      have hts : t ∈ s := hCus t htCu
      have hta : t ≠ a := by
        intro h
        exact haCu (h ▸ htCu)
      have hvf : v ∉ ({a, u} : Finset V) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hva, huv.ne.symm⟩
      have htf : t ∉ ({a, u} : Finset V) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hta, htu⟩
      apply reachableOnAvoiding_of_no_small_separation hnlow hntwo
        (by
          calc
            ({a, u} : Finset V).card ≤ ({u} : Finset V).card + 1 :=
              Finset.card_insert_le _ _
            _ ≤ 2 := by simp) hvs hvf hts htf
    obtain ⟨wv, Cv, hCv, haCv, hbcCv, hvCv, hCvs⟩ :=
      extend_cycle_preserving_edge hCu haCu hbcCu huCu
        (fun h ↦ hvU (Finset.mem_filter.mpr ⟨hvs,
          ⟨wu, Cu, hCu, haCu, hbcCu, h, hCus⟩⟩)) huv hCus hext
    exfalso
    apply hvU
    exact Finset.mem_filter.mpr ⟨hvs, wv, Cv, hCv, haCv, hbcCv, hvCv, hCvs⟩

theorem hasThreeSpokeCycle_of_triangle
    {G : SimpleGraph V} {s : Finset V}
    (hs4 : 4 ≤ s.card)
    (hnlow : ¬HasLowSeparationOn G s)
    (hntwo : ¬Nonempty (TwoSeparationOn G s))
    {a b c : V} (has : a ∈ s) (hbs : b ∈ s) (hcs : c ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (habAdj : G.Adj a b) (hacAdj : G.Adj a c) (hbcAdj : G.Adj b c) :
    HasThreeSpokeCycleTest G := by
  classical
  let n := neighborFinsetOn G s b
  have hn3 : 3 ≤ n.card :=
    three_le_card_neighborFinsetOn_of_no_small_separation hs4 hnlow hntwo hbs
  have hnsub : ¬n ⊆ {a, c} := by
    intro hsub
    have hcard := Finset.card_le_card hsub
    have hpair : ({a, c} : Finset V).card = 2 := Finset.card_pair hac
    omega
  obtain ⟨e, hen, henot⟩ := Finset.not_subset.mp hnsub
  have hes : e ∈ s := (Finset.mem_filter.mp hen).1
  have hbe : G.Adj b e := (Finset.mem_filter.mp hen).2
  have hea : e ≠ a := by
    intro h
    exact henot (by simp [h])
  have hec : e ≠ c := by
    intro h
    exact henot (by simp [h])
  have heb : e ≠ b := hbe.ne.symm
  have hef : e ∉ ({a, b} : Finset V) := by simp [hea, heb]
  have hcf : c ∉ ({a, b} : Finset V) := by simp [hac.symm, hbc.symm]
  have hpairle : ({a, b} : Finset V).card ≤ 2 := by
    calc
      ({a, b} : Finset V).card ≤ ({b} : Finset V).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ 2 := by simp
  obtain ⟨p, hp⟩ := reachableOnAvoiding_of_no_small_separation
    hnlow hntwo hpairle hes hef hcs hcf
  let p' : G.Walk e c := p.toPath
  have hp' : p'.IsPath := Walk.bypass_isPath p
  have hbp' : b ∉ p'.support := by
    intro h
    exact (hp b (p.support_bypass_subset_support h)).2 (by simp)
  obtain ⟨C, hC, hbcC, hCs'⟩ :=
    exists_cycle_of_edge_and_avoiding_path hbcAdj hbe hec p' hp' hbp'
  have haC : a ∉ C.support := by
    intro h
    rcases hCs' a h with rfl | hap
    · exact hab rfl
    · exact (hp a (p.support_bypass_subset_support hap)).2 (by simp)
  have hCs : ∀ z ∈ C.support, z ∈ s := by
    intro z hz
    rcases hCs' z hz with rfl | hzp
    · exact hbs
    · exact (hp z (p.support_bypass_subset_support hzp)).1
  apply hasThreeSpokeCycle_of_triangle_of_edge_vertex_cycle hs4 hnlow hntwo
    has hbs hcs hab hac hbc habAdj hacAdj hbcAdj
  intro d hds hda hdb hdc had
  obtain ⟨v, D, hD, haD, hbcD, hdD, hDs⟩ :=
    exists_cycle_containing_edge_and_vertex_avoiding hnlow hntwo
      hbs hds hda hC haC hbcC hCs
  have hbD : b ∈ D.support := D.fst_mem_support_of_mem_edges hbcD
  have hcD : c ∈ D.support := D.snd_mem_support_of_mem_edges hbcD
  exact ⟨v, D, hD, haD, hDs, hbD, hcD, hdD⟩

omit [Fintype V] in
theorem SeparationOn.walk_support_left_of_only_end_in_inter
    {G : SimpleGraph V} {s left right : Finset V} (hsep : SeparationOn G s left right)
    {x y : V} (p : G.Walk x y) (hp : p.IsPath) (hx : x ∈ left \ right)
    (hps : ∀ z ∈ p.support, z ∈ s)
    (hinter : ∀ z ∈ p.support, z ∈ left ∩ right → z = y) :
    ∀ z ∈ p.support, z ∈ left := by
  induction p with
  | nil => simpa using (Finset.mem_sdiff.mp hx).1
  | @cons u v w huv p ih =>
      have huLeft : u ∈ left := (Finset.mem_sdiff.mp hx).1
      have huNotRight : u ∉ right := (Finset.mem_sdiff.mp hx).2
      have hpParts : p.IsPath ∧ u ∉ p.support := by simpa using hp
      have hpPath : p.IsPath := hpParts.1
      have hvLeft : v ∈ left := by
        have huS : u ∈ s := hps u (by simp)
        have hvS : v ∈ s := hps v (by simp)
        rcases hsep.no_cross (hsep.union_eq.symm ▸ huS)
            (hsep.union_eq.symm ▸ hvS) huv with hL | hR
        · exact hL.2
        · exact (huNotRight hR.1).elim
      by_cases hvw : v = w
      · subst w
        have hpNil : p.Nil := Walk.isPath_iff_nil.mp hpPath
        obtain rfl := hpNil.eq_nil
        intro z hz
        have hz' : z = u ∨ z = v := by simpa using hz
        exact hz'.elim (fun h ↦ h ▸ huLeft) (fun h ↦ h ▸ hvLeft)
      · have hvNotRight : v ∉ right := by
          intro hvRight
          exact hvw (hinter v (by simp)
            (Finset.mem_inter.mpr ⟨hvLeft, hvRight⟩))
        have htail := ih hpPath (Finset.mem_sdiff.mpr ⟨hvLeft, hvNotRight⟩)
          (fun z hz ↦ hps z (List.mem_of_mem_tail hz))
          (fun z hz hi ↦ hinter z (List.mem_of_mem_tail hz) hi)
        intro z hz
        have hz' : z = u ∨ z ∈ p.support := by simpa using hz
        exact hz'.elim (fun h ↦ h ▸ huLeft) (htail z)

theorem SeparationOn.exists_external_walk_of_inter_triple
    {G : SimpleGraph V} {s left right : Finset V}
    (hsep : SeparationOn G s left right)
    {a b c r : V} (hi : left ∩ right = {a, b, c})
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hnlow : ¬HasLowSeparationOn G s)
    (hntwo : ¬Nonempty (TwoSeparationOn G s))
    (hr : r ∈ left \ right) :
    ∃ p : G.Walk a c,
      (∀ z ∈ p.support, z ∈ left) ∧
      (∀ z ∈ p.support, z ∈ right → z = a ∨ z = c) := by
  classical
  have haInter : a ∈ left ∩ right := by rw [hi]; simp
  have hbInter : b ∈ left ∩ right := by rw [hi]; simp
  have hcInter : c ∈ left ∩ right := by rw [hi]; simp
  have has : a ∈ s := hsep.union_eq ▸ Finset.mem_union.mpr (.inl (Finset.mem_inter.mp haInter).1)
  have hcs : c ∈ s := hsep.union_eq ▸ Finset.mem_union.mpr (.inl (Finset.mem_inter.mp hcInter).1)
  have hrs : r ∈ s := hsep.union_eq ▸
    Finset.mem_union.mpr (.inl (Finset.mem_sdiff.mp hr).1)
  have haf : a ∉ ({b, c} : Finset V) := by simp [hab, hac]
  have hrfBC : r ∉ ({b, c} : Finset V) := by
    intro h
    have hrLeft := (Finset.mem_sdiff.mp hr).1
    have hrRight : r ∈ right := by
      rcases Finset.mem_insert.mp h with hrb | hrc
      · exact hrb.symm ▸ (Finset.mem_inter.mp hbInter).2
      · exact (Finset.mem_singleton.mp hrc).symm ▸ (Finset.mem_inter.mp hcInter).2
    exact (Finset.mem_sdiff.mp hr).2 hrRight
  have hcf : c ∉ ({a, b} : Finset V) := by simp [hac.symm, hbc.symm]
  have hrfAB : r ∉ ({a, b} : Finset V) := by
    intro h
    have hrRight : r ∈ right := by
      rcases Finset.mem_insert.mp h with hra | hrb
      · exact hra.symm ▸ (Finset.mem_inter.mp haInter).2
      · exact (Finset.mem_singleton.mp hrb).symm ▸ (Finset.mem_inter.mp hbInter).2
    exact (Finset.mem_sdiff.mp hr).2 hrRight
  have hpairBC : ({b, c} : Finset V).card ≤ 2 := by
    calc
      _ ≤ ({c} : Finset V).card + 1 := Finset.card_insert_le _ _
      _ ≤ 2 := by simp
  have hpairAB : ({a, b} : Finset V).card ≤ 2 := by
    calc
      _ ≤ ({b} : Finset V).card + 1 := Finset.card_insert_le _ _
      _ ≤ 2 := by simp
  obtain ⟨pa, hpa⟩ := reachableOnAvoiding_of_no_small_separation
    hnlow hntwo hpairBC has haf hrs hrfBC
  obtain ⟨pc, hpc⟩ := reachableOnAvoiding_of_no_small_separation
    hnlow hntwo hpairAB hcs hcf hrs hrfAB
  let qa : G.Walk a r := pa.toPath
  let qc : G.Walk c r := pc.toPath
  have hqa : qa.IsPath := Walk.bypass_isPath pa
  have hqc : qc.IsPath := Walk.bypass_isPath pc
  have hqaS : ∀ z ∈ qa.support, z ∈ s := by
    intro z hz
    exact (hpa z (pa.support_bypass_subset_support hz)).1
  have hqcS : ∀ z ∈ qc.support, z ∈ s := by
    intro z hz
    exact (hpc z (pc.support_bypass_subset_support hz)).1
  have hqaInter : ∀ z ∈ qa.reverse.support, z ∈ left ∩ right → z = a := by
    intro z hz hzInter
    have hzqa : z ∈ qa.support := by simpa using hz
    have hzabc : z ∈ ({a, b, c} : Finset V) := hi ▸ hzInter
    have hzCases : z = a ∨ z = b ∨ z = c := by simpa using hzabc
    rcases hzCases with hza | hzb | hzc
    · exact hza
    · exact ((hpa z (pa.support_bypass_subset_support hzqa)).2 (by simp [hzb])).elim
    · exact ((hpa z (pa.support_bypass_subset_support hzqa)).2 (by simp [hzc])).elim
  have hqcInter : ∀ z ∈ qc.reverse.support, z ∈ left ∩ right → z = c := by
    intro z hz hzInter
    have hzqc : z ∈ qc.support := by simpa using hz
    have hzabc : z ∈ ({a, b, c} : Finset V) := hi ▸ hzInter
    have hzCases : z = a ∨ z = b ∨ z = c := by simpa using hzabc
    rcases hzCases with hza | hzb | hzc
    · exact ((hpc z (pc.support_bypass_subset_support hzqc)).2 (by simp [hza])).elim
    · exact ((hpc z (pc.support_bypass_subset_support hzqc)).2 (by simp [hzb])).elim
    · exact hzc
  have hqaLeft : ∀ z ∈ qa.support, z ∈ left := by
    intro z hz
    apply hsep.walk_support_left_of_only_end_in_inter qa.reverse hqa.reverse hr
      (by simpa using hqaS) hqaInter z
    simpa using hz
  have hqcLeft : ∀ z ∈ qc.support, z ∈ left := by
    intro z hz
    apply hsep.walk_support_left_of_only_end_in_inter qc.reverse hqc.reverse hr
      (by simpa using hqcS) hqcInter z
    simpa using hz
  let p : G.Walk a c := qa.append qc.reverse
  refine ⟨p, ?_, ?_⟩
  · intro z hz
    rw [Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · exact hqaLeft z hz
    · exact hqcLeft z (by simpa using hz)
  · intro z hz hzRight
    rw [Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · have hzInter : z ∈ left ∩ right :=
        Finset.mem_inter.mpr ⟨hqaLeft z hz, hzRight⟩
      have hzabc : z ∈ ({a, b, c} : Finset V) := hi ▸ hzInter
      have hzCases : z = a ∨ z = b ∨ z = c := by simpa using hzabc
      rcases hzCases with hza | hzb | hzc
      · exact Or.inl hza
      · exact ((hpa z (pa.support_bypass_subset_support hz)).2 (by simp [hzb])).elim
      · exact ((hpa z (pa.support_bypass_subset_support hz)).2 (by simp [hzc])).elim
    · have hzqc : z ∈ qc.support := by simpa using hz
      have hzInter : z ∈ left ∩ right :=
        Finset.mem_inter.mpr ⟨hqcLeft z hzqc, hzRight⟩
      have hzabc : z ∈ ({a, b, c} : Finset V) := hi ▸ hzInter
      have hzCases : z = a ∨ z = b ∨ z = c := by simpa using hzabc
      rcases hzCases with hza | hzb | hzc
      · exact ((hpc z (pc.support_bypass_subset_support hzqc)).2 (by simp [hza])).elim
      · exact ((hpc z (pc.support_bypass_subset_support hzqc)).2 (by simp [hzb])).elim
      · exact Or.inr hzc

omit [Fintype V] in
theorem edgeSetOn_triple_of_two_edges
    (G : SimpleGraph V) {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (habAdj : G.Adj a b) (hbcAdj : G.Adj b c) (hacNot : ¬G.Adj a c) :
    edgeSetOn G {a, b, c} = {s(a, b), s(b, c)} := by
  ext ⟨u, v⟩
  simp only [edgeSetOn, Set.mem_inter_iff, mem_edgeSet, Set.mk_mem_sym2_iff,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨huv, hu, hv⟩
    have hu' : u = a ∨ u = b ∨ u = c := by simpa using hu
    have hv' : v = a ∨ v = b ∨ v = c := by simpa using hv
    rcases hu' with rfl | rfl | rfl <;> rcases hv' with rfl | rfl | rfl
    · exact (G.loopless.irrefl _ huv).elim
    · exact Or.inl rfl
    · exact (hacNot huv).elim
    · exact Or.inl Sym2.eq_swap
    · exact (G.loopless.irrefl _ huv).elim
    · exact Or.inr rfl
    · exact (hacNot huv.symm).elim
    · exact Or.inr Sym2.eq_swap
    · exact (G.loopless.irrefl _ huv).elim
  · intro h
    rcases h with h | h
    · rw [Sym2.eq_iff] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨habAdj, by simp, by simp⟩
      · exact ⟨habAdj.symm, by simp, by simp⟩
    · rw [Sym2.eq_iff] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hbcAdj, by simp, by simp⟩
      · exact ⟨hbcAdj.symm, by simp, by simp⟩

theorem reachableOnAvoiding_triple_of_path_of_core_exact
    {G : SimpleGraph V} {s : Finset V}
    (hs3 : 3 ≤ s.card)
    (hnlow : ¬HasLowSeparationOn G s)
    (hntwo : ¬Nonempty (TwoSeparationOn G s))
    (hfree : ¬HasThreeSpokeCycleTest G)
    (hE : (edgeSetOn G s).ncard = 2 * s.card - 3)
    (hsmaller : ∀ (H : SimpleGraph V) (t : Finset V), t.card < s.card →
      3 ≤ t.card → ¬HasThreeSpokeCycleTest H →
      (edgeSetOn H t).ncard = 2 * t.card - 3 → IsCockadeOn H t)
    {a b c u v : V}
    (has : a ∈ s) (hbs : b ∈ s) (hcs : c ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (habAdj : G.Adj a b) (hbcAdj : G.Adj b c) (hacNot : ¬G.Adj a c)
    (hus : u ∈ s) (huf : u ∉ ({a, b, c} : Finset V))
    (hvs : v ∈ s) (hvf : v ∉ ({a, b, c} : Finset V)) :
    ReachableOnAvoiding G s {a, b, c} u v := by
  classical
  have bound (t : Finset V) (htlt : t.card < s.card) :
      (edgeSetOn G t).ncard ≤ 2 * t.card - 3 := by
    by_cases ht3 : 3 ≤ t.card
    · by_contra hle
      have hk : 2 * t.card - 3 ≤ (edgeSetOn G t).ncard := by omega
      obtain ⟨H, hHG, hHcard⟩ := exists_le_edgeSetOn_ncard_eq G t hk
      have hHfree : ¬HasThreeSpokeCycleTest H := by
        intro hH
        exact hfree (hH.mono hHG)
      have hc : IsCockadeOn H t := hsmaller H t htlt ht3 hHfree hHcard
      apply hfree
      apply hc.hasThreeSpokeCycle_of_more_edges hHG
      omega
    · have ht2 : t.card ≤ 2 := by omega
      have hchoose := ncard_edgeSetOn_le_choose G t
      interval_cases htc : t.card <;> simp_all
  by_contra huv
  obtain ⟨left, right, hsep, hinter, _⟩ :=
    separationOn_of_not_reachableOnAvoiding G s {a, b, c}
      hus huf hvs hvf huv
  have hsTriple : s ∩ ({a, b, c} : Finset V) = {a, b, c} := by
    have hsub : ({a, b, c} : Finset V) ⊆ s := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> assumption
    exact Finset.inter_eq_right.mpr hsub
  have hi : left ∩ right = {a, b, c} := hinter.trans hsTriple
  have hiCard : (left ∩ right).card = 3 := by simp [hi, hab, hac, hbc]
  have haLeft : a ∈ left := by
    have : a ∈ left ∩ right := by rw [hi]; simp
    exact (Finset.mem_inter.mp this).1
  have hcLeft : c ∈ left := by
    have : c ∈ left ∩ right := by rw [hi]; simp
    exact (Finset.mem_inter.mp this).1
  have haRight : a ∈ right := by
    have : a ∈ left ∩ right := by rw [hi]; simp
    exact (Finset.mem_inter.mp this).2
  have hcRight : c ∈ right := by
    have : c ∈ left ∩ right := by rw [hi]; simp
    exact (Finset.mem_inter.mp this).2
  have hleft3 : 3 ≤ left.card := by
    have hcard : (left ∩ right).card ≤ left.card :=
      Finset.card_le_card Finset.inter_subset_left
    omega
  have hright3 : 3 ≤ right.card := by
    have hcard : (left ∩ right).card ≤ right.card :=
      Finset.card_le_card Finset.inter_subset_right
    omega
  have hleftlt : left.card < s.card := Finset.card_lt_card hsep.left_ssubset
  have hrightlt : right.card < s.card := Finset.card_lt_card hsep.right_ssubset
  have hleftBound := bound left hleftlt
  have hrightBound := bound right hrightlt
  have hedgeInter : edgeSetOn G left ∩ edgeSetOn G right =
      {s(a, b), s(b, c)} := by
    rw [edgeSetOn_inter, hi]
    exact edgeSetOn_triple_of_two_edges G hab hac hbc habAdj hbcAdj hacNot
  have hedge := hsep.edge_count_identity
  rw [hedgeInter] at hedge
  have hpairs : s(a, b) ≠ s(b, c) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨hab', hbc'⟩ | ⟨hac', hbb'⟩
    · exact hac (hab'.trans hbc')
    · exact hac hac'
  have hedgeCard : ({s(a, b), s(b, c)} : Set (Sym2 V)).ncard = 2 := by
    simp [hpairs]
  rw [hedgeCard] at hedge
  have hverts := Finset.card_union_add_card_inter left right
  rw [hsep.union_eq, hiCard] at hverts
  have hleftStrict : (edgeSetOn G left).ncard < 2 * left.card - 3 := by
    by_contra hnot
    have heq : (edgeSetOn G left).ncard = 2 * left.card - 3 := by omega
    have hcL : IsCockadeOn G left :=
      hsmaller G left hleftlt hleft3 hfree heq
    obtain ⟨r, hr⟩ := hsep.right_nonempty
    have hi' : right ∩ left = {a, b, c} := by simpa [Finset.inter_comm] using hi
    obtain ⟨p, hpRight, hpExt⟩ :=
      hsep.symm.exists_external_walk_of_inter_triple hi' hab hac hbc
        hnlow hntwo hr
    apply hfree
    exact hcL.hasThreeSpokeCycle_of_external (fun _ _ h ↦ h) haLeft hcLeft
      hac hacNot p hpExt
  have hrightStrict : (edgeSetOn G right).ncard < 2 * right.card - 3 := by
    by_contra hnot
    have heq : (edgeSetOn G right).ncard = 2 * right.card - 3 := by omega
    have hcR : IsCockadeOn G right :=
      hsmaller G right hrightlt hright3 hfree heq
    obtain ⟨r, hr⟩ := hsep.left_nonempty
    obtain ⟨p, hpLeft, hpExt⟩ :=
      hsep.exists_external_walk_of_inter_triple hi hab hac hbc
        hnlow hntwo hr
    apply hfree
    exact hcR.hasThreeSpokeCycle_of_external (fun _ _ h ↦ h) haRight hcRight
      hac hacNot p hpExt
  omega

theorem exact_classification_of_core
    (hcore : ∀ (G : SimpleGraph V) (s : Finset V),
      3 ≤ s.card →
      ¬HasLowSeparationOn G s →
      ¬Nonempty (TwoSeparationOn G s) →
      ¬HasThreeSpokeCycleTest G →
      (edgeSetOn G s).ncard = 2 * s.card - 3 →
      (∀ (H : SimpleGraph V) (t : Finset V), t.card < s.card →
        3 ≤ t.card → ¬HasThreeSpokeCycleTest H →
        (edgeSetOn H t).ncard = 2 * t.card - 3 → IsCockadeOn H t) →
      IsCockadeOn G s) :
    ∀ (G : SimpleGraph V) (s : Finset V),
      3 ≤ s.card →
      ¬HasThreeSpokeCycleTest G →
      (edgeSetOn G s).ncard = 2 * s.card - 3 →
      IsCockadeOn G s := by
  intro G s hs3 hfree hexact
  induction hn : s.card using Nat.strong_induction_on generalizing G s with
  | h n ih =>
      have bound (t : Finset V) (htn : t.card < n) :
          (edgeSetOn G t).ncard ≤ 2 * t.card - 3 := by
        by_cases ht3 : 3 ≤ t.card
        · by_contra hle
          have hk : 2 * t.card - 3 ≤ (edgeSetOn G t).ncard := by omega
          obtain ⟨H, hHG, hHcard⟩ := exists_le_edgeSetOn_ncard_eq G t hk
          have hHfree : ¬HasThreeSpokeCycleTest H := by
            intro hH
            exact hfree (hH.mono hHG)
          have hc : IsCockadeOn H t :=
            ih t.card htn H t ht3 hHfree hHcard rfl
          apply hfree
          apply hc.hasThreeSpokeCycle_of_more_edges hHG
          omega
        · have ht2 : t.card ≤ 2 := by omega
          have hchoose := ncard_edgeSetOn_le_choose G t
          interval_cases htc : t.card <;> simp_all
      by_cases hlow : HasLowSeparationOn G s
      · obtain ⟨a, b, hsep, hi⟩ := hlow
        have ha_lt : a.card < n := by
          rw [← hn]
          exact Finset.card_lt_card hsep.left_ssubset
        have hb_lt : b.card < n := by
          rw [← hn]
          exact Finset.card_lt_card hsep.right_ssubset
        have ha_bound := bound a ha_lt
        have hb_bound := bound b hb_lt
        have hinter : edgeSetOn G a ∩ edgeSetOn G b = ∅ := by
          rw [edgeSetOn_inter]
          exact edgeSetOn_inter_eq_empty_of_card_le_one G (a ∩ b) hi
        have hedge := hsep.edge_count_identity
        rw [hinter, Set.ncard_empty, add_zero] at hedge
        have hverts := Finset.card_union_add_card_inter a b
        rw [hsep.union_eq] at hverts
        have ha1 : 1 ≤ a.card := by
          obtain ⟨v, hv⟩ := hsep.left_nonempty
          exact Finset.card_pos.mpr ⟨v, (Finset.mem_sdiff.mp hv).1⟩
        have hb1 : 1 ≤ b.card := by
          obtain ⟨v, hv⟩ := hsep.right_nonempty
          exact Finset.card_pos.mpr ⟨v, (Finset.mem_sdiff.mp hv).1⟩
        exfalso
        omega
      · by_cases htwo : Nonempty (TwoSeparationOn G s)
        · let h := Classical.choice htwo
          have ha_lt : h.leftSet.card < n := by
            rw [← hn]
            exact Finset.card_lt_card h.separation.left_ssubset
          have hb_lt : h.rightSet.card < n := by
            rw [← hn]
            exact Finset.card_lt_card h.separation.right_ssubset
          have hi_card : (h.leftSet ∩ h.rightSet).card = 2 := by
            simp [h.inter_eq, h.ne]
          have ha3 : 3 ≤ h.leftSet.card := by
            have hproper : h.leftSet ∩ h.rightSet ⊂ h.leftSet := by
              refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, ?_⟩
              obtain ⟨v, hv⟩ := h.separation.left_nonempty
              have ⟨hvl, hvr⟩ := Finset.mem_sdiff.mp hv
              intro heq
              apply hvr
              have hvinter : v ∈ h.leftSet ∩ h.rightSet := by
                rw [heq]
                exact hvl
              exact (Finset.mem_inter.mp hvinter).2
            have := Finset.card_lt_card hproper
            omega
          have hb3 : 3 ≤ h.rightSet.card := by
            have hproper : h.leftSet ∩ h.rightSet ⊂ h.rightSet := by
              refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, ?_⟩
              obtain ⟨v, hv⟩ := h.separation.right_nonempty
              have ⟨hvr, hvl⟩ := Finset.mem_sdiff.mp hv
              intro heq
              apply hvl
              have hvinter : v ∈ h.leftSet ∩ h.rightSet := by
                rw [heq]
                exact hvr
              exact (Finset.mem_inter.mp hvinter).1
            have := Finset.card_lt_card hproper
            omega
          have ha_bound := bound h.leftSet ha_lt
          have hb_bound := bound h.rightSet hb_lt
          have hedge := h.separation.edge_count_identity
          have hverts := Finset.card_union_add_card_inter h.leftSet h.rightSet
          rw [h.separation.union_eq] at hverts
          by_cases hadj : G.Adj h.sepX h.sepY
          · have hinter := edgeSetOn_inter_eq_singleton G h.leftSet h.rightSet
                h.ne h.inter_eq hadj
            rw [hinter, Set.ncard_singleton] at hedge
            have ha_eq : (edgeSetOn G h.leftSet).ncard =
                2 * h.leftSet.card - 3 := by omega
            have hb_eq : (edgeSetOn G h.rightSet).ncard =
                2 * h.rightSet.card - 3 := by omega
            have hca : IsCockadeOn G h.leftSet :=
              ih h.leftSet.card ha_lt G h.leftSet ha3 hfree ha_eq rfl
            have hcb : IsCockadeOn G h.rightSet :=
              ih h.rightSet.card hb_lt G h.rightSet hb3 hfree hb_eq rfl
            rw [← h.separation.union_eq]
            exact IsCockadeOn.glue hca hcb h.ne h.inter_eq hadj h.separation.no_cross
          · have hinter := edgeSetOn_inter_eq_empty_of_pair_nonadj G
                h.inter_eq hadj
            rw [hinter, Set.ncard_empty, add_zero] at hedge
            have ha_strict : (edgeSetOn G h.leftSet).ncard <
                2 * h.leftSet.card - 3 := by
              by_contra hnot
              have ha_eq : (edgeSetOn G h.leftSet).ncard =
                  2 * h.leftSet.card - 3 := by omega
              have hca : IsCockadeOn G h.leftSet :=
                ih h.leftSet.card ha_lt G h.leftSet ha3 hfree ha_eq rfl
              apply hfree
              exact hca.hasThreeSpokeCycle_of_external (fun _ _ h ↦ h)
                h.left_members.1 h.left_members.2 h.ne hadj h.rightPath
                h.rightPath_external_left
            have hb_strict : (edgeSetOn G h.rightSet).ncard <
                2 * h.rightSet.card - 3 := by
              by_contra hnot
              have hb_eq : (edgeSetOn G h.rightSet).ncard =
                  2 * h.rightSet.card - 3 := by omega
              have hcb : IsCockadeOn G h.rightSet :=
                ih h.rightSet.card hb_lt G h.rightSet hb3 hfree hb_eq rfl
              apply hfree
              exact hcb.hasThreeSpokeCycle_of_external (fun _ _ h ↦ h)
                h.right_members.1 h.right_members.2 h.ne hadj h.leftPath
                h.leftPath_external_right
            exfalso
            omega
        · apply hcore G s hs3 hlow htwo hfree hexact
          intro H t hts ht3 hHfree hHexact
          apply ih t.card (by omega) H t ht3 hHfree hHexact rfl

theorem cliqueFree_three_of_core
    {G : SimpleGraph V} {s : Finset V}
    (hs4 : 4 ≤ s.card)
    (hnlow : ¬HasLowSeparationOn G s)
    (hntwo : ¬Nonempty (TwoSeparationOn G s))
    (hfree : ¬HasThreeSpokeCycleTest G) :
    (G.induce (s : Set V)).CliqueFree 3 := by
  classical
  intro t ht
  rw [is3Clique_iff] at ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht
  have hab' : G.Adj (a : V) (b : V) := hab
  have hac' : G.Adj (a : V) (c : V) := hac
  have hbc' : G.Adj (b : V) (c : V) := hbc
  apply hfree
  exact hasThreeSpokeCycle_of_triangle hs4 hnlow hntwo
    a.property b.property c.property hab'.ne hac'.ne hbc'.ne
    hab' hac' hbc'

theorem isCockadeOn_of_core_exact_of_card_le_six
    {G : SimpleGraph V} {s : Finset V}
    (hs3 : 3 ≤ s.card) (hs6 : s.card ≤ 6)
    (hnlow : ¬HasLowSeparationOn G s)
    (hntwo : ¬Nonempty (TwoSeparationOn G s))
    (hfree : ¬HasThreeSpokeCycleTest G)
    (hE : (edgeSetOn G s).ncard = 2 * s.card - 3) :
    IsCockadeOn G s := by
  classical
  by_cases hs : s.card = 3
  · apply isCockadeOn_of_card_three_of_edge_count G s hs
    omega
  have hs4 : 4 ≤ s.card := by omega
  have hcf := cliqueFree_three_of_core hs4 hnlow hntwo hfree
  by_cases hsix : s.card = 6
  · apply isCockadeOn_of_card_six_of_edge_count_of_cliqueFree G s hsix
    · omega
    · exact hcf
  let K : SimpleGraph (s : Set V) := G.induce (s : Set V)
  letI : DecidableRel K.Adj := Classical.decRel _
  have hKcard : Fintype.card (s : Set V) = s.card := by simp
  have hKedges : K.edgeFinset.card = 2 * s.card - 3 := by
    have hn : (K.edgeFinset : Set (Sym2 (s : Set V))).ncard = K.edgeSet.ncard := by
      simp
    rw [Set.ncard_coe_finset] at hn
    rw [hn, ← ncard_edgeSetOn]
    exact hE
  have hbound := hcf.card_edgeFinset_le (r := 2)
  change K.edgeFinset.card ≤ _ at hbound
  rw [hKcard, hKedges] at hbound
  have hcard : s.card = 4 ∨ s.card = 5 := by omega
  rcases hcard with hcard | hcard <;> norm_num [hcard] at hbound

theorem exists_degree_le_one_of_isAcyclic
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hne : Nonempty W) (hacyc : G.IsAcyclic) :
    ∃ w, G.degree w ≤ 1 := by
  let w₀ : W := Classical.choice hne
  let c : G.ConnectedComponent := G.connectedComponentMk w₀
  letI : Fintype c := Fintype.ofFinite c
  letI : DecidableRel c.toSimpleGraph.Adj := Classical.decRel _
  have htree : c.toSimpleGraph.IsTree := hacyc.isTree_connectedComponent c
  have degree_eq (w : c) : c.toSimpleGraph.degree w = G.degree w := by
    apply Finset.card_bij (s := c.toSimpleGraph.neighborFinset w)
      (t := G.neighborFinset (w : W)) (fun z _ ↦ (z : W))
    · intro z hz
      apply (mem_neighborFinset (G := G) (v := (w : W)) (z : W)).mpr
      apply (c.toSimpleGraph_adj w.property z.property).mp
      exact (mem_neighborFinset (G := c.toSimpleGraph) (v := w) z).mp hz
    · intro z₁ _ z₂ _ hz
      exact Subtype.ext hz
    · intro z hz
      have hwz : G.Adj (w : W) z := by simpa using hz
      have hzc : z ∈ c := c.mem_supp_of_adj_mem_supp w.property hwz
      refine ⟨⟨z, hzc⟩, ?_, rfl⟩
      apply (mem_neighborFinset (G := c.toSimpleGraph) (v := w) ⟨z, hzc⟩).mpr
      exact (c.toSimpleGraph_adj w.property hzc).mpr hwz
  cases subsingleton_or_nontrivial c with
  | inl hc =>
      letI : Subsingleton c := hc
      let w : c := ⟨w₀, ConnectedComponent.connectedComponentMk_mem⟩
      refine ⟨w, ?_⟩
      rw [← degree_eq w]
      change (c.toSimpleGraph.neighborFinset w).card ≤ 1
      have hempty : c.toSimpleGraph.neighborFinset w = ∅ := by
        ext z
        simp [Subsingleton.elim z w]
      simp [hempty]
  | inr hc =>
      letI : Nontrivial c := hc
      obtain ⟨w, hw⟩ := htree.exists_vert_degree_one_of_nontrivial
      refine ⟨w, ?_⟩
      rw [← degree_eq w, hw]

omit [Fintype V] in
theorem Walk.IsCycle.isChordless_of_length_eq_girth
    {G : SimpleGraph V} {v : V} {c : G.Walk v v}
    (hc : c.IsCycle) (hlen : G.girth = c.length) : c.IsChordless := by
  classical
  intro e he
  induction e using Sym2.inductionOn with
  | _ u w =>
      rw [Walk.isChord_sym2Mk] at he
      rcases he with ⟨huw, hec, hu, hw⟩
      have huwne : u ≠ w := huw.ne
      let c' : G.Walk u u := c.rotate u hu
      have hc' : c'.IsCycle := by
        exact hc.rotate hu
      have hw' : w ∈ c'.support := by simpa [c'] using hw
      let p : G.Walk u w := c'.takeUntil w hw'
      let q : G.Walk w u := c'.dropUntil w hw'
      have hsplit : p.append q = c' := by
        exact c'.take_spec hw'
      have hpnon : ¬p.Nil := Walk.not_nil_of_ne huwne
      have hqpath : q.IsPath := by
        apply Walk.IsCycle.isPath_of_append_right hpnon
        rw [hsplit]
        exact hc'
      have hec' : s(u, w) ∉ c'.edges := by
        intro h
        apply hec
        exact (c.rotate_edges u hu).perm.mem_iff.mp h
      have heq : s(u, w) ∉ q.edges := by
        intro h
        exact hec' (c'.edges_dropUntil_subset_edges hw' h)
      let d : G.Walk u u := Walk.cons huw q
      have hd : d.IsCycle := by
        exact (Walk.cons_isCycle_iff q huw).mpr ⟨hqpath, heq⟩
      have hp2 : 2 ≤ p.length := by
        by_contra hp2
        have hp1 : p.length ≤ 1 := by omega
        have hpedge : p = huw.toWalk := by
          exact Walk.eq_of_length_le_one hp1 (by simp)
        have : s(u, w) ∈ p.edges := by simp [hpedge]
        exact hec' (c'.edges_takeUntil_subset_edges hw' this)
      have hlength : p.length + q.length = c.length := by
        have hlength' := congrArg Walk.length hsplit
        rw [Walk.length_append] at hlength'
        have hc'length : c'.length = c.length := by simp [c']
        omega
      have hshort : d.length < c.length := by
        simp only [d, Walk.length_cons]
        omega
      have := girth_le_length hd
      rw [hlen] at this
      omega

theorem Walk.IsCycle.card_neighbors_in_support_eq_two
    {G : SimpleGraph V} {v x : V} {c : G.Walk v v}
    [DecidableRel G.Adj]
    (hc : c.IsCycle) (hchord : c.IsChordless) (hx : x ∈ c.support) :
    (G.neighborFinset x ∩ c.support.toFinset).card = 2 := by
  classical
  let r : G.Walk x x := c.rotate x hx
  have hr : r.IsCycle := hc.rotate hx
  have hrnon : ¬r.Nil := hr.not_nil
  have hrlen : 2 ≤ r.length := (hr.three_le_length.trans' (by omega))
  have htailnon : ¬r.tail.Nil := by
    rw [Walk.not_nil_iff_lt_length]
    have := r.length_tail_add_one hrnon
    omega
  have hpen : r.penultimate = r.tail.penultimate := by
    calc
      r.penultimate = (Walk.cons (r.adj_snd hrnon) r.tail).penultimate := by
        rw [r.cons_tail_eq hrnon]
      _ = r.tail.penultimate := Walk.penultimate_cons_of_not_nil _ _ htailnon
  have hedge_rotate {a b : V} : s(a, b) ∈ c.edges ↔ s(a, b) ∈ r.edges := by
    exact (c.rotate_edges x hx).perm.mem_iff.symm
  have hfin : G.neighborFinset x ∩ c.support.toFinset = {r.snd, r.penultimate} := by
    ext y
    simp only [Finset.mem_inter, mem_neighborFinset, List.mem_toFinset,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxy, hyc⟩
      have hedgeC : s(x, y) ∈ c.edges := hchord.mem_edges hx hyc hxy
      have hedgeR : s(x, y) ∈ r.edges := hedge_rotate.mp hedgeC
      rw [← r.cons_tail_eq hrnon, Walk.edges_cons, List.mem_cons] at hedgeR
      rcases hedgeR with hedgeR | hedgeR
      · rw [Sym2.eq_iff] at hedgeR
        rcases hedgeR with ⟨_, hy⟩ | ⟨_, hyx⟩
        · exact Or.inl hy
        · exact (hxy.ne hyx.symm).elim
      · right
        have hy := hr.isPath_tail.eq_penultimate_of_mem_edges hedgeR
        exact hy.trans hpen.symm
    · intro hy
      have hsupport : y ∈ r.support := by
        rcases hy with rfl | rfl
        · exact List.mem_of_mem_tail (r.snd_mem_tail_support hrnon)
        · exact List.mem_of_mem_dropLast (r.penultimate_mem_dropLast_support hrnon)
      have hyc : y ∈ c.support := by simpa [r] using hsupport
      refine ⟨?_, hyc⟩
      rcases hy with rfl | rfl
      · exact r.adj_snd hrnon
      · exact (r.adj_penultimate hrnon).symm
  rw [hfin, Finset.card_pair hr.snd_ne_penultimate]

theorem Walk.IsCycle.existsUnique_neighborOn_not_mem_support
    {G : SimpleGraph V} {s : Finset V} {v x : V} {c : G.Walk v v}
    (hc : c.IsCycle) (hchord : c.IsChordless) (hx : x ∈ c.support)
    (hcs : ∀ z ∈ c.support, z ∈ s)
    (hdeg : (neighborFinsetOn G s x).card = 3) :
    ∃! y, y ∈ s ∧ G.Adj x y ∧ y ∉ c.support := by
  classical
  let n := neighborFinsetOn G s x
  let inside := n ∩ c.support.toFinset
  let outside := n \ inside
  have hinside : inside.card = 2 := by
    have heq : inside = G.neighborFinset x ∩ c.support.toFinset := by
      ext y
      simp only [inside, n, neighborFinsetOn, Finset.mem_inter,
        Finset.mem_filter, mem_neighborFinset, List.mem_toFinset]
      constructor
      · rintro ⟨⟨_, hxy⟩, hyc⟩
        exact ⟨hxy, hyc⟩
      · rintro ⟨hxy, hyc⟩
        exact ⟨⟨hcs y hyc, hxy⟩, hyc⟩
    rw [heq]
    exact Walk.IsCycle.card_neighbors_in_support_eq_two hc hchord hx
  have houtside : outside.card = 1 := by
    change (n \ inside).card = 1
    rw [Finset.card_sdiff_of_subset Finset.inter_subset_left, hinside]
    have hncard : n.card = 3 := by simpa [n] using hdeg
    omega
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp houtside
  have hyout : y ∈ outside := by simp [hy]
  have hyn : y ∈ n := (Finset.mem_sdiff.mp hyout).1
  have hyinside : y ∉ inside := (Finset.mem_sdiff.mp hyout).2
  have hys : y ∈ s := (Finset.mem_filter.mp hyn).1
  have hxy : G.Adj x y := (Finset.mem_filter.mp hyn).2
  have hyc : y ∉ c.support := by
    intro hyc
    exact hyinside (Finset.mem_inter.mpr ⟨hyn, by simpa⟩)
  refine ⟨y, ⟨hys, hxy, hyc⟩, ?_⟩
  intro z hz
  have hzn : z ∈ n := Finset.mem_filter.mpr ⟨hz.1, hz.2.1⟩
  have hzout : z ∈ outside := Finset.mem_sdiff.mpr ⟨hzn, ?_⟩
  · simpa [hy] using hzout
  · intro hzinside
    exact hz.2.2 (by simpa using (Finset.mem_inter.mp hzinside).2)

theorem edgeSetOn_ncard_sdiff_cycle
    {G : SimpleGraph V} {s : Finset V} {v : V} {c : G.Walk v v}
    (hc : c.IsCycle) (hchord : c.IsChordless)
    (hcs : ∀ z ∈ c.support, z ∈ s)
    (hdeg : ∀ z ∈ c.support, (neighborFinsetOn G s z).card = 3) :
    (edgeSetOn G (s \ c.support.toFinset)).ncard + 2 * c.length =
      (edgeSetOn G s).ncard := by
  classical
  let C : Finset V := c.support.toFinset
  let T : Finset V := s \ C
  let A : Set (Sym2 V) := edgeSetOn G C
  let B : Set (Sym2 V) := edgeSetOn G T
  let X : Set (Sym2 V) := edgeSetOn G s \ (A ∪ B)
  have hCsub : C ⊆ s := by
    intro z hz
    exact hcs z (by simpa [C] using hz)
  have hCcard : C.card = c.length := by
    have htailmem : v ∈ c.support.tail := c.end_mem_tail_support hc.not_nil
    have htoFinset : c.support.toFinset = c.support.tail.toFinset := by
      ext z
      simp only [List.mem_toFinset]
      constructor
      · intro hz
        have hz' : z = v ∨ z ∈ c.support.tail := by
          have hzcons : z ∈ v :: c.support.tail := by
            rw [Walk.cons_tail_support c]
            exact hz
          exact List.mem_cons.mp hzcons
        exact hz'.elim (fun h ↦ h ▸ htailmem) id
      · exact List.mem_of_mem_tail
    change c.support.toFinset.card = c.length
    rw [htoFinset, List.toFinset_card_of_nodup hc.support_nodup,
      List.length_tail, c.length_support]
    omega
  have hAeq : A = (c.edges.toFinset : Finset (Sym2 V)) := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y =>
        simp only [A, edgeSetOn, Set.mem_inter_iff, mem_edgeSet,
          Set.mk_mem_sym2_iff, Finset.mem_coe, List.mem_toFinset]
        constructor
        · rintro ⟨hxy, hxC, hyC⟩
          apply hchord.mem_edges
          · simpa [C] using hxC
          · simpa [C] using hyC
          · exact hxy
        · intro hxy
          exact ⟨c.adj_of_mem_edges hxy,
            by simpa [C] using c.fst_mem_support_of_mem_edges hxy,
            by simpa [C] using c.snd_mem_support_of_mem_edges hxy⟩
  have hAncard : A.ncard = c.length := by
    rw [hAeq, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup hc.isTrail.edges_nodup]
    exact c.length_edges
  let out : (z : C) → V := fun z ↦
    Classical.choose (Walk.IsCycle.existsUnique_neighborOn_not_mem_support hc hchord
      (by simpa only [C, List.mem_toFinset] using z.property) hcs
      (hdeg z (by simpa only [C, List.mem_toFinset] using z.property)))
  have out_spec (z : C) :
      out z ∈ s ∧ G.Adj z (out z) ∧ out z ∉ c.support := by
    exact (Classical.choose_spec (Walk.IsCycle.existsUnique_neighborOn_not_mem_support hc hchord
      (by simpa only [C, List.mem_toFinset] using z.property) hcs
      (hdeg z (by simpa only [C, List.mem_toFinset] using z.property)))).1
  have out_unique (z : C) {y : V}
      (hy : y ∈ s ∧ G.Adj z y ∧ y ∉ c.support) : y = out z := by
    exact (Classical.choose_spec (Walk.IsCycle.existsUnique_neighborOn_not_mem_support hc hchord
      (by simpa only [C, List.mem_toFinset] using z.property) hcs
      (hdeg z (by simpa only [C, List.mem_toFinset] using z.property)))).2 y hy
  let f : C → Sym2 V := fun z ↦ s((z : V), out z)
  have hf_injective : Function.Injective f := by
    intro z w hzw
    have hzout : out z ∉ C := by simpa [C] using (out_spec z).2.2
    have hwout : out w ∉ C := by simpa [C] using (out_spec w).2.2
    change s((z : V), out z) = s((w : V), out w) at hzw
    rw [Sym2.eq_iff] at hzw
    rcases hzw with ⟨hzw, _⟩ | ⟨hzow, hwz⟩
    · exact Subtype.ext hzw
    · exact (hzout (hwz ▸ w.property)).elim
  have hXeq : X = Set.range f := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y =>
        simp only [X, Set.mem_sdiff, Set.mem_union, A, B, edgeSetOn,
          Set.mem_inter_iff, mem_edgeSet, Set.mk_mem_sym2_iff, Set.mem_range]
        constructor
        · rintro ⟨⟨hxy, hxs, hys⟩, hnAB⟩
          have hnA : ¬(G.Adj x y ∧ x ∈ C ∧ y ∈ C) := fun h ↦ hnAB (Or.inl h)
          have hnB : ¬(G.Adj x y ∧ x ∈ T ∧ y ∈ T) := fun h ↦ hnAB (Or.inr h)
          have hxCases : x ∈ C ∨ x ∈ T := by
            by_cases hxC : x ∈ C
            · exact Or.inl hxC
            · exact Or.inr (Finset.mem_sdiff.mpr ⟨hxs, hxC⟩)
          have hyCases : y ∈ C ∨ y ∈ T := by
            by_cases hyC : y ∈ C
            · exact Or.inl hyC
            · exact Or.inr (Finset.mem_sdiff.mpr ⟨hys, hyC⟩)
          rcases hxCases with hxC | hxT <;> rcases hyCases with hyC | hyT
          · exact (hnA ⟨hxy, hxC, hyC⟩).elim
          · let z : C := ⟨x, hxC⟩
            have hyNot : y ∉ c.support := by
              simpa [C] using (Finset.mem_sdiff.mp hyT).2
            have hyout : y = out z := out_unique z ⟨hys, hxy, hyNot⟩
            refine ⟨z, ?_⟩
            change s((z : V), out z) = s(x, y)
            rw [show (z : V) = x from rfl, hyout]
          · let z : C := ⟨y, hyC⟩
            have hxNot : x ∉ c.support := by
              simpa [C] using (Finset.mem_sdiff.mp hxT).2
            have hxout : x = out z := out_unique z ⟨hxs, hxy.symm, hxNot⟩
            refine ⟨z, ?_⟩
            change s((z : V), out z) = s(x, y)
            rw [show (z : V) = y from rfl, hxout]
            exact Sym2.eq_swap
          · exact (hnB ⟨hxy, hxT, hyT⟩).elim
        · rintro ⟨z, he⟩
          have hz := out_spec z
          have hzC : (z : V) ∈ C := z.property
          have hzT : (z : V) ∉ T := by simp [T, hzC]
          have houtC : out z ∉ C := by simpa [C] using hz.2.2
          have houtT : out z ∈ T := Finset.mem_sdiff.mpr ⟨hz.1, houtC⟩
          change s((z : V), out z) = s(x, y) at he
          rw [Sym2.eq_iff] at he
          rcases he with ⟨hzx, houty⟩ | ⟨hzy, houtx⟩
          · subst x
            subst y
            refine ⟨⟨hz.2.1, hCsub hzC, hz.1⟩, ?_⟩
            intro hAB
            rcases hAB with hA | hB
            · exact houtC hA.2.2
            · exact hzT hB.2.1
          · subst y
            subst x
            refine ⟨⟨hz.2.1.symm, hz.1, hCsub hzC⟩, ?_⟩
            intro hAB
            rcases hAB with hA | hB
            · exact houtC hA.2.1
            · exact hzT hB.2.2
  have hXncard : X.ncard = C.card := by
    rw [hXeq, Set.ncard_range_of_injective hf_injective,
      Nat.card_eq_fintype_card]
    simp
  have hABdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ heA heB
    change G.Adj x y ∧ x ∈ C ∧ y ∈ C at heA
    change G.Adj x y ∧ x ∈ T ∧ y ∈ T at heB
    exact (Finset.mem_sdiff.mp heB.2.1).2 heA.2.1
  have hABsub : A ∪ B ⊆ edgeSetOn G s := by
    rintro ⟨x, y⟩ (he | he)
    · change G.Adj x y ∧ x ∈ C ∧ y ∈ C at he
      exact ⟨he.1, hCsub he.2.1, hCsub he.2.2⟩
    · change G.Adj x y ∧ x ∈ T ∧ y ∈ T at he
      exact ⟨he.1, (Finset.mem_sdiff.mp he.2.1).1,
        (Finset.mem_sdiff.mp he.2.2).1⟩
  have hpartition : (A ∪ B) ∪ X = edgeSetOn G s := by
    exact Set.union_sdiff_cancel hABsub
  have hABXdisj : Disjoint (A ∪ B) X := Set.disjoint_sdiff_right
  have hcardAB : (A ∪ B).ncard = A.ncard + B.ncard :=
    Set.ncard_union_eq hABdisj
  have hcardAll : (edgeSetOn G s).ncard = (A ∪ B).ncard + X.ncard := by
    rw [← hpartition]
    exact Set.ncard_union_eq hABXdisj
  change B.ncard + 2 * c.length = (edgeSetOn G s).ncard
  rw [hcardAll, hcardAB, hAncard, hXncard, hCcard]
  omega

noncomputable def degreeThreeSetOn (G : SimpleGraph V) (s : Finset V) : Finset V :=
  s.filter fun z ↦ (neighborFinsetOn G s z).card = 3

theorem exists_chordless_degreeThree_cycle_of_not_isAcyclic
    {G : SimpleGraph V} {s : Finset V}
    (hacyc : ¬(G.induce (degreeThreeSetOn G s : Set V)).IsAcyclic) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.IsChordless ∧
      (∀ z ∈ c.support, z ∈ s) ∧
      (∀ z ∈ c.support, (neighborFinsetOn G s z).card = 3) := by
  classical
  let D : Finset V := degreeThreeSetOn G s
  let K : SimpleGraph (D : Set V) := G.induce (D : Set V)
  obtain ⟨v, c, hc, hlen⟩ := exists_girth_eq_length.mpr (by simpa [K, D] using hacyc)
  have hchordK : c.IsChordless :=
    Walk.IsCycle.isChordless_of_length_eq_girth hc hlen
  let e : K ↪g G := SimpleGraph.Embedding.induce (D : Set V)
  let C : G.Walk (e v) (e v) := c.map e.toHom
  have hCcycle : C.IsCycle := hc.map e.injective
  have hCdata (z : V) (hz : z ∈ C.support) :
      z ∈ s ∧ (neighborFinsetOn G s z).card = 3 := by
    have hzmap : z ∈ c.support.map e := by simpa [C] using hz
    obtain ⟨z₀, hz₀, rfl⟩ := List.mem_map.mp hzmap
    have hzD : (z₀ : V) ∈ D := z₀.property
    have heval : e z₀ = (z₀ : V) := rfl
    rw [heval]
    simpa only [D, degreeThreeSetOn, Finset.mem_filter] using hzD
  have hCchord : C.IsChordless := by
    rw [Walk.isChordless_iff_forall_mem_edges]
    intro x y hx hy hxy
    have hxmap : x ∈ c.support.map e := by simpa [C] using hx
    have hymap : y ∈ c.support.map e := by simpa [C] using hy
    obtain ⟨x₀, hx₀, rfl⟩ := List.mem_map.mp hxmap
    obtain ⟨y₀, hy₀, rfl⟩ := List.mem_map.mp hymap
    have hxyK : K.Adj x₀ y₀ := hxy
    have hedgeK : s(x₀, y₀) ∈ c.edges := hchordK.mem_edges hx₀ hy₀ hxyK
    change s(e x₀, e y₀) ∈ (c.map e.toHom).edges
    rw [Walk.edges_map]
    exact List.mem_map.mpr ⟨s(x₀, y₀), hedgeK, by simp [e]⟩
  exact ⟨e v, C, hCcycle, hCchord,
    fun z hz ↦ (hCdata z hz).1, fun z hz ↦ (hCdata z hz).2⟩

omit [Fintype V] [DecidableEq V] in
theorem Walk.length_induce_eq {G : SimpleGraph V} {S : Set V} {u v : V}
    (w : G.Walk u v) (hw : ∀ z ∈ w.support, z ∈ S) :
    (w.induce S hw).length = w.length := by
  induction w with
  | nil => rfl
  | cons h w ih =>
      simp only [Walk.induce_cons, Walk.length_cons]
      rw [ih]

theorem Walk.IsCycle.four_le_length_of_cliqueFree_induce
    {G : SimpleGraph V} {s : Finset V} {v : V} {c : G.Walk v v}
    (hc : c.IsCycle) (hcs : ∀ z ∈ c.support, z ∈ s)
    (hcf : (G.induce (s : Set V)).CliqueFree 3) :
    4 ≤ c.length := by
  classical
  have hthree : 3 ≤ c.length := hc.three_le_length
  by_contra hfour
  have hlen : c.length = 3 := by omega
  let ci := c.induce (s : Set V) hcs
  let e : G.induce (s : Set V) ↪g G := SimpleGraph.Embedding.induce (s : Set V)
  have hmap : ci.map e.toHom = c := by
    exact Walk.map_induce c hcs
  have hci : ci.IsCycle := by
    have hmapcycle : (ci.map e.toHom).IsCycle := hmap.symm ▸ hc
    exact (Walk.map_isCycle_iff_of_injective (p := ci) e.injective).mp hmapcycle
  have hcilen : ci.length = 3 := by
    have hlength : ci.length = c.length := by
      exact Walk.length_induce_eq c hcs
    exact hlength.trans hlen
  obtain ⟨t, ht⟩ :=
    is3Clique_iff_exists_cycle_length_three.mpr ⟨_, ci, hci, hcilen⟩
  exact hcf t ht

theorem Walk.IsCycle.card_support_toFinset_eq_length
    {G : SimpleGraph V} {v : V} {c : G.Walk v v} (hc : c.IsCycle) :
    c.support.toFinset.card = c.length := by
  classical
  have htailmem : v ∈ c.support.tail := c.end_mem_tail_support hc.not_nil
  have htoFinset : c.support.toFinset = c.support.tail.toFinset := by
    ext z
    simp only [List.mem_toFinset]
    constructor
    · intro hz
      have hz' : z = v ∨ z ∈ c.support.tail := by
        have hzcons : z ∈ v :: c.support.tail := by
          rw [Walk.cons_tail_support c]
          exact hz
        exact List.mem_cons.mp hzcons
      exact hz'.elim (fun h ↦ h ▸ htailmem) id
    · exact List.mem_of_mem_tail
  rw [htoFinset, List.toFinset_card_of_nodup hc.support_nodup,
    List.length_tail, c.length_support]
  omega

theorem exists_cycle_external_neighbor_set
    {G : SimpleGraph V} {s : Finset V} {v : V} {c : G.Walk v v}
    (hs7 : 7 ≤ s.card)
    (hnlow : ¬HasLowSeparationOn G s)
    (hntwo : ¬Nonempty (TwoSeparationOn G s))
    (hfree : ¬HasThreeSpokeCycleTest G)
    (hc : c.IsCycle) (hchord : c.IsChordless)
    (hcs : ∀ z ∈ c.support, z ∈ s)
    (hdeg : ∀ z ∈ c.support, (neighborFinsetOn G s z).card = 3) :
    ∃ (out : (z : c.support.toFinset) → V) (W : Finset V),
      (∀ z, out z ∈ s ∧ G.Adj z (out z) ∧ out z ∉ c.support) ∧
      (∀ (z : c.support.toFinset) (y : V),
        y ∈ s ∧ G.Adj z y ∧ y ∉ c.support → y = out z) ∧
      W = c.support.toFinset.attach.image out ∧ 3 ≤ W.card := by
  classical
  let C : Finset V := c.support.toFinset
  let T : Finset V := s \ C
  have hCsub : C ⊆ s := by
    intro z hz
    exact hcs z (by simpa [C] using hz)
  have hCcard : C.card = c.length := by
    simpa [C] using Walk.IsCycle.card_support_toFinset_eq_length hc
  let out : (z : C) → V := fun z ↦
    Classical.choose (Walk.IsCycle.existsUnique_neighborOn_not_mem_support hc hchord
      (by simpa only [C, List.mem_toFinset] using z.property) hcs
      (hdeg z (by simpa only [C, List.mem_toFinset] using z.property)))
  have out_spec (z : C) :
      out z ∈ s ∧ G.Adj z (out z) ∧ out z ∉ c.support := by
    exact (Classical.choose_spec (Walk.IsCycle.existsUnique_neighborOn_not_mem_support hc hchord
      (by simpa only [C, List.mem_toFinset] using z.property) hcs
      (hdeg z (by simpa only [C, List.mem_toFinset] using z.property)))).1
  have out_unique (z : C) (y : V)
      (hy : y ∈ s ∧ G.Adj z y ∧ y ∉ c.support) : y = out z := by
    exact (Classical.choose_spec (Walk.IsCycle.existsUnique_neighborOn_not_mem_support hc hchord
      (by simpa only [C, List.mem_toFinset] using z.property) hcs
      (hdeg z (by simpa only [C, List.mem_toFinset] using z.property)))).2 y hy
  let W : Finset V := C.attach.image out
  have houtW (z : C) : out z ∈ W := by
    exact Finset.mem_image.mpr ⟨z, by simp, rfl⟩
  have hWsubT : W ⊆ T := by
    intro w hw
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_sdiff.mpr ⟨(out_spec z).1,
      by simpa [C] using (out_spec z).2.2⟩
  let fiber : V → Finset C := fun w ↦ C.attach.filter fun z ↦ out z = w
  have hfiber (w : V) (hw : w ∈ W) : (fiber w).card ≤ 2 := by
    by_contra hle
    have hthree : 2 < (fiber w).card := by omega
    obtain ⟨a, ha, b, hb, d, hd, hab, had, hbd⟩ := Finset.two_lt_card.mp hthree
    have haw : out a = w := (Finset.mem_filter.mp ha).2
    have hbw : out b = w := (Finset.mem_filter.mp hb).2
    have hdw : out d = w := (Finset.mem_filter.mp hd).2
    have hwout : w ∉ c.support := by
      rw [← haw]
      exact (out_spec a).2.2
    apply hfree
    refine ⟨v, w, c, hc, hwout, a, ?_, b, ?_, d, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [C, List.mem_toFinset] using a.property
    · simpa only [C, List.mem_toFinset] using b.property
    · simpa only [C, List.mem_toFinset] using d.property
    · exact fun h ↦ hab (Subtype.ext h)
    · exact fun h ↦ had (Subtype.ext h)
    · exact fun h ↦ hbd (Subtype.ext h)
    · constructor
      · rw [← haw]
        exact (out_spec a).2.1.symm
      constructor
      · rw [← hbw]
        exact (out_spec b).2.1.symm
      · rw [← hdw]
        exact (out_spec d).2.1.symm
  have hcover : W.biUnion fiber = C.attach := by
    ext z
    constructor
    · intro _
      simp
    · intro _
      apply Finset.mem_biUnion.mpr
      exact ⟨out z, houtW z, Finset.mem_filter.mpr ⟨by simp, rfl⟩⟩
  have hCle : C.card ≤ W.card * 2 := by
    calc
      C.card = C.attach.card := by simp
      _ = (W.biUnion fiber).card := by rw [hcover]
      _ ≤ W.card * 2 := Finset.card_biUnion_le_card_mul W fiber 2 hfiber
  have hs4 : 4 ≤ s.card := by omega
  have hcf := cliqueFree_three_of_core hs4 hnlow hntwo hfree
  have hlen4 : 4 ≤ c.length :=
    Walk.IsCycle.four_le_length_of_cliqueFree_induce hc hcs hcf
  have hW3 : 3 ≤ W.card := by
    by_contra hW3
    have hW2 : W.card ≤ 2 := by omega
    have hlen_le : c.length ≤ 4 := by omega
    have hlen : c.length = 4 := by omega
    have hTcard : T.card = s.card - C.card := by
      exact Finset.card_sdiff_of_subset hCsub
    have hT3 : 3 ≤ T.card := by omega
    have hnsub : ¬T ⊆ W := by
      intro hsub
      have := Finset.card_le_card hsub
      omega
    obtain ⟨y, hyT, hyW⟩ := Finset.not_subset.mp hnsub
    have hvC : v ∈ C := by simp [C]
    have hvW : v ∉ W := by
      intro hv
      exact (Finset.mem_sdiff.mp (hWsubT hv)).2 hvC
    have hys : y ∈ s := (Finset.mem_sdiff.mp hyT).1
    have hyC : y ∉ C := (Finset.mem_sdiff.mp hyT).2
    obtain ⟨p, hp⟩ := reachableOnAvoiding_of_no_small_separation
      hnlow hntwo hW2 (hcs v (Walk.start_mem_support c)) hvW hys hyW
    obtain ⟨a, b, hap, hbp, hab, haC, hbC⟩ :=
      Walk.exists_adj_crossing_finset p hvC hyC
    have has : a ∈ s := (hp a hap).1
    have hbs : b ∈ s := (hp b hbp).1
    have hbW : b ∉ W := (hp b hbp).2
    let za : C := ⟨a, haC⟩
    have hbSupport : b ∉ c.support := by simpa [C] using hbC
    have hbout : b = out za := out_unique za b ⟨hbs, hab, hbSupport⟩
    apply hbW
    rw [hbout]
    exact houtW za
  refine ⟨out, W, ?_, ?_, rfl, hW3⟩
  · exact out_spec
  · intro z y hy
    exact out_unique z y hy

theorem degreeThree_induce_isAcyclic_of_core_exact
    {G : SimpleGraph V} {s : Finset V}
    (hs7 : 7 ≤ s.card)
    (hnlow : ¬HasLowSeparationOn G s)
    (hntwo : ¬Nonempty (TwoSeparationOn G s))
    (hfree : ¬HasThreeSpokeCycleTest G)
    (hE : (edgeSetOn G s).ncard = 2 * s.card - 3)
    (hsmaller : ∀ (H : SimpleGraph V) (t : Finset V), t.card < s.card →
      3 ≤ t.card → ¬HasThreeSpokeCycleTest H →
      (edgeSetOn H t).ncard = 2 * t.card - 3 → IsCockadeOn H t) :
    (G.induce (degreeThreeSetOn G s : Set V)).IsAcyclic := by
  classical
  by_contra hacyc
  obtain ⟨v, c, hc, hchord, hcs, hdeg⟩ :=
    exists_chordless_degreeThree_cycle_of_not_isAcyclic hacyc
  obtain ⟨out, W, out_spec, out_unique, hWdef, hW3⟩ :=
    exists_cycle_external_neighbor_set hs7 hnlow hntwo hfree hc hchord hcs hdeg
  let C : Finset V := c.support.toFinset
  let T : Finset V := s \ C
  have hCsub : C ⊆ s := by
    intro z hz
    exact hcs z (by simpa [C] using hz)
  have hCcard : C.card = c.length := by
    simpa [C] using Walk.IsCycle.card_support_toFinset_eq_length hc
  have hWsubT : W ⊆ T := by
    intro w hw
    rw [hWdef] at hw
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_sdiff.mpr ⟨(out_spec z).1,
      by simpa [C] using (out_spec z).2.2⟩
  have hs4 : 4 ≤ s.card := by omega
  have hpair : ∃ u ∈ W, ∃ w ∈ W, u ≠ w ∧ ¬G.Adj u w := by
    by_contra hpair
    have hcomplete : ∀ {u w : V}, u ∈ W → w ∈ W → u ≠ w → G.Adj u w := by
      intro u w hu hw huw
      by_contra hn
      exact hpair ⟨u, hu, w, hw, huw, hn⟩
    have htwo : 2 < W.card := by omega
    obtain ⟨a, ha, b, hb, d, hd, hab, had, hbd⟩ := Finset.two_lt_card.mp htwo
    have has : a ∈ s := (Finset.mem_sdiff.mp (hWsubT ha)).1
    have hbs : b ∈ s := (Finset.mem_sdiff.mp (hWsubT hb)).1
    have hds : d ∈ s := (Finset.mem_sdiff.mp (hWsubT hd)).1
    apply hfree
    exact hasThreeSpokeCycle_of_triangle hs4 hnlow hntwo has hbs hds hab had hbd
      (hcomplete ha hb hab) (hcomplete ha hd had) (hcomplete hb hd hbd)
  obtain ⟨u, huW, w, hwW, huw, hnuw⟩ := hpair
  have huT : u ∈ T := hWsubT huW
  have hwT : w ∈ T := hWsubT hwW
  have huImage₀ : u ∈ c.support.toFinset.attach.image out := by
    rw [← hWdef]
    exact huW
  have hwImage₀ : w ∈ c.support.toFinset.attach.image out := by
    rw [← hWdef]
    exact hwW
  have huImage : u ∈ C.attach.image out := by simpa [C] using huImage₀
  have hwImage : w ∈ C.attach.image out := by simpa [C] using hwImage₀
  obtain ⟨a, _, hau⟩ := Finset.mem_image.mp huImage
  obtain ⟨b, _, hbw⟩ := Finset.mem_image.mp hwImage
  have haSupport : (a : V) ∈ c.support := by
    simpa only [C, List.mem_toFinset] using a.property
  have hbSupport : (b : V) ∈ c.support := by
    simpa only [C, List.mem_toFinset] using b.property
  have hTcard : T.card = s.card - C.card := Finset.card_sdiff_of_subset hCsub
  have hT3 : 3 ≤ T.card := by
    have := Finset.card_le_card hWsubT
    omega
  have hTlt : T.card < s.card := by
    have hlen3 : 3 ≤ c.length := hc.three_le_length
    omega
  have hdelete := edgeSetOn_ncard_sdiff_cycle hc hchord hcs hdeg
  have hTexact : (edgeSetOn G T).ncard = 2 * T.card - 3 := by
    change (edgeSetOn G (s \ c.support.toFinset)).ncard = _
    omega
  have hcockade : IsCockadeOn G T := hsmaller G T hTlt hT3 hfree hTexact
  let r : G.Walk (a : V) (a : V) := c.rotate a haSupport
  have hbR : (b : V) ∈ r.support := by simpa [r] using hbSupport
  let q : G.Walk (a : V) (b : V) := r.takeUntil b hbR
  let p₀ : G.Walk (out a) (out b) :=
    Walk.cons (out_spec a).2.1.symm
      (q.append (Walk.cons (out_spec b).2.1 Walk.nil))
  let p : G.Walk u w := p₀.copy hau hbw
  have hpExternal : ∀ z ∈ p.support, z ∈ T → z = u ∨ z = w := by
    intro z hzp hzT
    have hzCases : z = out a ∨ z ∈ q.support ∨ z = (b : V) ∨ z = out b := by
      simpa [p, p₀] using hzp
    rcases hzCases with hza | hzq | hzb | hzb
    · exact Or.inl (hza.trans hau)
    · have hzr : z ∈ r.support := r.support_takeUntil_subset_support hbR hzq
      have hzc : z ∈ c.support := by simpa [r] using hzr
      have hzC : z ∈ C := by simpa [C] using hzc
      exact ((Finset.mem_sdiff.mp hzT).2 hzC).elim
    · have hzC : z ∈ C := hzb.symm ▸ b.property
      exact ((Finset.mem_sdiff.mp hzT).2 hzC).elim
    · exact Or.inr (hzb.trans hbw)
  apply hfree
  exact hcockade.hasThreeSpokeCycle_of_external (fun _ _ h ↦ h)
    huT hwT huw hnuw p hpExternal

theorem exists_degreeThree_vertex_with_two_high_neighbors
    {G : SimpleGraph V} {s : Finset V}
    (hs4 : 4 ≤ s.card)
    (hnlow : ¬HasLowSeparationOn G s)
    (hntwo : ¬Nonempty (TwoSeparationOn G s))
    (hE : (edgeSetOn G s).ncard = 2 * s.card - 3)
    (hacyc : (G.induce (degreeThreeSetOn G s : Set V)).IsAcyclic) :
    ∃ x₀ x₁ x₂ x₃, x₀ ∈ s ∧ x₁ ∈ s ∧ x₂ ∈ s ∧ x₃ ∈ s ∧
      x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃ ∧
      G.Adj x₀ x₁ ∧ G.Adj x₀ x₂ ∧ G.Adj x₀ x₃ ∧
      (neighborFinsetOn G s x₀).card = 3 ∧
      4 ≤ (neighborFinsetOn G s x₁).card ∧
      4 ≤ (neighborFinsetOn G s x₂).card := by
  classical
  let D : Finset V := degreeThreeSetOn G s
  let K : SimpleGraph (D : Set V) := G.induce (D : Set V)
  letI : DecidableRel K.Adj := Classical.decRel _
  obtain ⟨x, hxs, hxdeg⟩ :=
    exists_card_neighborFinsetOn_eq_three_of_core_exact hs4 hnlow hntwo hE
  have hxD : x ∈ D := by
    exact Finset.mem_filter.mpr ⟨hxs, hxdeg⟩
  have hDnon : Nonempty (D : Set V) := ⟨⟨x, hxD⟩⟩
  have hKacyc : K.IsAcyclic := by simpa [K, D] using hacyc
  obtain ⟨x₀, hx₀deg⟩ := exists_degree_le_one_of_isAcyclic K hDnon hKacyc
  have degree_eq : K.degree x₀ =
      (neighborFinsetOn G s (x₀ : V) ∩ D).card := by
    change (K.neighborFinset x₀).card = _
    refine Finset.card_bij (s := K.neighborFinset x₀)
      (t := neighborFinsetOn G s (x₀ : V) ∩ D) (fun y _ ↦ (y : V)) ?_ ?_ ?_
    · intro y hy
      have hyAdj : G.Adj (x₀ : V) (y : V) := by
        simpa [K] using (K.mem_neighborFinset x₀ y).mp hy
      have hyD : (y : V) ∈ D := y.property
      have hyS : (y : V) ∈ s := (Finset.mem_filter.mp hyD).1
      exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨hyS, hyAdj⟩, hyD⟩
    · intro y₁ _ y₂ _ h
      exact Subtype.ext h
    · intro y hy
      have hy' := Finset.mem_inter.mp hy
      refine ⟨⟨y, hy'.2⟩, ?_, rfl⟩
      apply (K.mem_neighborFinset x₀ ⟨y, hy'.2⟩).mpr
      simpa [K] using (Finset.mem_filter.mp hy'.1).2
  have hinter_le : (neighborFinsetOn G s (x₀ : V) ∩ D).card ≤ 1 := by
    rw [← degree_eq]
    exact hx₀deg
  have hx₀D : (x₀ : V) ∈ D := x₀.property
  have hx₀s : (x₀ : V) ∈ s := (Finset.mem_filter.mp hx₀D).1
  have hx₀three : (neighborFinsetOn G s (x₀ : V)).card = 3 :=
    (Finset.mem_filter.mp hx₀D).2
  obtain ⟨a, b, d, hab, had, hbd, hN⟩ :=
    Finset.card_eq_three.mp hx₀three
  have haN : a ∈ neighborFinsetOn G s (x₀ : V) := by rw [hN]; simp
  have hbN : b ∈ neighborFinsetOn G s (x₀ : V) := by rw [hN]; simp
  have hdN : d ∈ neighborFinsetOn G s (x₀ : V) := by rw [hN]; simp
  have no_two {u w : V} (huN : u ∈ neighborFinsetOn G s (x₀ : V))
      (hwN : w ∈ neighborFinsetOn G s (x₀ : V)) (huw : u ≠ w)
      (huD : u ∈ D) (hwD : w ∈ D) : False := by
    have hsub : ({u, w} : Finset V) ⊆ neighborFinsetOn G s (x₀ : V) ∩ D := by
      intro z hz
      have hz' : z = u ∨ z = w := by simpa using hz
      rcases hz' with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨huN, huD⟩
      · exact Finset.mem_inter.mpr ⟨hwN, hwD⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_pair huw] at hcard
    omega
  have hmin (z : V) (hzs : z ∈ s) : 3 ≤ (neighborFinsetOn G s z).card :=
    three_le_card_neighborFinsetOn_of_no_small_separation hs4 hnlow hntwo hzs
  have high_of_not_D (z : V) (hzs : z ∈ s) (hzD : z ∉ D) :
      4 ≤ (neighborFinsetOn G s z).card := by
    have hz3 := hmin z hzs
    have hzNe : (neighborFinsetOn G s z).card ≠ 3 := by
      intro hz
      exact hzD (Finset.mem_filter.mpr ⟨hzs, hz⟩)
    omega
  have has : a ∈ s := (Finset.mem_filter.mp haN).1
  have hbs : b ∈ s := (Finset.mem_filter.mp hbN).1
  have hds : d ∈ s := (Finset.mem_filter.mp hdN).1
  have hxa : G.Adj (x₀ : V) a := (Finset.mem_filter.mp haN).2
  have hxb : G.Adj (x₀ : V) b := (Finset.mem_filter.mp hbN).2
  have hxd : G.Adj (x₀ : V) d := (Finset.mem_filter.mp hdN).2
  by_cases haD : a ∈ D
  · have hbNot : b ∉ D := fun hbD ↦ no_two haN hbN hab haD hbD
    have hdNot : d ∉ D := fun hdD ↦ no_two haN hdN had haD hdD
    exact ⟨x₀, b, d, a, hx₀s, hbs, hds, has, hbd, hab.symm, had.symm,
      hxb, hxd, hxa, hx₀three, high_of_not_D b hbs hbNot,
      high_of_not_D d hds hdNot⟩
  · by_cases hbD : b ∈ D
    · have hdNot : d ∉ D := fun hdD ↦ no_two hbN hdN hbd hbD hdD
      exact ⟨x₀, a, d, b, hx₀s, has, hds, hbs, had, hab, hbd.symm,
        hxa, hxd, hxb, hx₀three, high_of_not_D a has haD,
        high_of_not_D d hds hdNot⟩
    · exact ⟨x₀, a, b, d, hx₀s, has, hbs, hds, hab, had, hbd,
        hxa, hxb, hxd, hx₀three, high_of_not_D a has haD,
        high_of_not_D b hbs hbD⟩

theorem edgeSetOn_ncard_erase_vertex
    {G : SimpleGraph V} {s : Finset V} {x : V} (hxs : x ∈ s) :
    (edgeSetOn G (s.erase x)).ncard + (neighborFinsetOn G s x).card =
      (edgeSetOn G s).ncard := by
  classical
  let T : Finset V := s.erase x
  let N : Finset V := neighborFinsetOn G s x
  let A : Set (Sym2 V) := edgeSetOn G T
  let f : N → Sym2 V := fun y ↦ s(x, (y : V))
  let R : Set (Sym2 V) := Set.range f
  have hf : Function.Injective f := by
    intro y z hyz
    change s(x, (y : V)) = s(x, (z : V)) at hyz
    rw [Sym2.eq_iff] at hyz
    rcases hyz with ⟨_, hyz⟩ | ⟨hxz, hyx⟩
    · exact Subtype.ext hyz
    · have hxy : G.Adj x (y : V) := (Finset.mem_filter.mp y.property).2
      exact (hxy.ne hyx.symm).elim
  have hdisj : Disjoint A R := by
    rw [Set.disjoint_left]
    intro e heA heR
    obtain ⟨y, rfl⟩ := heR
    change G.Adj x (y : V) ∧ x ∈ T ∧ (y : V) ∈ T at heA
    exact (Finset.mem_erase.mp heA.2.1).1 rfl
  have hpartition : A ∪ R = edgeSetOn G s := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
        constructor
        · intro he
          rcases he with heA | heR
          · change G.Adj u v ∧ u ∈ T ∧ v ∈ T at heA
            exact ⟨heA.1, (Finset.mem_erase.mp heA.2.1).2,
              (Finset.mem_erase.mp heA.2.2).2⟩
          · obtain ⟨y, hy⟩ := heR
            change s(x, (y : V)) = s(u, v) at hy
            rw [Sym2.eq_iff] at hy
            rcases hy with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
            · subst u
              subst v
              exact ⟨(Finset.mem_filter.mp y.property).2,
                hxs, (Finset.mem_filter.mp y.property).1⟩
            · subst v
              subst u
              exact ⟨(Finset.mem_filter.mp y.property).2.symm,
                (Finset.mem_filter.mp y.property).1, hxs⟩
        · rintro ⟨huv, hus, hvs⟩
          by_cases hux : u = x
          · subst u
            right
            let y : N := ⟨v, Finset.mem_filter.mpr ⟨hvs, huv⟩⟩
            exact ⟨y, rfl⟩
          · by_cases hvx : v = x
            · subst v
              right
              let y : N := ⟨u, Finset.mem_filter.mpr ⟨hus, huv.symm⟩⟩
              refine ⟨y, ?_⟩
              exact Sym2.eq_swap
            · left
              exact ⟨huv, Finset.mem_erase.mpr ⟨hux, hus⟩,
                Finset.mem_erase.mpr ⟨hvx, hvs⟩⟩
  have hRncard : R.ncard = N.card := by
    change (Set.range f).ncard = N.card
    rw [Set.ncard_range_of_injective hf, Nat.card_eq_fintype_card]
    simp
  have hcard : (edgeSetOn G s).ncard = A.ncard + R.ncard := by
    rw [← hpartition]
    exact Set.ncard_union_eq hdisj
  change A.ncard + N.card = (edgeSetOn G s).ncard
  rw [hcard, hRncard]

theorem edgeSetOn_ncard_sup_edge_deleteIncidenceSet
    {G : SimpleGraph V} {t : Finset V} {x x₁ x₂ : V}
    (hxt : x ∉ t) (hx₁t : x₁ ∈ t) (hx₂t : x₂ ∈ t) (hx₁ : x₁ ≠ x)
    (hx₂ : x₂ ≠ x) (hx₁x₂ : x₁ ≠ x₂) (hnadj : ¬G.Adj x₁ x₂) :
    (edgeSetOn (G.deleteIncidenceSet x ⊔ edge x₁ x₂) t).ncard =
      (edgeSetOn G t).ncard + 1 := by
  classical
  have heq : edgeSetOn (G.deleteIncidenceSet x ⊔ edge x₁ x₂) t =
      insert s(x₁, x₂) (edgeSetOn G t) := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
        change (((G.deleteIncidenceSet x ⊔ edge x₁ x₂).Adj u v ∧ u ∈ t ∧ v ∈ t) ↔
          (s(u, v) = s(x₁, x₂) ∨ (G.Adj u v ∧ u ∈ t ∧ v ∈ t)))
        constructor
        · rintro ⟨huv, hut, hvt⟩
          rw [sup_adj] at huv
          rcases huv with huv | huv
          · exact Or.inr ⟨(deleteIncidenceSet_adj.mp huv).1, hut, hvt⟩
          · left
            rcases (edge_adj (s := x₁) (t := x₂) u v).mp huv with ⟨horient, _⟩
            rcases horient with horient | horient
            · simpa [horient.1, horient.2]
            · rw [horient.1, horient.2]
              exact Sym2.eq_swap
        · intro huv
          rcases huv with huv | huv
          · rw [Sym2.eq_iff] at huv
            rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
            · subst u
              subst v
              refine ⟨?_, hx₁t, hx₂t⟩
              apply (sup_adj _ _ _ _).mpr
              exact Or.inr ((edge_adj (s := x₁) (t := x₂) x₁ x₂).mpr
                ⟨Or.inl ⟨rfl, rfl⟩, hx₁x₂⟩)
            · subst u
              subst v
              refine ⟨?_, hx₂t, hx₁t⟩
              apply (sup_adj _ _ _ _).mpr
              exact Or.inr ((edge_adj (s := x₁) (t := x₂) x₂ x₁).mpr
                ⟨Or.inr ⟨rfl, rfl⟩, hx₁x₂.symm⟩)
          · refine ⟨?_, huv.2.1, huv.2.2⟩
            apply (sup_adj _ _ _ _).mpr
            left
            apply deleteIncidenceSet_adj.mpr
            refine ⟨huv.1, ?_, ?_⟩
            · intro hux
              exact hxt (hux ▸ huv.2.1)
            · intro hvx
              exact hxt (hvx ▸ huv.2.2)
  rw [heq, Set.ncard_insert_of_notMem]
  intro hmem
  exact hnadj hmem.1

omit [Fintype V] in
theorem Walk.IsPath.isCycle_append_reverse_of_only_endpoints
    {G : SimpleGraph V} {u v : V} {p q : G.Walk u v}
    (hp : p.IsPath) (hq : q.IsPath) (huv : u ≠ v)
    (hcommon : ∀ z, z ∈ p.support → z ∈ q.support → z = u ∨ z = v)
    (hlength : 1 < p.length ∨ 1 < q.length) :
    (p.append q.reverse).IsCycle := by
  apply hp.isCycle_append hq.reverse
  · rw [List.disjoint_left]
    intro z hzp hzq
    have hzpFull : z ∈ p.support := List.mem_of_mem_tail hzp
    have hzqFull : z ∈ q.support := by simpa using List.mem_of_mem_tail hzq
    rcases hcommon z hzpFull hzqFull with rfl | rfl
    · have hn := hp.support_nodup
      rw [← Walk.cons_tail_support p] at hn
      exact (List.nodup_cons.mp hn).1 hzp
    · have hn := hq.reverse.support_nodup
      rw [← Walk.cons_tail_support q.reverse] at hn
      exact (List.nodup_cons.mp hn).1 hzq
  · simpa using hlength

omit [Fintype V] in
theorem Walk.IsCycle.mem_support_takeUntil_or_dropUntil
    {G : SimpleGraph V} {u x y : V} {c : G.Walk u u}
    (hc : c.IsCycle) (hx : x ∈ c.support) (hy : y ∈ c.support) :
    y ∈ (c.takeUntil x hx).support ∨ y ∈ (c.dropUntil x hx).support := by
  rw [← Walk.mem_support_append_iff, c.take_spec hx]
  exact hy

omit [Fintype V] in
theorem Walk.IsCycle.common_mem_takeUntil_dropUntil
    {G : SimpleGraph V} {u x y : V} {c : G.Walk u u}
    (hc : c.IsCycle) (hx : x ∈ c.support)
    (hytake : y ∈ (c.takeUntil x hx).support)
    (hydrop : y ∈ (c.dropUntil x hx).support) : y = u ∨ y = x := by
  by_contra h
  push Not at h
  have hytail : y ∈ (c.takeUntil x hx).support.tail := by
    rw [Walk.mem_support_iff] at hytake
    exact hytake.resolve_left h.1
  have hydtail : y ∈ (c.dropUntil x hx).support.tail := by
    rw [Walk.mem_support_iff] at hydrop
    exact hydrop.resolve_left h.2
  have hn := hc.support_nodup
  rw [← c.take_spec hx, Walk.tail_support_append, List.nodup_append'] at hn
  exact hn.2.2 hytail hydtail

theorem Walk.IsCycle.isPath_dropUntil_append_takeUntil
    {G : SimpleGraph V} {u x y : V} {c : G.Walk u u}
    (hc : c.IsCycle) (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxu : x ≠ u) (hyu : y ≠ u) (hxy : x ≠ y)
    (hidx : c.support.idxOf y ≤ c.support.idxOf x) :
    ((c.dropUntil x hx).append (c.takeUntil y hy)).IsPath := by
  have htakeX : (c.takeUntil x hx).IsPath := hc.isPath_takeUntil hx
  have hdropX : (c.dropUntil x hx).IsPath := by
    have hwhole : ((c.takeUntil x hx).append (c.dropUntil x hx)).IsCycle := by
      simpa only [c.take_spec hx] using hc
    exact hwhole.isPath_of_append_right (Walk.not_nil_of_ne hxu.symm)
  have htakeY : (c.takeUntil y hy).IsPath := hc.isPath_takeUntil hy
  have hxDropY : x ∈ (c.dropUntil y hy).support :=
    Walk.mem_support_dropUntil_of_idxOf_le c hy hx hidx
  have hxNotTakeY : x ∉ (c.takeUntil y hy).support := by
    intro hxTakeY
    rcases Walk.IsCycle.common_mem_takeUntil_dropUntil hc hy hxTakeY hxDropY with h | h
    · exact hxu h
    · exact hxy h
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append']
  refine ⟨hdropX.support_nodup, htakeY.support_nodup.tail, ?_⟩
  rw [List.disjoint_left]
  intro z hzDrop hzTakeTail
  have hzTake : z ∈ (c.takeUntil y hy).support := List.mem_of_mem_tail hzTakeTail
  have hzuNe : z ≠ u := by
    intro hzu
    have hn := htakeY.support_nodup
    rw [← Walk.cons_tail_support (c.takeUntil y hy)] at hn
    exact (List.nodup_cons.mp hn).1 (hzu ▸ hzTakeTail)
  have hzC : z ∈ c.support := c.support_dropUntil_subset_support hx hzDrop
  have hzDropX : z ∈ (c.dropUntil x hx).support := hzDrop
  rcases Walk.IsCycle.common_mem_takeUntil_dropUntil hc hx
      (Walk.mem_support_takeUntil_of_idxOf_le c hx hzC (by
        have hzy : c.support.idxOf z ≤ c.support.idxOf y := by
          by_contra h
          have hyz : c.support.idxOf y < c.support.idxOf z := by omega
          have hzDropY : z ∈ (c.dropUntil y hy).support :=
            Walk.mem_support_dropUntil_of_idxOf_le c hy hzC hyz.le
          rcases Walk.IsCycle.common_mem_takeUntil_dropUntil hc hy hzTake hzDropY with hzu | hzy'
          · exact hzuNe hzu
          · have hzEq : z = y := hzy'
            subst z
            omega
        exact hzy.trans hidx)) hzDropX with hzu | hzx
  · have hn := htakeY.support_nodup
    exact hzuNe hzu
  · exact hxNotTakeY (hzx ▸ hzTake)

theorem Walk.IsCycle.exists_attachment_arc_through_two
    {G : SimpleGraph V} {w r₁ r₂ r₃ a d : V} {C : G.Walk w w}
    (hC : C.IsCycle)
    (hr₁C : r₁ ∈ C.support) (hr₂C : r₂ ∈ C.support)
    (hr₃C : r₃ ∈ C.support) (haC : a ∈ C.support) (hdC : d ∈ C.support)
    (hr₁r₂ : r₁ ≠ r₂) (hr₁r₃ : r₁ ≠ r₃) (hr₂r₃ : r₂ ≠ r₃) :
    ∃ u v, ∃ p : G.Walk u v,
      u ∈ ({r₁, r₂, r₃} : Finset V) ∧
      v ∈ ({r₁, r₂, r₃} : Finset V) ∧ u ≠ v ∧ p.IsPath ∧
      a ∈ p.support ∧ d ∈ p.support ∧
      (∀ z ∈ p.support, z ∈ C.support) := by
  classical
  let R : G.Walk r₁ r₁ := C.rotate r₁ hr₁C
  have hR : R.IsCycle := hC.rotate hr₁C
  have hr₂R : r₂ ∈ R.support := by simpa [R] using hr₂C
  have hr₃R : r₃ ∈ R.support := by simpa [R] using hr₃C
  have haR : a ∈ R.support := by simpa [R] using haC
  have hdR : d ∈ R.support := by simpa [R] using hdC
  have hsubR (z : V) (hz : z ∈ R.support) : z ∈ C.support := by
    simpa [R] using hz
  have dropPath {x : V} (hxR : x ∈ R.support) (hxr₁ : x ≠ r₁) :
      (R.dropUntil x hxR).IsPath := by
    have hwhole : ((R.takeUntil x hxR).append (R.dropUntil x hxR)).IsCycle := by
      simpa only [R.take_spec hxR] using hR
    exact hwhole.isPath_of_append_right (Walk.not_nil_of_ne hxr₁.symm)
  have ordered (p q : V) (hpR : p ∈ R.support) (hqR : q ∈ R.support)
      (hpr₁ : p ≠ r₁) (hqr₁ : q ≠ r₁) (hpq : p ≠ q)
      (hpT : p ∈ ({r₁, r₂, r₃} : Finset V))
      (hqT : q ∈ ({r₁, r₂, r₃} : Finset V))
      (hpqIdx : R.support.idxOf p ≤ R.support.idxOf q) :
      ∃ u v, ∃ arc : G.Walk u v,
        u ∈ ({r₁, r₂, r₃} : Finset V) ∧
        v ∈ ({r₁, r₂, r₃} : Finset V) ∧ u ≠ v ∧ arc.IsPath ∧
        a ∈ arc.support ∧ d ∈ arc.support ∧
        (∀ z ∈ arc.support, z ∈ C.support) := by
    have takeArc (x : V) (hxR : x ∈ R.support) (hxr₁ : r₁ ≠ x)
        (hxT : x ∈ ({r₁, r₂, r₃} : Finset V))
        (haIdx : R.support.idxOf a ≤ R.support.idxOf x)
        (hdIdx : R.support.idxOf d ≤ R.support.idxOf x) :
        ∃ u v, ∃ arc : G.Walk u v,
          u ∈ ({r₁, r₂, r₃} : Finset V) ∧
          v ∈ ({r₁, r₂, r₃} : Finset V) ∧ u ≠ v ∧ arc.IsPath ∧
          a ∈ arc.support ∧ d ∈ arc.support ∧
          (∀ z ∈ arc.support, z ∈ C.support) := by
      refine ⟨r₁, x, R.takeUntil x hxR, by simp, hxT, hxr₁,
        hR.isPath_takeUntil hxR,
        Walk.mem_support_takeUntil_of_idxOf_le R hxR haR haIdx,
        Walk.mem_support_takeUntil_of_idxOf_le R hxR hdR hdIdx, ?_⟩
      intro z hz
      exact hsubR z (R.support_takeUntil_subset_support hxR hz)
    have dropArc (x : V) (hxR : x ∈ R.support) (hxr₁ : x ≠ r₁)
        (hxT : x ∈ ({r₁, r₂, r₃} : Finset V))
        (haIdx : R.support.idxOf x ≤ R.support.idxOf a)
        (hdIdx : R.support.idxOf x ≤ R.support.idxOf d) :
        ∃ u v, ∃ arc : G.Walk u v,
          u ∈ ({r₁, r₂, r₃} : Finset V) ∧
          v ∈ ({r₁, r₂, r₃} : Finset V) ∧ u ≠ v ∧ arc.IsPath ∧
          a ∈ arc.support ∧ d ∈ arc.support ∧
          (∀ z ∈ arc.support, z ∈ C.support) := by
      refine ⟨x, r₁, R.dropUntil x hxR, hxT, by simp, hxr₁,
        dropPath hxR hxr₁,
        Walk.mem_support_dropUntil_of_idxOf_le R hxR haR haIdx,
        Walk.mem_support_dropUntil_of_idxOf_le R hxR hdR hdIdx, ?_⟩
      intro z hz
      exact hsubR z (R.support_dropUntil_subset_support hxR hz)
    have middleMem {z : V} (hzR : z ∈ R.support)
        (hpz : R.support.idxOf p ≤ R.support.idxOf z)
        (hzq : R.support.idxOf z ≤ R.support.idxOf q) :
        z ∈ ((R.takeUntil q hqR).dropUntil p
          (Walk.mem_support_takeUntil_of_idxOf_le R hqR hpR hpqIdx)).support := by
      let Tq : G.Walk r₁ q := R.takeUntil q hqR
      have hpTq : p ∈ Tq.support :=
        Walk.mem_support_takeUntil_of_idxOf_le R hqR hpR hpqIdx
      have hzTq : z ∈ Tq.support :=
        Walk.mem_support_takeUntil_of_idxOf_le R hqR hzR hzq
      have hprefix := R.support_takeUntil_prefix_support hqR
      have hpIdx : Tq.support.idxOf p = R.support.idxOf p :=
        hprefix.idxOf_eq_of_mem hpTq
      have hzIdx : Tq.support.idxOf z = R.support.idxOf z :=
        hprefix.idxOf_eq_of_mem hzTq
      apply Walk.mem_support_dropUntil_of_idxOf_le Tq hpTq hzTq
      simpa [hpIdx, hzIdx] using hpz
    have middleArc
        (haLo : R.support.idxOf p ≤ R.support.idxOf a)
        (haHi : R.support.idxOf a ≤ R.support.idxOf q)
        (hdLo : R.support.idxOf p ≤ R.support.idxOf d)
        (hdHi : R.support.idxOf d ≤ R.support.idxOf q) :
        ∃ u v, ∃ arc : G.Walk u v,
          u ∈ ({r₁, r₂, r₃} : Finset V) ∧
          v ∈ ({r₁, r₂, r₃} : Finset V) ∧ u ≠ v ∧ arc.IsPath ∧
          a ∈ arc.support ∧ d ∈ arc.support ∧
          (∀ z ∈ arc.support, z ∈ C.support) := by
      let Tq : G.Walk r₁ q := R.takeUntil q hqR
      have hpTq : p ∈ Tq.support :=
        Walk.mem_support_takeUntil_of_idxOf_le R hqR hpR hpqIdx
      let M : G.Walk p q := Tq.dropUntil p hpTq
      have hM : M.IsPath := (hR.isPath_takeUntil hqR).dropUntil hpTq
      refine ⟨p, q, M, hpT, hqT, hpq, hM,
        middleMem haR haLo haHi, middleMem hdR hdLo hdHi, ?_⟩
      intro z hz
      have hzTq : z ∈ Tq.support := Tq.support_dropUntil_subset_support hpTq hz
      exact hsubR z (R.support_takeUntil_subset_support hqR hzTq)
    have wrappedMemLeft {z : V} (hzR : z ∈ R.support)
        (hz : R.support.idxOf q ≤ R.support.idxOf z) :
        z ∈ ((R.dropUntil q hqR).append (R.takeUntil p hpR)).support := by
      rw [Walk.mem_support_append_iff]
      exact Or.inl (Walk.mem_support_dropUntil_of_idxOf_le R hqR hzR hz)
    have wrappedMemRight {z : V} (hzR : z ∈ R.support)
        (hz : R.support.idxOf z ≤ R.support.idxOf p) :
        z ∈ ((R.dropUntil q hqR).append (R.takeUntil p hpR)).support := by
      rw [Walk.mem_support_append_iff]
      exact Or.inr (Walk.mem_support_takeUntil_of_idxOf_le R hpR hzR hz)
    have wrappedArc
        (haOuter : R.support.idxOf q ≤ R.support.idxOf a ∨
          R.support.idxOf a ≤ R.support.idxOf p)
        (hdOuter : R.support.idxOf q ≤ R.support.idxOf d ∨
          R.support.idxOf d ≤ R.support.idxOf p) :
        ∃ u v, ∃ arc : G.Walk u v,
          u ∈ ({r₁, r₂, r₃} : Finset V) ∧
          v ∈ ({r₁, r₂, r₃} : Finset V) ∧ u ≠ v ∧ arc.IsPath ∧
          a ∈ arc.support ∧ d ∈ arc.support ∧
          (∀ z ∈ arc.support, z ∈ C.support) := by
      let W : G.Walk q p := (R.dropUntil q hqR).append (R.takeUntil p hpR)
      have hW : W.IsPath :=
        Walk.IsCycle.isPath_dropUntil_append_takeUntil hR
          hqR hpR hqr₁ hpr₁ hpq.symm hpqIdx
      have haW : a ∈ W.support := by
        rcases haOuter with ha | ha
        · exact wrappedMemLeft haR ha
        · exact wrappedMemRight haR ha
      have hdW : d ∈ W.support := by
        rcases hdOuter with hd | hd
        · exact wrappedMemLeft hdR hd
        · exact wrappedMemRight hdR hd
      refine ⟨q, p, W, hqT, hpT, hpq.symm, hW, haW, hdW, ?_⟩
      intro z hz
      rw [Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · exact hsubR z (R.support_dropUntil_subset_support hqR hz)
      · exact hsubR z (R.support_takeUntil_subset_support hpR hz)
    by_cases haP : R.support.idxOf a ≤ R.support.idxOf p
    · by_cases hdP : R.support.idxOf d ≤ R.support.idxOf p
      · exact takeArc p hpR hpr₁.symm hpT haP hdP
      · have hpD : R.support.idxOf p ≤ R.support.idxOf d := by omega
        by_cases hdQ : R.support.idxOf d ≤ R.support.idxOf q
        · exact takeArc q hqR hqr₁.symm hqT
            (haP.trans hpqIdx) hdQ
        · exact wrappedArc (Or.inr haP) (Or.inl (by omega))
    · have hpA : R.support.idxOf p ≤ R.support.idxOf a := by omega
      by_cases haQ : R.support.idxOf a ≤ R.support.idxOf q
      · by_cases hdP : R.support.idxOf d ≤ R.support.idxOf p
        · exact takeArc q hqR hqr₁.symm hqT haQ
            (hdP.trans hpqIdx)
        · have hpD : R.support.idxOf p ≤ R.support.idxOf d := by omega
          by_cases hdQ : R.support.idxOf d ≤ R.support.idxOf q
          · exact middleArc hpA haQ hpD hdQ
          · exact dropArc p hpR hpr₁ hpT hpA (by omega)
      · have hqA : R.support.idxOf q ≤ R.support.idxOf a := by omega
        by_cases hdP : R.support.idxOf d ≤ R.support.idxOf p
        · exact wrappedArc (Or.inl hqA) (Or.inr hdP)
        · exact dropArc p hpR hpr₁ hpT hpA (by omega)
  by_cases h₂₃ : R.support.idxOf r₂ ≤ R.support.idxOf r₃
  · exact ordered r₂ r₃ hr₂R hr₃R hr₁r₂.symm hr₁r₃.symm hr₂r₃
      (by simp) (by simp) h₂₃
  · exact ordered r₃ r₂ hr₃R hr₂R hr₁r₃.symm hr₁r₂.symm hr₂r₃.symm
      (by simp) (by simp) (by omega)

omit [Fintype V] in
theorem hasThreeSpokeCycle_of_two_paths
    {G : SimpleGraph V} {u v x₀ x₁ x₂ x₃ : V}
    {p q : G.Walk u v}
    (hp : p.IsPath) (hq : q.IsPath) (huv : u ≠ v)
    (hcommon : ∀ z, z ∈ p.support → z ∈ q.support → z = u ∨ z = v)
    (hlength : 1 < p.length ∨ 1 < q.length)
    (hx₀p : x₀ ∉ p.support) (hx₀q : x₀ ∉ q.support)
    (hx₁q : x₁ ∈ q.support) (hx₂p : x₂ ∈ p.support)
    (hx₃p : x₃ ∈ p.support)
    (hx₁x₂ : x₁ ≠ x₂) (hx₁x₃ : x₁ ≠ x₃) (hx₂x₃ : x₂ ≠ x₃)
    (hx₀x₁ : G.Adj x₀ x₁) (hx₀x₂ : G.Adj x₀ x₂)
    (hx₀x₃ : G.Adj x₀ x₃) :
    HasThreeSpokeCycleTest G := by
  let D : G.Walk u u := p.append q.reverse
  have hD : D.IsCycle :=
    Walk.IsPath.isCycle_append_reverse_of_only_endpoints hp hq huv hcommon hlength
  refine ⟨u, x₀, D, hD, ?_, x₁, ?_, x₂, ?_, x₃, ?_,
    hx₁x₂, hx₁x₃, hx₂x₃, hx₀x₁, hx₀x₂, hx₀x₃⟩
  · intro hx₀D
    rw [Walk.mem_support_append_iff] at hx₀D
    exact hx₀D.elim hx₀p (fun h ↦ hx₀q (by simpa using h))
  · rw [Walk.mem_support_append_iff]
    exact Or.inr (by simpa using hx₁q)
  · rw [Walk.mem_support_append_iff]
    exact Or.inl hx₂p
  · rw [Walk.mem_support_append_iff]
    exact Or.inl hx₃p

theorem hasThreeSpokeCycle_of_cycle_and_three_fan
    {G : SimpleGraph V} {w x₀ x₁ x₂ x₃ y₁ y₂ z : V}
    {C : G.Walk w w} {P : G.Walk x₁ z}
    (hC : C.IsCycle)
    (hx₀C : x₀ ∉ C.support) (hx₁C : x₁ ∉ C.support)
    (hx₂C : x₂ ∈ C.support) (hx₃C : x₃ ∈ C.support)
    (hy₁C : y₁ ∈ C.support) (hy₂C : y₂ ∈ C.support)
    (hzC : z ∈ C.support)
    (hP : P.IsPath) (hx₀P : x₀ ∉ P.support)
    (hPC : ∀ a ∈ P.support, a ∈ C.support → a = z)
    (hy₁y₂ : y₁ ≠ y₂) (hy₁z : y₁ ≠ z) (hy₂z : y₂ ≠ z)
    (hx₁x₂ : x₁ ≠ x₂) (hx₁x₃ : x₁ ≠ x₃) (hx₂x₃ : x₂ ≠ x₃)
    (hx₀x₁ : G.Adj x₀ x₁) (hx₀x₂ : G.Adj x₀ x₂)
    (hx₀x₃ : G.Adj x₀ x₃) (hx₁y₁ : G.Adj x₁ y₁)
    (hx₁y₂ : G.Adj x₁ y₂) :
    HasThreeSpokeCycleTest G := by
  have hx₁y₁ne : x₁ ≠ y₁ := fun h ↦ hx₁C (h ▸ hy₁C)
  have hx₁y₂ne : x₁ ≠ y₂ := fun h ↦ hx₁C (h ▸ hy₂C)
  have hx₁zne : x₁ ≠ z := fun h ↦ hx₁C (h ▸ hzC)
  have hx₀y₁ : x₀ ≠ y₁ := fun h ↦ hx₀C (h ▸ hy₁C)
  have hx₀y₂ : x₀ ≠ y₂ := fun h ↦ hx₀C (h ▸ hy₂C)
  have hx₀z : x₀ ≠ z := fun h ↦ hx₀C (h ▸ hzC)
  have hy₁P : y₁ ∉ P.support := by
    intro h
    exact hy₁z (hPC y₁ h hy₁C)
  have hy₂P : y₂ ∉ P.support := by
    intro h
    exact hy₂z (hPC y₂ h hy₂C)
  have hPpos : 0 < P.length := by
    apply Nat.pos_of_ne_zero
    intro hlen
    exact hx₁zne (P.eq_of_length_eq_zero hlen)
  let q₁₂ : G.Walk y₁ y₂ :=
    Walk.cons hx₁y₁.symm (Walk.cons hx₁y₂ Walk.nil)
  have hq₁₂ : q₁₂.IsPath := by
    simp [q₁₂, Walk.isPath_def, hy₁y₂, hx₁y₁ne.symm, hx₁y₂ne]
  have hx₀q₁₂ : x₀ ∉ q₁₂.support := by
    simp [q₁₂, hx₀y₁, hx₀x₁.ne, hx₀y₂]
  have hx₁q₁₂ : x₁ ∈ q₁₂.support := by simp [q₁₂]
  have hq₁₂len : 1 < q₁₂.length := by simp [q₁₂]
  let q₁z : G.Walk y₁ z := Walk.cons hx₁y₁.symm P
  have hq₁z : q₁z.IsPath := hP.cons hy₁P
  have hx₀q₁z : x₀ ∉ q₁z.support := by
    simp [q₁z, hx₀y₁, hx₀P]
  have hx₁q₁z : x₁ ∈ q₁z.support := by simp [q₁z]
  have hq₁zlen : 1 < q₁z.length := by simp [q₁z]; omega
  let q₂z : G.Walk y₂ z := Walk.cons hx₁y₂.symm P
  have hq₂z : q₂z.IsPath := hP.cons hy₂P
  have hx₀q₂z : x₀ ∉ q₂z.support := by
    simp [q₂z, hx₀y₂, hx₀P]
  have hx₁q₂z : x₁ ∈ q₂z.support := by simp [q₂z]
  have hq₂zlen : 1 < q₂z.length := by simp [q₂z]; omega
  obtain ⟨u, v, p, hu, hv, huv, hp, hx₂p, hx₃p, hpC⟩ :=
    Walk.IsCycle.exists_attachment_arc_through_two hC
      hy₁C hy₂C hzC hx₂C hx₃C hy₁y₂ hy₁z hy₂z
  have hx₀p : x₀ ∉ p.support := fun h ↦ hx₀C (hpC x₀ h)
  have finish {q : G.Walk u v} (hq : q.IsPath)
      (hcommon : ∀ a, a ∈ p.support → a ∈ q.support → a = u ∨ a = v)
      (hx₀q : x₀ ∉ q.support) (hx₁q : x₁ ∈ q.support)
      (hlen : 1 < q.length) : HasThreeSpokeCycleTest G := by
    exact hasThreeSpokeCycle_of_two_paths hp hq huv hcommon (Or.inr hlen)
      hx₀p hx₀q hx₁q hx₂p hx₃p hx₁x₂ hx₁x₃ hx₂x₃
      hx₀x₁ hx₀x₂ hx₀x₃
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv
  all_goals subst u
  all_goals subst v
  · exact (huv rfl).elim
  · apply finish hq₁₂
    · intro a hap haq
      have ha : a = y₁ ∨ a = x₁ ∨ a = y₂ := by simpa [q₁₂] using haq
      rcases ha with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact (hx₁C (hpC _ hap)).elim
      · exact Or.inr rfl
    · exact hx₀q₁₂
    · exact hx₁q₁₂
    · exact hq₁₂len
  · apply finish hq₁z
    · intro a hap haq
      have ha : a = y₁ ∨ a ∈ P.support := by simpa [q₁z] using haq
      rcases ha with rfl | haP
      · exact Or.inl rfl
      · exact Or.inr (hPC a haP (hpC a hap))
    · exact hx₀q₁z
    · exact hx₁q₁z
    · exact hq₁zlen
  · apply finish hq₁₂.reverse
    · intro a hap haq
      have haq' : a ∈ q₁₂.support := by simpa using haq
      have ha : a = y₁ ∨ a = x₁ ∨ a = y₂ := by simpa [q₁₂] using haq'
      rcases ha with rfl | rfl | rfl
      · exact Or.inr rfl
      · exact (hx₁C (hpC _ hap)).elim
      · exact Or.inl rfl
    · simpa using hx₀q₁₂
    · simpa using hx₁q₁₂
    · simpa using hq₁₂len
  · exact (huv rfl).elim
  · apply finish hq₂z
    · intro a hap haq
      have ha : a = y₂ ∨ a ∈ P.support := by simpa [q₂z] using haq
      rcases ha with rfl | haP
      · exact Or.inl rfl
      · exact Or.inr (hPC a haP (hpC a hap))
    · exact hx₀q₂z
    · exact hx₁q₂z
    · exact hq₂zlen
  · apply finish hq₁z.reverse
    · intro a hap haq
      have haq' : a ∈ q₁z.support := by simpa using haq
      have ha : a = y₁ ∨ a ∈ P.support := by simpa [q₁z] using haq'
      rcases ha with rfl | haP
      · exact Or.inr rfl
      · exact Or.inl (hPC a haP (hpC a hap))
    · simpa using hx₀q₁z
    · simpa using hx₁q₁z
    · simpa using hq₁zlen
  · apply finish hq₂z.reverse
    · intro a hap haq
      have haq' : a ∈ q₂z.support := by simpa using haq
      have ha : a = y₂ ∨ a ∈ P.support := by simpa [q₂z] using haq'
      rcases ha with rfl | haP
      · exact Or.inr rfl
      · exact Or.inl (hPC a haP (hpC a hap))
    · simpa using hx₀q₂z
    · simpa using hx₁q₂z
    · simpa using hq₂zlen
  · exact (huv rfl).elim

theorem Walk.IsPath.end_not_mem_takeUntil
    {G : SimpleGraph V} {u v x : V} {p : G.Walk u v}
    (hp : p.IsPath) (hx : x ∈ p.support) (hxv : x ≠ v) :
    v ∉ (p.takeUntil x hx).support := by
  intro hvTake
  let L : G.Walk u x := p.takeUntil x hx
  let R : G.Walk x v := p.dropUntil x hx
  have hRnon : ¬R.Nil := Walk.not_nil_of_ne hxv
  have hwhole : (L.append R).IsPath := by
    simpa [L, R, p.take_spec hx] using hp
  have hdisj : L.support.Disjoint R.tail.support :=
    hwhole.disjoint_support_of_append hRnon
  have hvR : v ∈ R.support := Walk.end_mem_support R
  have hvx : v ≠ x := hxv.symm
  have hvTailList : v ∈ R.support.tail := by
    rw [Walk.mem_support_iff] at hvR
    exact hvR.resolve_left hvx
  have hvTail : v ∈ R.tail.support := by
    rw [R.support_tail_of_not_nil hRnon]
    exact hvTailList
  exact hdisj (by simpa [L] using hvTake) hvTail

theorem Walk.IsPath.start_not_mem_dropUntil
    {G : SimpleGraph V} {u v x : V} {p : G.Walk u v}
    (hp : p.IsPath) (hx : x ∈ p.support) (hxu : x ≠ u) :
    u ∉ (p.dropUntil x hx).support := by
  intro huDrop
  let L : G.Walk u x := p.takeUntil x hx
  let R : G.Walk x v := p.dropUntil x hx
  by_cases hRnon : ¬R.Nil
  · have hwhole : (L.append R).IsPath := by
      simpa [L, R, p.take_spec hx] using hp
    have hdisj : L.support.Disjoint R.tail.support :=
      hwhole.disjoint_support_of_append hRnon
    have huRtailList : u ∈ R.support.tail := by
      rw [Walk.mem_support_iff] at huDrop
      exact huDrop.resolve_left hxu.symm
    have huRtail : u ∈ R.tail.support := by
      rw [R.support_tail_of_not_nil hRnon]
      exact huRtailList
    exact hdisj (Walk.start_mem_support L) huRtail
  · have hRnil : R.Nil := not_not.mp hRnon
    have hxv : x = v := hRnil.eq
    subst v
    have huR : u ∈ R.support := by simpa [R] using huDrop
    have hux : u = x := by
      simpa [hRnil.eq_nil] using huR
    exact hxu hux.symm

omit [Fintype V] in
theorem Walk.IsPath.one_lt_length_of_mem_support_ne_ends
    {G : SimpleGraph V} {u v x : V} {p : G.Walk u v}
    (hp : p.IsPath) (hx : x ∈ p.support) (hxu : x ≠ u) (hxv : x ≠ v) :
    1 < p.length := by
  let L : G.Walk u x := p.takeUntil x hx
  let R : G.Walk x v := p.dropUntil x hx
  have hLpos : 0 < L.length := by
    apply Nat.pos_of_ne_zero
    intro h
    exact hxu (L.eq_of_length_eq_zero h).symm
  have hRpos : 0 < R.length := by
    apply Nat.pos_of_ne_zero
    intro h
    exact hxv (R.eq_of_length_eq_zero h)
  have hlen : L.length + R.length = p.length := by
    rw [← Walk.length_append, p.take_spec hx]
  omega

omit [Fintype V] in
theorem Walk.IsPath.append_of_only_join
    {G : SimpleGraph V} {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (hp : p.IsPath) (hq : q.IsPath)
    (hcommon : ∀ z, z ∈ p.support → z ∈ q.support → z = v) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append']
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  rw [List.disjoint_left]
  intro z hzp hzqTail
  have hzq : z ∈ q.support := List.mem_of_mem_tail hzqTail
  have hzv : z = v := hcommon z hzp hzq
  subst z
  have hn := hq.support_nodup
  rw [← Walk.cons_tail_support q] at hn
  exact (List.nodup_cons.mp hn).1 hzqTail

theorem hasThreeSpokeCycle_of_ear_arc
    {G : SimpleGraph V} {r t x₀ x₁ x₂ x₃ y₁ y₂ : V}
    {C : List V} {q : G.Walk r t} {p : G.Walk r x₂}
    (hp : p.IsPath) (hpC : ∀ a ∈ p.support, a ∈ C)
    (hy₁p : y₁ ∈ p.support) (hy₂p : y₂ ∈ p.support)
    (hq : q.IsPath) (hx₃q : x₃ ∈ q.support)
    (hrC : r ∈ C) (htC : t ∈ C) (hx₂C : x₂ ∈ C)
    (hx₀C : x₀ ∉ C) (hx₁C : x₁ ∉ C) (hx₃C : x₃ ∉ C)
    (hqC : ∀ a ∈ q.support, a ∈ C → a = r ∨ a = t)
    (hx₀q : x₀ ∉ q.support) (hx₁q : x₁ ∉ q.support)
    (hrt : r ≠ t) (hx₂r : x₂ ≠ r) (hx₂t : x₂ ≠ t)
    (hy₁y₂ : y₁ ≠ y₂)
    (hx₀x₁ : G.Adj x₀ x₁) (hx₀x₂ : G.Adj x₀ x₂)
    (hx₀x₃ : G.Adj x₀ x₃) (hx₁y₁ : G.Adj x₁ y₁)
    (hx₁y₂ : G.Adj x₁ y₂) :
    HasThreeSpokeCycleTest G := by
  have hx₃r : x₃ ≠ r := fun h ↦ hx₃C (h ▸ hrC)
  have hx₃t : x₃ ≠ t := fun h ↦ hx₃C (h ▸ htC)
  have hx₁x₂ : x₁ ≠ x₂ := fun h ↦ hx₁C (h ▸ hx₂C)
  have hx₀y₁ : x₀ ≠ y₁ := fun h ↦ hx₀C (h ▸ hpC y₁ hy₁p)
  have hx₀y₂ : x₀ ≠ y₂ := fun h ↦ hx₀C (h ▸ hpC y₂ hy₂p)
  let L : G.Walk r x₃ := q.takeUntil x₃ hx₃q
  have hL : L.IsPath := hq.takeUntil hx₃q
  have hx₀L : x₀ ∉ L.support := by
    intro h
    exact hx₀q (q.support_takeUntil_subset_support hx₃q (by simpa [L] using h))
  have hx₁L : x₁ ∉ L.support := by
    intro h
    exact hx₁q (q.support_takeUntil_subset_support hx₃q (by simpa [L] using h))
  have hx₂L : x₂ ∉ L.support := by
    intro h
    have hx₂q : x₂ ∈ q.support :=
      q.support_takeUntil_subset_support hx₃q (by simpa [L] using h)
    rcases hqC x₂ hx₂q hx₂C with h | h
    · exact hx₂r h
    · exact hx₂t h
  have htL : t ∉ L.support := by
    exact Walk.IsPath.end_not_mem_takeUntil hq hx₃q hx₃t
  let Q : G.Walk r x₂ :=
    (L.concat hx₀x₃.symm).concat hx₀x₂
  have hLx₀ : (L.concat hx₀x₃.symm).IsPath := hL.concat hx₀L hx₀x₃.symm
  have hx₂Lx₀ : x₂ ∉ (L.concat hx₀x₃.symm).support := by
    simp [hx₂L, hx₀x₂.ne.symm]
  have hQ : Q.IsPath := hLx₀.concat hx₂Lx₀ hx₀x₂
  have hx₁Q : x₁ ∉ Q.support := by
    simp [Q, hx₁L, hx₀x₁.ne.symm, hx₁x₂]
  have hx₀Q : x₀ ∈ Q.support := by simp [Q]
  have hQlen : 1 < Q.length := by simp [Q]
  have hcommon : ∀ a, a ∈ p.support → a ∈ Q.support → a = r ∨ a = x₂ := by
    intro a hap haQ
    have haC := hpC a hap
    have haCases : a ∈ L.support ∨ a = x₀ ∨ a = x₂ := by
      simpa [Q] using haQ
    rcases haCases with haL | rfl | rfl
    · have haq : a ∈ q.support :=
        q.support_takeUntil_subset_support hx₃q (by simpa [L] using haL)
      rcases hqC a haq haC with rfl | rfl
      · exact Or.inl rfl
      · exact (htL haL).elim
    · exact (hx₀C haC).elim
    · exact Or.inr rfl
  exact hasThreeSpokeCycle_of_two_paths hp hQ hx₂r.symm hcommon
    (Or.inr hQlen) (fun h ↦ hx₁C (hpC x₁ h)) hx₁Q hx₀Q
    hy₁p hy₂p hx₀y₁ hx₀y₂ hy₁y₂ hx₀x₁.symm hx₁y₁ hx₁y₂

theorem exists_cycle_of_ear_and_arc
    {G : SimpleGraph V} {r t x₀ x₁ x₂ x₃ y₁ y₂ : V}
    {C : List V} {q p : G.Walk r t}
    (hp : p.IsPath) (hpC : ∀ a ∈ p.support, a ∈ C)
    (hx₂p : x₂ ∈ p.support) (hy₁p : y₁ ∈ p.support)
    (hy₂p : y₂ ∈ p.support)
    (hq : q.IsPath) (hx₃q : x₃ ∈ q.support)
    (hrC : r ∈ C) (htC : t ∈ C)
    (hx₀C : x₀ ∉ C) (hx₁C : x₁ ∉ C) (hx₃C : x₃ ∉ C)
    (hqC : ∀ a ∈ q.support, a ∈ C → a = r ∨ a = t)
    (hx₀q : x₀ ∉ q.support) (hx₁q : x₁ ∉ q.support)
    (hrt : r ≠ t) :
    ∃ d, ∃ D : G.Walk d d, D.IsCycle ∧ x₀ ∉ D.support ∧
      x₁ ∉ D.support ∧ x₂ ∈ D.support ∧ x₃ ∈ D.support ∧
      y₁ ∈ D.support ∧ y₂ ∈ D.support := by
  have hx₃r : x₃ ≠ r := fun h ↦ hx₃C (h ▸ hrC)
  have hx₃t : x₃ ≠ t := fun h ↦ hx₃C (h ▸ htC)
  have hcommon : ∀ a, a ∈ p.support → a ∈ q.support → a = r ∨ a = t := by
    intro a hap haq
    exact hqC a haq (hpC a hap)
  let D : G.Walk r r := p.append q.reverse
  have hD : D.IsCycle :=
    Walk.IsPath.isCycle_append_reverse_of_only_endpoints hp hq hrt hcommon
      (Or.inr (Walk.IsPath.one_lt_length_of_mem_support_ne_ends
        hq hx₃q hx₃r hx₃t))
  refine ⟨r, D, hD, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [Walk.mem_support_append_iff] at h
    exact h.elim (fun h ↦ hx₀C (hpC x₀ h))
      (fun h ↦ hx₀q (by simpa using h))
  · intro h
    rw [Walk.mem_support_append_iff] at h
    exact h.elim (fun h ↦ hx₁C (hpC x₁ h))
      (fun h ↦ hx₁q (by simpa using h))
  · rw [Walk.mem_support_append_iff]
    exact Or.inl hx₂p
  · rw [Walk.mem_support_append_iff]
    exact Or.inr (by simpa using hx₃q)
  · rw [Walk.mem_support_append_iff]
    exact Or.inl hy₁p
  · rw [Walk.mem_support_append_iff]
    exact Or.inl hy₂p

theorem hasThreeSpokeCycle_of_ear_and_opposite_arcs
    {G : SimpleGraph V} {r t x₀ x₁ x₂ x₃ y₁ y₂ : V}
    {C : List V} {q A B : G.Walk r t}
    (hA : A.IsPath) (hB : B.IsPath)
    (hAC : ∀ a ∈ A.support, a ∈ C)
    (hBC : ∀ a ∈ B.support, a ∈ C)
    (hAB : ∀ a, a ∈ A.support → a ∈ B.support → a = r ∨ a = t)
    (hy₁A : y₁ ∈ A.support) (hy₂A : y₂ ∈ A.support)
    (hx₂B : x₂ ∈ B.support)
    (hq : q.IsPath) (hx₃q : x₃ ∈ q.support)
    (hrC : r ∈ C) (htC : t ∈ C)
    (hx₀C : x₀ ∉ C) (hx₁C : x₁ ∉ C) (hx₃C : x₃ ∉ C)
    (hqC : ∀ a ∈ q.support, a ∈ C → a = r ∨ a = t)
    (hx₀q : x₀ ∉ q.support) (hx₁q : x₁ ∉ q.support)
    (hrt : r ≠ t) (hx₂r : x₂ ≠ r) (hx₂t : x₂ ≠ t)
    (hx₁x₃ : x₁ ≠ x₃) (hy₁y₂ : y₁ ≠ y₂)
    (hx₀x₁ : G.Adj x₀ x₁) (hx₀x₂ : G.Adj x₀ x₂)
    (hx₀x₃ : G.Adj x₀ x₃) (hx₁y₁ : G.Adj x₁ y₁)
    (hx₁y₂ : G.Adj x₁ y₂) :
    HasThreeSpokeCycleTest G := by
  have hx₃t : x₃ ≠ t := fun h ↦ hx₃C (h ▸ htC)
  let L : G.Walk r x₃ := q.takeUntil x₃ hx₃q
  have hL : L.IsPath := hq.takeUntil hx₃q
  have htL : t ∉ L.support :=
    Walk.IsPath.end_not_mem_takeUntil hq hx₃q hx₃t
  have hx₀L : x₀ ∉ L.support := by
    intro h
    exact hx₀q (q.support_takeUntil_subset_support hx₃q (by simpa [L] using h))
  have hx₁L : x₁ ∉ L.support := by
    intro h
    exact hx₁q (q.support_takeUntil_subset_support hx₃q (by simpa [L] using h))
  let S : G.Walk x₂ t := B.dropUntil x₂ hx₂B
  have hS : S.IsPath := hB.dropUntil hx₂B
  have hrS : r ∉ S.support :=
    Walk.IsPath.start_not_mem_dropUntil hB hx₂B hx₂r
  have hSC : ∀ a ∈ S.support, a ∈ C := by
    intro a ha
    exact hBC a (B.support_dropUntil_subset_support hx₂B (by simpa [S] using ha))
  have hx₀S : x₀ ∉ S.support := fun h ↦ hx₀C (hSC x₀ h)
  have hx₁S : x₁ ∉ S.support := fun h ↦ hx₁C (hSC x₁ h)
  have hx₃S : x₃ ∉ S.support := fun h ↦ hx₃C (hSC x₃ h)
  let S₀ : G.Walk x₀ t := Walk.cons hx₀x₂ S
  have hS₀ : S₀.IsPath := hS.cons hx₀S
  let S₃ : G.Walk x₃ t := Walk.cons hx₀x₃.symm S₀
  have hx₃S₀ : x₃ ∉ S₀.support := by
    simp [S₀, hx₀x₃.ne.symm, hx₃S]
  have hS₃ : S₃.IsPath := hS₀.cons hx₃S₀
  let Q : G.Walk r t := L.append S₃
  have hLS₃ : ∀ a, a ∈ L.support → a ∈ S₃.support → a = x₃ := by
    intro a haL haS₃
    have haq : a ∈ q.support :=
      q.support_takeUntil_subset_support hx₃q (by simpa [L] using haL)
    have haCases : a = x₃ ∨ a = x₀ ∨ a ∈ S.support := by
      simpa [S₃, S₀] using haS₃
    rcases haCases with h | rfl | haS
    · exact h
    · exact (hx₀q haq).elim
    · have haC := hSC a haS
      rcases hqC a haq haC with rfl | rfl
      · exact (hrS haS).elim
      · exact (htL haL).elim
  have hQ : Q.IsPath :=
    Walk.IsPath.append_of_only_join hL hS₃ hLS₃
  have hx₁Q : x₁ ∉ Q.support := by
    intro h
    rw [Walk.mem_support_append_iff] at h
    rcases h with h | h
    · exact hx₁L h
    · have h' : x₁ = x₃ ∨ x₁ = x₀ ∨ x₁ ∈ S.support := by
        simpa [S₃, S₀] using h
      rcases h' with h' | h' | h'
      · exact hx₁x₃ h'
      · exact hx₀x₁.ne h'.symm
      · exact hx₁S h'
  have hx₀Q : x₀ ∈ Q.support := by
    rw [Walk.mem_support_append_iff]
    right
    simp [S₃, S₀]
  have hQlen : 1 < Q.length := by simp [Q, S₃, S₀]; omega
  have hAQ : ∀ a, a ∈ A.support → a ∈ Q.support → a = r ∨ a = t := by
    intro a haA haQ
    have haC := hAC a haA
    rw [Walk.mem_support_append_iff] at haQ
    rcases haQ with haL | haS₃
    · have haq : a ∈ q.support :=
        q.support_takeUntil_subset_support hx₃q (by simpa [L] using haL)
      exact hqC a haq haC
    · have haCases : a = x₃ ∨ a = x₀ ∨ a ∈ S.support := by
        simpa [S₃, S₀] using haS₃
      rcases haCases with rfl | rfl | haS
      · exact (hx₃C haC).elim
      · exact (hx₀C haC).elim
      · have haB : a ∈ B.support :=
          B.support_dropUntil_subset_support hx₂B (by simpa [S] using haS)
        exact hAB a haA haB
  have hx₀y₁ : x₀ ≠ y₁ := fun h ↦ hx₀C (h ▸ hAC y₁ hy₁A)
  have hx₀y₂ : x₀ ≠ y₂ := fun h ↦ hx₀C (h ▸ hAC y₂ hy₂A)
  exact hasThreeSpokeCycle_of_two_paths hA hQ hrt hAQ (Or.inr hQlen)
    (fun h ↦ hx₁C (hAC x₁ h)) hx₁Q hx₀Q hy₁A hy₂A
    hx₀y₁ hx₀y₂ hy₁y₂ hx₀x₁.symm hx₁y₁ hx₁y₂

theorem exists_endpoint_arc_through_split
    {G : SimpleGraph V} {r t x₂ a d : V} {C : List V}
    {A B : G.Walk r t}
    (hA : A.IsPath) (hB : B.IsPath)
    (hAC : ∀ z ∈ A.support, z ∈ C)
    (hBC : ∀ z ∈ B.support, z ∈ C)
    (hAB : ∀ z, z ∈ A.support → z ∈ B.support → z = r ∨ z = t)
    (hx₂A : x₂ ∈ A.support) (haA : a ∈ A.support)
    (hdB : d ∈ B.support) (hx₂r : x₂ ≠ r) (hx₂t : x₂ ≠ t) :
    (∃ P : G.Walk t x₂, P.IsPath ∧ a ∈ P.support ∧ d ∈ P.support ∧
      ∀ z ∈ P.support, z ∈ C) ∨
    (∃ P : G.Walk r x₂, P.IsPath ∧ a ∈ P.support ∧ d ∈ P.support ∧
      ∀ z ∈ P.support, z ∈ C) := by
  have haSplit : a ∈ (A.takeUntil x₂ hx₂A).support ∨
      a ∈ (A.dropUntil x₂ hx₂A).support := by
    rw [← Walk.mem_support_append_iff, A.take_spec hx₂A]
    exact haA
  rcases haSplit with haTake | haDrop
  · let T : G.Walk r x₂ := A.takeUntil x₂ hx₂A
    have hT : T.IsPath := hA.takeUntil hx₂A
    have htT : t ∉ T.support :=
      Walk.IsPath.end_not_mem_takeUntil hA hx₂A hx₂t
    let P : G.Walk t x₂ := B.reverse.append T
    have hjoin : ∀ z, z ∈ B.reverse.support → z ∈ T.support → z = r := by
      intro z hzB hzT
      have hzB' : z ∈ B.support := by simpa using hzB
      have hzA : z ∈ A.support :=
        A.support_takeUntil_subset_support hx₂A (by simpa [T] using hzT)
      rcases hAB z hzA hzB' with h | h
      · exact h
      · exact (htT (h ▸ hzT)).elim
    have hP : P.IsPath :=
      Walk.IsPath.append_of_only_join hB.reverse hT hjoin
    refine Or.inl ⟨P, hP, ?_, ?_, ?_⟩
    · rw [Walk.mem_support_append_iff]
      exact Or.inr (by simpa [T] using haTake)
    · rw [Walk.mem_support_append_iff]
      exact Or.inl (by simpa using hdB)
    · intro z hz
      rw [Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · exact hBC z (by simpa using hz)
      · exact hAC z (A.support_takeUntil_subset_support hx₂A
          (by simpa [T] using hz))
  · let D : G.Walk x₂ t := A.dropUntil x₂ hx₂A
    have hD : D.IsPath := hA.dropUntil hx₂A
    have hrD : r ∉ D.support :=
      Walk.IsPath.start_not_mem_dropUntil hA hx₂A hx₂r
    let P : G.Walk r x₂ := B.append D.reverse
    have hjoin : ∀ z, z ∈ B.support → z ∈ D.reverse.support → z = t := by
      intro z hzB hzD
      have hzD' : z ∈ D.support := by simpa using hzD
      have hzA : z ∈ A.support :=
        A.support_dropUntil_subset_support hx₂A (by simpa [D] using hzD')
      rcases hAB z hzA hzB with h | h
      · exact (hrD (h ▸ hzD')).elim
      · exact h
    have hP : P.IsPath :=
      Walk.IsPath.append_of_only_join hB hD.reverse hjoin
    refine Or.inr ⟨P, hP, ?_, ?_, ?_⟩
    · rw [Walk.mem_support_append_iff]
      exact Or.inr (by simpa [D] using haDrop)
    · rw [Walk.mem_support_append_iff]
      exact Or.inl hdB
    · intro z hz
      rw [Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · exact hBC z hz
      · have hzD : z ∈ D.support := by simpa using hz
        exact hAC z (A.support_dropUntil_subset_support hx₂A
          (by simpa [D] using hzD))

theorem Walk.IsCycle.exists_two_arcs
    {G : SimpleGraph V} {w r t : V} {C : G.Walk w w}
    (hC : C.IsCycle) (hrC : r ∈ C.support) (htC : t ∈ C.support)
    (hrt : r ≠ t) :
    ∃ A B : G.Walk r t, A.IsPath ∧ B.IsPath ∧
      (∀ z ∈ A.support, z ∈ C.support) ∧
      (∀ z ∈ B.support, z ∈ C.support) ∧
      (∀ z, z ∈ A.support → z ∈ B.support → z = r ∨ z = t) ∧
      (∀ z ∈ C.support, z ∈ A.support ∨ z ∈ B.support) := by
  let R : G.Walk r r := C.rotate r hrC
  have hR : R.IsCycle := Walk.IsCycle.rotate hrC hC
  have htR : t ∈ R.support := by simpa [R] using htC
  let A : G.Walk r t := R.takeUntil t htR
  let D : G.Walk t r := R.dropUntil t htR
  let B : G.Walk r t := D.reverse
  have hA : A.IsPath := hR.isPath_takeUntil htR
  have hwhole : (A.append D).IsCycle := by
    simpa [A, D, R.take_spec htR] using hR
  have hAnil : ¬A.Nil := Walk.not_nil_of_ne hrt
  have hD : D.IsPath := hwhole.isPath_of_append_right hAnil
  have hB : B.IsPath := hD.reverse
  refine ⟨A, B, hA, hB, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hzR : z ∈ R.support :=
      R.support_takeUntil_subset_support htR (by simpa [A] using hz)
    simpa [R] using hzR
  · intro z hz
    have hzD : z ∈ D.support := by simpa [B] using hz
    have hzR : z ∈ R.support :=
      R.support_dropUntil_subset_support htR (by simpa [D] using hzD)
    simpa [R] using hzR
  · intro z hzA hzB
    have hzTake : z ∈ (R.takeUntil t htR).support := by simpa [A] using hzA
    have hzDrop : z ∈ (R.dropUntil t htR).support := by
      have : z ∈ D.support := by simpa [B] using hzB
      simpa [D] using this
    exact Walk.IsCycle.common_mem_takeUntil_dropUntil hR htR hzTake hzDrop
  · intro z hzC
    have hzR : z ∈ R.support := by simpa [R] using hzC
    rcases Walk.IsCycle.mem_support_takeUntil_or_dropUntil hR htR hzR with h | h
    · exact Or.inl (by simpa [A] using h)
    · exact Or.inr (by simpa [B, D] using h)

theorem hasThreeSpokeCycle_of_ear_and_split_arcs_at_start
    {G : SimpleGraph V} {r t x₀ x₁ x₃ y₁ y₂ : V}
    {C : List V} {q A B : G.Walk r t}
    (hA : A.IsPath) (hB : B.IsPath)
    (hAC : ∀ a ∈ A.support, a ∈ C)
    (hBC : ∀ a ∈ B.support, a ∈ C)
    (hAB : ∀ a, a ∈ A.support → a ∈ B.support → a = r ∨ a = t)
    (hy₁A : y₁ ∈ A.support) (hy₂B : y₂ ∈ B.support)
    (hy₂notA : y₂ ∉ A.support)
    (hq : q.IsPath) (hx₃q : x₃ ∈ q.support)
    (hrC : r ∈ C) (htC : t ∈ C)
    (hx₀C : x₀ ∉ C) (hx₁C : x₁ ∉ C) (hx₃C : x₃ ∉ C)
    (hqC : ∀ a ∈ q.support, a ∈ C → a = r ∨ a = t)
    (hx₀q : x₀ ∉ q.support) (hx₁q : x₁ ∉ q.support)
    (hrt : r ≠ t) (hry₁ : r ≠ y₁) (hx₁x₃ : x₁ ≠ x₃)
    (hx₀x₁ : G.Adj x₀ x₁) (hx₀r : G.Adj x₀ r)
    (hx₀x₃ : G.Adj x₀ x₃) (hx₁y₁ : G.Adj x₁ y₁)
    (hx₁y₂ : G.Adj x₁ y₂) :
    HasThreeSpokeCycleTest G := by
  have hy₂t : y₂ ≠ t := by
    intro h
    exact hy₂notA (h ▸ Walk.end_mem_support A)
  have hy₁r : y₁ ≠ r := hry₁.symm
  let T : G.Walk r y₂ := B.takeUntil y₂ hy₂B
  have hT : T.IsPath := hB.takeUntil hy₂B
  have htT : t ∉ T.support :=
    Walk.IsPath.end_not_mem_takeUntil hB hy₂B hy₂t
  let U : G.Walk y₁ t := A.dropUntil y₁ hy₁A
  have hU : U.IsPath := hA.dropUntil hy₁A
  have hrU : r ∉ U.support :=
    Walk.IsPath.start_not_mem_dropUntil hA hy₁A hy₁r
  have hUC : ∀ a ∈ U.support, a ∈ C := by
    intro a ha
    exact hAC a (A.support_dropUntil_subset_support hy₁A (by simpa [U] using ha))
  have hx₁U : x₁ ∉ U.support := fun h ↦ hx₁C (hUC x₁ h)
  have hy₂U : y₂ ∉ U.support := by
    intro h
    exact hy₂notA (A.support_dropUntil_subset_support hy₁A (by simpa [U] using h))
  let E : G.Walk y₂ t :=
    Walk.cons hx₁y₂.symm (Walk.cons hx₁y₁ U)
  have hinner : (Walk.cons hx₁y₁ U).IsPath := hU.cons hx₁U
  have hy₂inner : y₂ ∉ (Walk.cons hx₁y₁ U).support := by
    simp [hx₁y₂.ne.symm, hy₂U]
  have hE : E.IsPath := hinner.cons hy₂inner
  let Q : G.Walk r t := T.append E
  have hTE : ∀ a, a ∈ T.support → a ∈ E.support → a = y₂ := by
    intro a haT haE
    have haB : a ∈ B.support :=
      B.support_takeUntil_subset_support hy₂B (by simpa [T] using haT)
    have haCases : a = y₂ ∨ a = x₁ ∨ a ∈ U.support := by
      simpa [E] using haE
    rcases haCases with h | hx₁eq | haU
    · exact h
    · subst a
      exact (hx₁C (hBC x₁ haB)).elim
    · have haA : a ∈ A.support :=
        A.support_dropUntil_subset_support hy₁A (by simpa [U] using haU)
      rcases hAB a haA haB with rfl | rfl
      · exact (hrU haU).elim
      · exact (htT haT).elim
  have hQ : Q.IsPath := Walk.IsPath.append_of_only_join hT hE hTE
  have hx₁Q : x₁ ∈ Q.support := by
    rw [Walk.mem_support_append_iff]
    right
    simp [E]
  have hx₀Q : x₀ ∉ Q.support := by
    intro h
    rw [Walk.mem_support_append_iff] at h
    rcases h with h | h
    · have hBmem : x₀ ∈ B.support :=
        B.support_takeUntil_subset_support hy₂B (by simpa [T] using h)
      exact hx₀C (hBC x₀ hBmem)
    · have hCases : x₀ = y₂ ∨ x₀ = x₁ ∨ x₀ ∈ U.support := by
        simpa [E] using h
      rcases hCases with h | h | h
      · subst x₀
        exact hx₀C (hBC y₂ hy₂B)
      · exact hx₀x₁.ne h
      · exact hx₀C (hUC x₀ h)
  have hqQ : ∀ a, a ∈ q.support → a ∈ Q.support → a = r ∨ a = t := by
    intro a haq haQ
    rw [Walk.mem_support_append_iff] at haQ
    rcases haQ with haT | haE
    · have haC : a ∈ C := hBC a
        (B.support_takeUntil_subset_support hy₂B (by simpa [T] using haT))
      exact hqC a haq haC
    · have haCases : a = y₂ ∨ a = x₁ ∨ a ∈ U.support := by
        simpa [E] using haE
      rcases haCases with h | h | haU
      · subst a
        exact hqC y₂ haq (hBC y₂ hy₂B)
      · subst a
        exact (hx₁q haq).elim
      · exact hqC a haq (hUC a haU)
  have hQlen : 1 < Q.length := by simp [Q, E]; omega
  have hrq : r ∈ q.support := Walk.start_mem_support q
  exact hasThreeSpokeCycle_of_two_paths hq hQ hrt hqQ (Or.inr hQlen)
    hx₀q hx₀Q hx₁Q hrq hx₃q
    (fun h ↦ hx₁C (h ▸ hrC)) hx₁x₃ (fun h ↦ hx₃C (h ▸ hrC))
    hx₀x₁ hx₀r hx₀x₃

theorem hasThreeSpokeCycle_or_exists_four_vertex_cycle_of_ear
    {G : SimpleGraph V} {w z₁ z₂ x₀ x₁ x₂ x₃ y₁ y₂ : V}
    {C : G.Walk w w} {q : G.Walk z₁ z₂}
    (hC : C.IsCycle)
    (hx₀C : x₀ ∉ C.support) (hx₁C : x₁ ∉ C.support)
    (hx₂C : x₂ ∈ C.support) (hy₁C : y₁ ∈ C.support)
    (hy₂C : y₂ ∈ C.support)
    (hq : q.IsPath) (hx₀q : x₀ ∉ q.support) (hx₁q : x₁ ∉ q.support)
    (hx₃q : x₃ ∈ q.support)
    (hz₁C : z₁ ∈ C.support) (hz₂C : z₂ ∈ C.support)
    (hz₁z₂ : z₁ ≠ z₂)
    (hqC : ∀ a ∈ q.support, a ∈ C.support → a = z₁ ∨ a = z₂)
    (hx₂y₁ : x₂ ≠ y₁) (hx₂y₂ : x₂ ≠ y₂) (hy₁y₂ : y₁ ≠ y₂)
    (hx₁x₃ : x₁ ≠ x₃)
    (hx₀x₁ : G.Adj x₀ x₁) (hx₀x₂ : G.Adj x₀ x₂)
    (hx₀x₃ : G.Adj x₀ x₃) (hx₁y₁ : G.Adj x₁ y₁)
    (hx₁y₂ : G.Adj x₁ y₂) :
    HasThreeSpokeCycleTest G ∨
      ∃ d, ∃ D : G.Walk d d, D.IsCycle ∧ x₀ ∉ D.support ∧
        x₁ ∉ D.support ∧ x₂ ∈ D.support ∧ x₃ ∈ D.support ∧
        y₁ ∈ D.support ∧ y₂ ∈ D.support := by
  by_cases hx₃Cmem : x₃ ∈ C.support
  · exact Or.inr ⟨w, C, hC, hx₀C, hx₁C, hx₂C, hx₃Cmem, hy₁C, hy₂C⟩
  have hqRevC : ∀ a ∈ q.reverse.support, a ∈ C.support → a = z₂ ∨ a = z₁ := by
    intro a haq haC
    rcases hqC a (by simpa using haq) haC with h | h
    · exact Or.inr h
    · exact Or.inl h
  have splitTarget {A B : G.Walk z₁ z₂} {a d : V}
      (hA : A.IsPath) (hB : B.IsPath)
      (hAC : ∀ a ∈ A.support, a ∈ C.support)
      (hBC : ∀ a ∈ B.support, a ∈ C.support)
      (hAB : ∀ a, a ∈ A.support → a ∈ B.support → a = z₁ ∨ a = z₂)
      (hx₂a : x₂ ≠ a) (hx₂d : x₂ ≠ d) (had : a ≠ d)
      (hx₁a : G.Adj x₁ a) (hx₁d : G.Adj x₁ d)
      (hx₂A : x₂ ∈ A.support) (haA : a ∈ A.support)
      (hdB : d ∈ B.support) (hdnotA : d ∉ A.support) :
      HasThreeSpokeCycleTest G := by
    by_cases hx₂z₁ : x₂ = z₁
    · have hz₁a : z₁ ≠ a := by
        intro h
        exact hx₂a (hx₂z₁.trans h)
      apply hasThreeSpokeCycle_of_ear_and_split_arcs_at_start
        hA hB hAC hBC hAB haA hdB hdnotA hq hx₃q
        hz₁C hz₂C hx₀C hx₁C hx₃Cmem hqC hx₀q hx₁q hz₁z₂
        hz₁a hx₁x₃ hx₀x₁
      · simpa [← hx₂z₁] using hx₀x₂
      · exact hx₀x₃
      · exact hx₁a
      · exact hx₁d
    · by_cases hx₂z₂ : x₂ = z₂
      · have hARevC : ∀ a ∈ A.reverse.support, a ∈ C.support := by
          intro a ha
          exact hAC a (by simpa using ha)
        have hBRevC : ∀ a ∈ B.reverse.support, a ∈ C.support := by
          intro a ha
          exact hBC a (by simpa using ha)
        have hBARev : ∀ a, a ∈ A.reverse.support → a ∈ B.reverse.support →
            a = z₂ ∨ a = z₁ := by
          intro a ha hb
          rcases hAB a (by simpa using ha) (by simpa using hb) with h | h
          · exact Or.inr h
          · exact Or.inl h
        have hdnotARev : d ∉ A.reverse.support := by simpa using hdnotA
        have hz₂a : z₂ ≠ a := by
          intro h
          exact hx₂a (hx₂z₂.trans h)
        apply hasThreeSpokeCycle_of_ear_and_split_arcs_at_start
          hA.reverse hB.reverse hARevC hBRevC hBARev
          (by simpa using haA) (by simpa using hdB) hdnotARev
          hq.reverse (by simpa using hx₃q) hz₂C hz₁C hx₀C hx₁C
          hx₃Cmem hqRevC (by simpa using hx₀q) (by simpa using hx₁q)
          hz₁z₂.symm hz₂a hx₁x₃ hx₀x₁
        · simpa [← hx₂z₂] using hx₀x₂
        · exact hx₀x₃
        · exact hx₁a
        · exact hx₁d
      · obtain hP | hP := exists_endpoint_arc_through_split hA hB hAC hBC hAB
          hx₂A haA hdB hx₂z₁ hx₂z₂
        · obtain ⟨P, hPpath, haP, hdP, hPC⟩ := hP
          exact hasThreeSpokeCycle_of_ear_arc hPpath hPC haP hdP
            hq.reverse (by simpa using hx₃q) hz₂C hz₁C hx₂C hx₀C
            hx₁C hx₃Cmem hqRevC (by simpa using hx₀q)
            (by simpa using hx₁q) hz₁z₂.symm hx₂z₂ hx₂z₁ had
            hx₀x₁ hx₀x₂ hx₀x₃ hx₁a hx₁d
        · obtain ⟨P, hPpath, haP, hdP, hPC⟩ := hP
          exact hasThreeSpokeCycle_of_ear_arc hPpath hPC haP hdP
            hq hx₃q hz₁C hz₂C hx₂C hx₀C hx₁C hx₃Cmem hqC
            hx₀q hx₁q hz₁z₂ hx₂z₁ hx₂z₂ had
            hx₀x₁ hx₀x₂ hx₀x₃ hx₁a hx₁d
  obtain ⟨A, B, hA, hB, hAC, hBC, hAB, hcover⟩ :=
    Walk.IsCycle.exists_two_arcs hC hz₁C hz₂C hz₁z₂
  have hz₁A : z₁ ∈ A.support := Walk.start_mem_support A
  have hz₂A : z₂ ∈ A.support := Walk.end_mem_support A
  have hz₁B : z₁ ∈ B.support := Walk.start_mem_support B
  have hz₂B : z₂ ∈ B.support := Walk.end_mem_support B
  by_cases hy₁A : y₁ ∈ A.support
  · by_cases hy₂A : y₂ ∈ A.support
    · by_cases hx₂A : x₂ ∈ A.support
      · right
        exact exists_cycle_of_ear_and_arc hA hAC hx₂A hy₁A hy₂A hq hx₃q
          hz₁C hz₂C hx₀C hx₁C hx₃Cmem hqC hx₀q hx₁q hz₁z₂
      · left
        have hx₂B : x₂ ∈ B.support := (hcover x₂ hx₂C).resolve_left hx₂A
        have hx₂z₁ : x₂ ≠ z₁ := fun h ↦ hx₂A (h ▸ hz₁A)
        have hx₂z₂ : x₂ ≠ z₂ := fun h ↦ hx₂A (h ▸ hz₂A)
        exact hasThreeSpokeCycle_of_ear_and_opposite_arcs hA hB hAC hBC hAB
          hy₁A hy₂A hx₂B hq hx₃q hz₁C hz₂C hx₀C hx₁C hx₃Cmem
          hqC hx₀q hx₁q hz₁z₂ hx₂z₁ hx₂z₂ hx₁x₃ hy₁y₂
          hx₀x₁ hx₀x₂ hx₀x₃ hx₁y₁ hx₁y₂
    · have hy₂B : y₂ ∈ B.support := (hcover y₂ hy₂C).resolve_left hy₂A
      by_cases hx₂A : x₂ ∈ A.support
      · left
        exact splitTarget hA hB hAC hBC hAB
          hx₂y₁ hx₂y₂ hy₁y₂ hx₁y₁ hx₁y₂ hx₂A hy₁A hy₂B hy₂A
      · have hx₂B : x₂ ∈ B.support := (hcover x₂ hx₂C).resolve_left hx₂A
        by_cases hy₁B : y₁ ∈ B.support
        · right
          exact exists_cycle_of_ear_and_arc hB hBC hx₂B hy₁B hy₂B hq hx₃q
            hz₁C hz₂C hx₀C hx₁C hx₃Cmem hqC hx₀q hx₁q hz₁z₂
        · left
          have hBA : ∀ a, a ∈ B.support → a ∈ A.support → a = z₁ ∨ a = z₂ :=
            fun a haB haA ↦ hAB a haA haB
          exact splitTarget hB hA hBC hAC hBA
            hx₂y₂ hx₂y₁ hy₁y₂.symm hx₁y₂ hx₁y₁
            hx₂B hy₂B hy₁A hy₁B
  · have hy₁B : y₁ ∈ B.support := (hcover y₁ hy₁C).resolve_left hy₁A
    by_cases hy₂A : y₂ ∈ A.support
    · by_cases hx₂A : x₂ ∈ A.support
      · left
        exact splitTarget hA hB hAC hBC hAB
          hx₂y₂ hx₂y₁ hy₁y₂.symm hx₁y₂ hx₁y₁
          hx₂A hy₂A hy₁B hy₁A
      · have hx₂B : x₂ ∈ B.support := (hcover x₂ hx₂C).resolve_left hx₂A
        by_cases hy₂B : y₂ ∈ B.support
        · right
          exact exists_cycle_of_ear_and_arc hB hBC hx₂B hy₁B hy₂B hq hx₃q
            hz₁C hz₂C hx₀C hx₁C hx₃Cmem hqC hx₀q hx₁q hz₁z₂
        · left
          have hBA : ∀ a, a ∈ B.support → a ∈ A.support → a = z₁ ∨ a = z₂ :=
            fun a haB haA ↦ hAB a haA haB
          exact splitTarget hB hA hBC hAC hBA
            hx₂y₁ hx₂y₂ hy₁y₂ hx₁y₁ hx₁y₂
            hx₂B hy₁B hy₂A hy₂B
    · have hy₂B : y₂ ∈ B.support := (hcover y₂ hy₂C).resolve_left hy₂A
      by_cases hx₂B : x₂ ∈ B.support
      · right
        exact exists_cycle_of_ear_and_arc hB hBC hx₂B hy₁B hy₂B hq hx₃q
          hz₁C hz₂C hx₀C hx₁C hx₃Cmem hqC hx₀q hx₁q hz₁z₂
      · left
        have hx₂A : x₂ ∈ A.support := (hcover x₂ hx₂C).resolve_right hx₂B
        have hBA : ∀ a, a ∈ B.support → a ∈ A.support → a = z₁ ∨ a = z₂ :=
          fun a haB haA ↦ hAB a haA haB
        have hx₂z₁ : x₂ ≠ z₁ := fun h ↦ hx₂B (h ▸ hz₁B)
        have hx₂z₂ : x₂ ≠ z₂ := fun h ↦ hx₂B (h ▸ hz₂B)
        exact hasThreeSpokeCycle_of_ear_and_opposite_arcs hB hA hBC hAC hBA
          hy₁B hy₂B hx₂A hq hx₃q hz₁C hz₂C hx₀C hx₁C hx₃Cmem
          hqC hx₀q hx₁q hz₁z₂ hx₂z₁ hx₂z₂ hx₁x₃ hy₁y₂
          hx₀x₁ hx₀x₂ hx₀x₃ hx₁y₁ hx₁y₂

theorem neighborFinsetOn_eq_triple_of_card_eq_three
    {G : SimpleGraph V} {s : Finset V} {x₀ x₁ x₂ x₃ : V}
    (hcard : (neighborFinsetOn G s x₀).card = 3)
    (hx₁ : x₁ ∈ neighborFinsetOn G s x₀)
    (hx₂ : x₂ ∈ neighborFinsetOn G s x₀)
    (hx₃ : x₃ ∈ neighborFinsetOn G s x₀)
    (hx₁x₂ : x₁ ≠ x₂) (hx₁x₃ : x₁ ≠ x₃) (hx₂x₃ : x₂ ≠ x₃) :
    neighborFinsetOn G s x₀ = {x₁, x₂, x₃} := by
  have hsub : ({x₁, x₂, x₃} : Finset V) ⊆ neighborFinsetOn G s x₀ := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  have htriple : ({x₁, x₂, x₃} : Finset V).card = 3 := by
    simp [hx₁x₂, hx₁x₃, hx₂x₃]
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

theorem degree_three_vertex_not_mem_path_to_first_hit
    {G : SimpleGraph V} {s : Finset V} {x₀ x₁ x₂ x₃ u z : V}
    {T : List V} {p : G.Walk u z}
    (hp : p.IsPath) (hps : ∀ a ∈ p.support, a ∈ s)
    (hux₀ : u ≠ x₀) (hzx₀ : z ≠ x₀) (hx₁p : x₁ ∉ p.support)
    (hfirst : ∀ a ∈ p.support, a ∈ T → a = z)
    (hx₂T : x₂ ∈ T) (hx₃T : x₃ ∈ T)
    (hcard : (neighborFinsetOn G s x₀).card = 3)
    (hx₁s : x₁ ∈ s) (hx₂s : x₂ ∈ s) (hx₃s : x₃ ∈ s)
    (hx₀x₁ : G.Adj x₀ x₁) (hx₀x₂ : G.Adj x₀ x₂)
    (hx₀x₃ : G.Adj x₀ x₃)
    (hx₁x₂ : x₁ ≠ x₂) (hx₁x₃ : x₁ ≠ x₃) (hx₂x₃ : x₂ ≠ x₃) :
    x₀ ∉ p.support := by
  classical
  intro hx₀p
  have hx₁N : x₁ ∈ neighborFinsetOn G s x₀ :=
    Finset.mem_filter.mpr ⟨hx₁s, hx₀x₁⟩
  have hx₂N : x₂ ∈ neighborFinsetOn G s x₀ :=
    Finset.mem_filter.mpr ⟨hx₂s, hx₀x₂⟩
  have hx₃N : x₃ ∈ neighborFinsetOn G s x₀ :=
    Finset.mem_filter.mpr ⟨hx₃s, hx₀x₃⟩
  have hN := neighborFinsetOn_eq_triple_of_card_eq_three hcard
    hx₁N hx₂N hx₃N hx₁x₂ hx₁x₃ hx₂x₃
  let L : G.Walk u x₀ := p.takeUntil x₀ hx₀p
  let R : G.Walk x₀ z := p.dropUntil x₀ hx₀p
  have hLnon : ¬L.Nil := Walk.not_nil_of_ne hux₀
  have hRnon : ¬R.Nil := Walk.not_nil_of_ne hzx₀.symm
  let a : V := L.penultimate
  let b : V := R.snd
  have haL : a ∈ L.support := by
    exact List.mem_of_mem_dropLast (L.penultimate_mem_dropLast_support hLnon)
  have hbRtailList : b ∈ R.support.tail := R.snd_mem_tail_support hRnon
  have hbR : b ∈ R.support := List.mem_of_mem_tail hbRtailList
  have hap : a ∈ p.support :=
    p.support_takeUntil_subset_support hx₀p (by simpa [L] using haL)
  have hbp : b ∈ p.support :=
    p.support_dropUntil_subset_support hx₀p (by simpa [R] using hbR)
  have haN : a ∈ neighborFinsetOn G s x₀ := by
    apply Finset.mem_filter.mpr
    exact ⟨hps a hap, (L.adj_penultimate hLnon).symm⟩
  have hbN : b ∈ neighborFinsetOn G s x₀ := by
    apply Finset.mem_filter.mpr
    exact ⟨hps b hbp, R.adj_snd hRnon⟩
  have haCases : a = x₁ ∨ a = x₂ ∨ a = x₃ := by
    rw [hN] at haN
    simpa using haN
  have hbCases : b = x₁ ∨ b = x₂ ∨ b = x₃ := by
    rw [hN] at hbN
    simpa using hbN
  have haz : a = z := by
    rcases haCases with h | h | h
    · exact (hx₁p (h ▸ hap)).elim
    · exact h.trans (hfirst x₂ (h ▸ hap) hx₂T)
    · exact h.trans (hfirst x₃ (h ▸ hap) hx₃T)
  have hbz : b = z := by
    rcases hbCases with h | h | h
    · exact (hx₁p (h ▸ hbp)).elim
    · exact h.trans (hfirst x₂ (h ▸ hbp) hx₂T)
    · exact h.trans (hfirst x₃ (h ▸ hbp) hx₃T)
  have hwhole : (L.append R).IsPath := by
    simpa [L, R, p.take_spec hx₀p] using hp
  have hdisj : L.support.Disjoint R.tail.support :=
    hwhole.disjoint_support_of_append hRnon
  have hbRtail : b ∈ R.tail.support := by
    rw [R.support_tail_of_not_nil hRnon]
    exact hbRtailList
  exact hdisj haL (haz.trans hbz.symm ▸ hbRtail)

theorem hasThreeSpokeCycle_of_four_cycle_and_fourth_neighbor
    {G : SimpleGraph V} {s : Finset V}
    (hs3 : 3 ≤ s.card)
    (hnlow : ¬HasLowSeparationOn G s)
    (hntwo : ¬Nonempty (TwoSeparationOn G s))
    (hfree : ¬HasThreeSpokeCycleTest G)
    (hE : (edgeSetOn G s).ncard = 2 * s.card - 3)
    (hsmaller : ∀ (H : SimpleGraph V) (t : Finset V), t.card < s.card →
      3 ≤ t.card → ¬HasThreeSpokeCycleTest H →
      (edgeSetOn H t).ncard = 2 * t.card - 3 → IsCockadeOn H t)
    {w x₀ x₁ x₂ x₃ y₁ y₂ x₄ : V} {C : G.Walk w w}
    (hC : C.IsCycle) (hx₀C : x₀ ∉ C.support) (hx₁C : x₁ ∉ C.support)
    (hx₂C : x₂ ∈ C.support) (hx₃C : x₃ ∈ C.support)
    (hy₁C : y₁ ∈ C.support) (hy₂C : y₂ ∈ C.support)
    (hx₁s : x₁ ∈ s) (hx₂s : x₂ ∈ s) (hx₃s : x₃ ∈ s)
    (hy₁s : y₁ ∈ s) (hy₂s : y₂ ∈ s) (hx₄s : x₄ ∈ s)
    (hx₄x₀ : x₄ ≠ x₀) (hx₄y₁ : x₄ ≠ y₁)
    (hx₄x₁ : x₄ ≠ x₁) (hx₄y₂ : x₄ ≠ y₂)
    (hx₁x₂ : x₁ ≠ x₂) (hx₁x₃ : x₁ ≠ x₃) (hx₂x₃ : x₂ ≠ x₃)
    (hx₂y₁ : x₂ ≠ y₁) (hx₂y₂ : x₂ ≠ y₂) (hy₁y₂ : y₁ ≠ y₂)
    (hx₀x₁ : G.Adj x₀ x₁) (hx₀x₂ : G.Adj x₀ x₂)
    (hx₀x₃ : G.Adj x₀ x₃) (hx₁y₁ : G.Adj x₁ y₁)
    (hx₁y₂ : G.Adj x₁ y₂) (hx₁x₄ : G.Adj x₁ x₄)
    (hy₁y₂Not : ¬G.Adj y₁ y₂)
    (hx₀deg : (neighborFinsetOn G s x₀).card = 3) :
    HasThreeSpokeCycleTest G := by
  have hy₁x₁ : y₁ ≠ x₁ := hx₁y₁.ne.symm
  have hy₂x₁ : y₂ ≠ x₁ := hx₁y₂.ne.symm
  have htriple₄ : x₄ ∉ ({y₁, x₁, y₂} : Finset V) := by
    simp [hx₄y₁, hx₄x₁, hx₄y₂]
  have htriple₂ : x₂ ∉ ({y₁, x₁, y₂} : Finset V) := by
    simp [hx₂y₁, hx₁x₂.symm, hx₂y₂]
  obtain ⟨r, hr⟩ := reachableOnAvoiding_triple_of_path_of_core_exact
    hs3 hnlow hntwo hfree hE hsmaller hy₁s hx₁s hy₂s
    hy₁x₁ hy₁y₂ hx₁y₂.ne
    hx₁y₁.symm hx₁y₂ hy₁y₂Not hx₄s htriple₄ hx₂s htriple₂
  let P : G.Walk x₄ x₂ := r.toPath
  have hP : P.IsPath := Walk.bypass_isPath r
  have hPs : ∀ a ∈ P.support, a ∈ s := by
    intro a ha
    exact (hr a (r.support_bypass_subset_support ha)).1
  have hPavoid : ∀ a ∈ P.support, a ∉ ({y₁, x₁, y₂} : Finset V) := by
    intro a ha
    exact (hr a (r.support_bypass_subset_support ha)).2
  let T : Finset V := C.support.toFinset
  have hmeet : {a ∈ T | a ∈ P.support}.Nonempty := by
    refine ⟨x₂, Finset.mem_filter.mpr ⟨?_, Walk.end_mem_support P⟩⟩
    simpa [T] using hx₂C
  obtain ⟨z, hzT, hzP, hzfirst⟩ :=
    P.exists_mem_support_forall_mem_support_imp_eq T hmeet
  let Q : G.Walk x₄ z := P.takeUntil z hzP
  have hQ : Q.IsPath := hP.takeUntil hzP
  have hQs : ∀ a ∈ Q.support, a ∈ s := by
    intro a ha
    exact hPs a (P.support_takeUntil_subset_support hzP ha)
  have hQavoid : ∀ a ∈ Q.support, a ∉ ({y₁, x₁, y₂} : Finset V) := by
    intro a ha
    exact hPavoid a (P.support_takeUntil_subset_support hzP ha)
  have hzC : z ∈ C.support := by simpa [T] using hzT
  have hzNotx₀ : z ≠ x₀ := fun h ↦ hx₀C (h ▸ hzC)
  have hx₁Q : x₁ ∉ Q.support := by
    intro h
    exact hQavoid x₁ h (by simp)
  have hx₀Q : x₀ ∉ Q.support := by
    apply degree_three_vertex_not_mem_path_to_first_hit hQ hQs hx₄x₀
      hzNotx₀ hx₁Q
    · intro a haQ haC
      apply hzfirst a
      · simpa [T] using haC
      · exact haQ
    · exact hx₂C
    · exact hx₃C
    · exact hx₀deg
    · exact hx₁s
    · exact hx₂s
    · exact hx₃s
    · exact hx₀x₁
    · exact hx₀x₂
    · exact hx₀x₃
    · exact hx₁x₂
    · exact hx₁x₃
    · exact hx₂x₃
  have hy₁z : y₁ ≠ z := by
    intro h
    exact hQavoid y₁ (h ▸ Walk.end_mem_support Q) (by simp)
  have hy₂z : y₂ ≠ z := by
    intro h
    exact hQavoid y₂ (h ▸ Walk.end_mem_support Q) (by simp)
  let R : G.Walk x₁ z := Walk.cons hx₁x₄ Q
  have hR : R.IsPath := hQ.cons hx₁Q
  have hx₀R : x₀ ∉ R.support := by
    simp [R, hx₀x₁.ne, hx₀Q]
  have hRC : ∀ a ∈ R.support, a ∈ C.support → a = z := by
    intro a haR haC
    have haCases : a = x₁ ∨ a ∈ Q.support := by simpa [R] using haR
    rcases haCases with rfl | haQ
    · exact (hx₁C haC).elim
    · apply hzfirst a
      · simpa [T] using haC
      · exact haQ
  exact hasThreeSpokeCycle_of_cycle_and_three_fan hC hx₀C hx₁C
    hx₂C hx₃C hy₁C hy₂C hzC hR hx₀R hRC hy₁y₂ hy₁z hy₂z
    hx₁x₂ hx₁x₃ hx₂x₃ hx₀x₁ hx₀x₂ hx₀x₃ hx₁y₁ hx₁y₂

def restrictOn (G : SimpleGraph V) (t : Finset V) : SimpleGraph V where
  Adj u v := u ∈ t ∧ v ∈ t ∧ G.Adj u v
  symm := ⟨by
    rintro u v ⟨hu, hv, huv⟩
    exact ⟨hv, hu, huv.symm⟩⟩
  loopless := ⟨by
    rintro u ⟨_, _, huu⟩
    exact G.loopless.irrefl u huu⟩

@[simp]
theorem restrictOn_adj {G : SimpleGraph V} {t : Finset V} {u v : V} :
    (restrictOn G t).Adj u v ↔ u ∈ t ∧ v ∈ t ∧ G.Adj u v := Iff.rfl

theorem edgeSetOn_ncard_sup_edge_restrictOn
    {G : SimpleGraph V} {t : Finset V} {x₁ x₂ : V}
    (hx₁t : x₁ ∈ t) (hx₂t : x₂ ∈ t) (hx₁x₂ : x₁ ≠ x₂)
    (hnadj : ¬G.Adj x₁ x₂) :
    (edgeSetOn (restrictOn G t ⊔ edge x₁ x₂) t).ncard =
      (edgeSetOn G t).ncard + 1 := by
  classical
  have heq : edgeSetOn (restrictOn G t ⊔ edge x₁ x₂) t =
      insert s(x₁, x₂) (edgeSetOn G t) := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
        simp only [edgeSetOn, Set.mem_inter_iff, mem_edgeSet,
          Set.mk_mem_sym2_iff, Set.mem_insert_iff]
        constructor
        · rintro ⟨huv, hut, hvt⟩
          rw [sup_adj] at huv
          rcases huv with huv | huv
          · exact Or.inr ⟨huv.2.2, hut, hvt⟩
          · left
            rcases (edge_adj (s := x₁) (t := x₂) u v).mp huv with ⟨h, _⟩
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · rfl
            · exact Sym2.eq_swap
        · rintro (huv | ⟨huv, hut, hvt⟩)
          · rw [Sym2.eq_iff] at huv
            rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
            · subst u
              subst v
              refine ⟨(sup_adj _ _ _ _).mpr (Or.inr ?_), hx₁t, hx₂t⟩
              exact (edge_adj (s := x₁) (t := x₂) x₁ x₂).mpr
                ⟨Or.inl ⟨rfl, rfl⟩, hx₁x₂⟩
            · subst u
              subst v
              refine ⟨(sup_adj _ _ _ _).mpr (Or.inr ?_), hx₂t, hx₁t⟩
              exact (edge_adj (s := x₁) (t := x₂) x₂ x₁).mpr
                ⟨Or.inr ⟨rfl, rfl⟩, hx₁x₂.symm⟩
          · refine ⟨(sup_adj _ _ _ _).mpr (Or.inl ?_), hut, hvt⟩
            exact ⟨hut, hvt, huv⟩
  rw [heq, Set.ncard_insert_of_notMem]
  intro hmem
  exact hnadj hmem.1

omit [Fintype V] in
theorem hasThreeSpokeCycle_of_two_paths_general
    {G : SimpleGraph V} {u v x₀ x₁ x₂ x₃ : V}
    {p q : G.Walk u v}
    (hp : p.IsPath) (hq : q.IsPath) (huv : u ≠ v)
    (hcommon : ∀ z, z ∈ p.support → z ∈ q.support → z = u ∨ z = v)
    (hlength : 1 < p.length ∨ 1 < q.length)
    (hx₀p : x₀ ∉ p.support) (hx₀q : x₀ ∉ q.support)
    (hx₁ : x₁ ∈ p.support ∨ x₁ ∈ q.support)
    (hx₂ : x₂ ∈ p.support ∨ x₂ ∈ q.support)
    (hx₃ : x₃ ∈ p.support ∨ x₃ ∈ q.support)
    (hx₁x₂ : x₁ ≠ x₂) (hx₁x₃ : x₁ ≠ x₃) (hx₂x₃ : x₂ ≠ x₃)
    (hx₀x₁ : G.Adj x₀ x₁) (hx₀x₂ : G.Adj x₀ x₂)
    (hx₀x₃ : G.Adj x₀ x₃) :
    HasThreeSpokeCycleTest G := by
  let D : G.Walk u u := p.append q.reverse
  have hD : D.IsCycle :=
    Walk.IsPath.isCycle_append_reverse_of_only_endpoints hp hq huv hcommon hlength
  have memD {x : V} (h : x ∈ p.support ∨ x ∈ q.support) : x ∈ D.support := by
    rw [Walk.mem_support_append_iff]
    exact h.imp_right (by simpa using ·)
  refine ⟨u, x₀, D, hD, ?_, x₁, memD hx₁, x₂, memD hx₂,
    x₃, memD hx₃, hx₁x₂, hx₁x₃, hx₂x₃, hx₀x₁, hx₀x₂, hx₀x₃⟩
  intro h
  rw [Walk.mem_support_append_iff] at h
  exact h.elim hx₀p (fun h ↦ hx₀q (by simpa using h))

theorem hasThreeSpokeCycle_of_ear_containing_center
    {G : SimpleGraph V} {w z₁ z₂ x₀ x₁ x₂ x₃ : V}
    {C : G.Walk w w} {q : G.Walk z₁ z₂}
    (hC : C.IsCycle) (hx₀C : x₀ ∉ C.support) (hx₂C : x₂ ∈ C.support)
    (hx₃C : x₃ ∉ C.support)
    (hq : q.IsPath) (hx₀q : x₀ ∉ q.support)
    (hx₁q : x₁ ∈ q.support) (hx₃q : x₃ ∈ q.support)
    (hz₁C : z₁ ∈ C.support) (hz₂C : z₂ ∈ C.support)
    (hz₁z₂ : z₁ ≠ z₂)
    (hqC : ∀ a ∈ q.support, a ∈ C.support → a = z₁ ∨ a = z₂)
    (hx₁x₂ : x₁ ≠ x₂) (hx₁x₃ : x₁ ≠ x₃) (hx₂x₃ : x₂ ≠ x₃)
    (hx₀x₁ : G.Adj x₀ x₁) (hx₀x₂ : G.Adj x₀ x₂)
    (hx₀x₃ : G.Adj x₀ x₃) :
    HasThreeSpokeCycleTest G := by
  obtain ⟨A, B, hA, hB, hAC, hBC, _, hcover⟩ :=
    Walk.IsCycle.exists_two_arcs hC hz₁C hz₂C hz₁z₂
  have hcommonA : ∀ a, a ∈ A.support → a ∈ q.support → a = z₁ ∨ a = z₂ := by
    intro a haA haq
    exact hqC a haq (hAC a haA)
  have hcommonB : ∀ a, a ∈ B.support → a ∈ q.support → a = z₁ ∨ a = z₂ := by
    intro a haB haq
    exact hqC a haq (hBC a haB)
  have hx₀A : x₀ ∉ A.support := fun h ↦ hx₀C (hAC x₀ h)
  have hx₀B : x₀ ∉ B.support := fun h ↦ hx₀C (hBC x₀ h)
  rcases hcover x₂ hx₂C with hx₂A | hx₂B
  · exact hasThreeSpokeCycle_of_two_paths_general hA hq hz₁z₂ hcommonA
      (Or.inr (Walk.IsPath.one_lt_length_of_mem_support_ne_ends hq hx₃q
        (fun h ↦ hx₃C (h ▸ hz₁C)) (fun h ↦ hx₃C (h ▸ hz₂C))))
      hx₀A hx₀q (Or.inr hx₁q) (Or.inl hx₂A) (Or.inr hx₃q)
      hx₁x₂ hx₁x₃ hx₂x₃ hx₀x₁ hx₀x₂ hx₀x₃
  · exact hasThreeSpokeCycle_of_two_paths_general hB hq hz₁z₂ hcommonB
      (Or.inr (Walk.IsPath.one_lt_length_of_mem_support_ne_ends hq hx₃q
        (fun h ↦ hx₃C (h ▸ hz₁C)) (fun h ↦ hx₃C (h ▸ hz₂C))))
      hx₀B hx₀q (Or.inr hx₁q) (Or.inl hx₂B) (Or.inr hx₃q)
      hx₁x₂ hx₁x₃ hx₂x₃ hx₀x₁ hx₀x₂ hx₀x₃

theorem hasThreeSpokeCycle_of_fake_spoke_cycle
    {G : SimpleGraph V} {s : Finset V}
    (hs7 : 7 ≤ s.card)
    (hnlow : ¬HasLowSeparationOn G s)
    (hntwo : ¬Nonempty (TwoSeparationOn G s))
    (hfree : ¬HasThreeSpokeCycleTest G)
    (hE : (edgeSetOn G s).ncard = 2 * s.card - 3)
    (hsmaller : ∀ (H : SimpleGraph V) (t : Finset V), t.card < s.card →
      3 ≤ t.card → ¬HasThreeSpokeCycleTest H →
      (edgeSetOn H t).ncard = 2 * t.card - 3 → IsCockadeOn H t)
    {w x₀ x₁ x₂ x₃ y₁ y₂ : V} {C : G.Walk w w}
    (hC : C.IsCycle) (hx₀C : x₀ ∉ C.support) (hx₁C : x₁ ∉ C.support)
    (hx₂C : x₂ ∈ C.support) (hy₁C : y₁ ∈ C.support)
    (hy₂C : y₂ ∈ C.support) (hCs : ∀ a ∈ C.support, a ∈ s)
    (hx₀s : x₀ ∈ s) (hx₁s : x₁ ∈ s) (hx₂s : x₂ ∈ s)
    (hx₃s : x₃ ∈ s)
    (hx₁x₂ : x₁ ≠ x₂) (hx₁x₃ : x₁ ≠ x₃) (hx₂x₃ : x₂ ≠ x₃)
    (hx₂y₁ : x₂ ≠ y₁) (hx₂y₂ : x₂ ≠ y₂) (hy₁y₂ : y₁ ≠ y₂)
    (hx₀x₁ : G.Adj x₀ x₁) (hx₀x₂ : G.Adj x₀ x₂)
    (hx₀x₃ : G.Adj x₀ x₃) (hx₁y₁ : G.Adj x₁ y₁)
    (hx₁y₂ : G.Adj x₁ y₂)
    (hx₀deg : (neighborFinsetOn G s x₀).card = 3)
    (hx₁high : 4 ≤ (neighborFinsetOn G s x₁).card) :
    HasThreeSpokeCycleTest G := by
  classical
  have hs4 : 4 ≤ s.card := by omega
  have hs3 : 3 ≤ s.card := by omega
  have hy₁s : y₁ ∈ s := hCs y₁ hy₁C
  have hy₂s : y₂ ∈ s := hCs y₂ hy₂C
  by_cases hy₁y₂Adj : G.Adj y₁ y₂
  · exact hasThreeSpokeCycle_of_triangle hs4 hnlow hntwo
      hx₁s hy₁s hy₂s hx₁y₁.ne hx₁y₂.ne hy₁y₂
      hx₁y₁ hx₁y₂ hy₁y₂Adj
  have finish {d : V} {D : G.Walk d d}
      (hD : D.IsCycle) (hx₀D : x₀ ∉ D.support) (hx₁D : x₁ ∉ D.support)
      (hx₂D : x₂ ∈ D.support) (hx₃D : x₃ ∈ D.support)
      (hy₁D : y₁ ∈ D.support) (hy₂D : y₂ ∈ D.support) :
      HasThreeSpokeCycleTest G := by
    let N : Finset V := neighborFinsetOn G s x₁
    have hNhigh : 4 ≤ N.card := by simpa [N] using hx₁high
    have hx₀N : x₀ ∈ N := Finset.mem_filter.mpr ⟨hx₀s, hx₀x₁.symm⟩
    have hy₁N : y₁ ∈ N := Finset.mem_filter.mpr ⟨hy₁s, hx₁y₁⟩
    have hy₂N : y₂ ∈ N := Finset.mem_filter.mpr ⟨hy₂s, hx₁y₂⟩
    have hx₀y₁ : x₀ ≠ y₁ := fun h ↦ hx₀D (h ▸ hy₁D)
    have hx₀y₂ : x₀ ≠ y₂ := fun h ↦ hx₀D (h ▸ hy₂D)
    have htripleCard : ({x₀, y₁, y₂} : Finset V).card = 3 := by
      simp [hx₀y₁, hx₀y₂, hy₁y₂]
    have hnsub : ¬N ⊆ {x₀, y₁, y₂} := by
      intro hsub
      have hcard := Finset.card_le_card hsub
      change N.card ≤ _ at hcard
      rw [htripleCard] at hcard
      omega
    obtain ⟨x₄, hx₄N, hx₄not⟩ := Finset.not_subset.mp hnsub
    have hx₄s : x₄ ∈ s := (Finset.mem_filter.mp hx₄N).1
    have hx₁x₄ : G.Adj x₁ x₄ := (Finset.mem_filter.mp hx₄N).2
    have hx₄x₀ : x₄ ≠ x₀ := by
      intro h
      exact hx₄not (by simp [h])
    have hx₄y₁ : x₄ ≠ y₁ := by
      intro h
      exact hx₄not (by simp [h])
    have hx₄y₂ : x₄ ≠ y₂ := by
      intro h
      exact hx₄not (by simp [h])
    exact hasThreeSpokeCycle_of_four_cycle_and_fourth_neighbor
      hs3 hnlow hntwo hfree hE hsmaller hD hx₀D hx₁D
      hx₂D hx₃D hy₁D hy₂D hx₁s hx₂s hx₃s hy₁s hy₂s hx₄s
      hx₄x₀ hx₄y₁ hx₁x₄.ne.symm hx₄y₂ hx₁x₂ hx₁x₃ hx₂x₃
      hx₂y₁ hx₂y₂ hy₁y₂ hx₀x₁ hx₀x₂ hx₀x₃ hx₁y₁ hx₁y₂
      hx₁x₄ hy₁y₂Adj hx₀deg
  by_cases hx₃C : x₃ ∈ C.support
  · exact finish hC hx₀C hx₁C hx₂C hx₃C hy₁C hy₂C
  have hbaseEdge : s(w, C.snd) ∈ C.edges := C.mk_start_snd_mem_edges hC.not_nil
  obtain ⟨z₁, z₂, q, hz₁C, hz₂C, hz₁z₂, hq, hx₀q, hx₃q, hqs, hqC⟩ :=
    exists_ear_through_vertex_of_core hnlow hntwo hx₀s hx₃s
      hx₀x₃.ne.symm hC hx₀C hx₃C hbaseEdge hCs
  by_cases hx₁q : x₁ ∈ q.support
  · exact hasThreeSpokeCycle_of_ear_containing_center hC hx₀C hx₂C hx₃C
      hq hx₀q hx₁q hx₃q hz₁C hz₂C hz₁z₂ hqC
      hx₁x₂ hx₁x₃ hx₂x₃ hx₀x₁ hx₀x₂ hx₀x₃
  rcases hasThreeSpokeCycle_or_exists_four_vertex_cycle_of_ear
      hC hx₀C hx₁C hx₂C hy₁C hy₂C hq hx₀q hx₁q hx₃q
      hz₁C hz₂C hz₁z₂ hqC hx₂y₁ hx₂y₂ hy₁y₂ hx₁x₃
      hx₀x₁ hx₀x₂ hx₀x₃ hx₁y₁ hx₁y₂ with htarget | hcycle
  · exact htarget
  · obtain ⟨d, D, hD, hx₀D, hx₁D, hx₂D, hx₃D, hy₁D, hy₂D⟩ := hcycle
    exact finish hD hx₀D hx₁D hx₂D hx₃D hy₁D hy₂D

omit [Fintype V] in
theorem sym2_left_cancel_of_left_ne {x y z : V} (hxy : x ≠ y)
    (h : s(x, y) = s(x, z)) : y = z := by
  rw [Sym2.eq_iff] at h
  rcases h with ⟨_, hyz⟩ | ⟨_, hyx⟩
  · exact hyz
  · exact (hxy hyx.symm).elim

theorem hasThreeSpokeCycle_of_augmented_target
    {G H : SimpleGraph V} {s t : Finset V}
    (hs7 : 7 ≤ s.card)
    (hnlow : ¬HasLowSeparationOn G s)
    (hntwo : ¬Nonempty (TwoSeparationOn G s))
    (hfree : ¬HasThreeSpokeCycleTest G)
    (hE : (edgeSetOn G s).ncard = 2 * s.card - 3)
    (hsmaller : ∀ (K : SimpleGraph V) (u : Finset V), u.card < s.card →
      3 ≤ u.card → ¬HasThreeSpokeCycleTest K →
      (edgeSetOn K u).ncard = 2 * u.card - 3 → IsCockadeOn K u)
    {x₀ x₁ x₂ x₃ : V}
    (hx₀s : x₀ ∈ s) (hx₁s : x₁ ∈ s) (hx₂s : x₂ ∈ s) (hx₃s : x₃ ∈ s)
    (hx₀t : x₀ ∉ t)
    (hx₁x₂ : x₁ ≠ x₂) (hx₁x₃ : x₁ ≠ x₃) (hx₂x₃ : x₂ ≠ x₃)
    (hx₀x₁ : G.Adj x₀ x₁) (hx₀x₂ : G.Adj x₀ x₂)
    (hx₀x₃ : G.Adj x₀ x₃)
    (hx₀deg : (neighborFinsetOn G s x₀).card = 3)
    (hx₁high : 4 ≤ (neighborFinsetOn G s x₁).card)
    (hx₂high : 4 ≤ (neighborFinsetOn G s x₂).card)
    (hHverts : ∀ {u v}, H.Adj u v → u ∈ t ∧ v ∈ t)
    (hts : ∀ {u}, u ∈ t → u ∈ s)
    (hfake : H.Adj x₁ x₂)
    (hkeep : ∀ {u v}, H.Adj u v → s(u, v) ≠ s(x₁, x₂) → G.Adj u v)
    (hHtarget : HasThreeSpokeCycleTest H) :
    HasThreeSpokeCycleTest G := by
  classical
  obtain ⟨v, x, c, hc, hxc, a, hac, b, hbc, d, hdc,
    hab, had, hbd, hxa, hxb, hxd⟩ := hHtarget
  have cycle_mem_t {z : V} (hz : z ∈ c.support) : z ∈ t := by
    let R : H.Walk z z := c.rotate z hz
    have hR : R.IsCycle := Walk.IsCycle.rotate hz hc
    exact (hHverts (R.adj_snd hR.not_nil)).1
  have hx₀c : x₀ ∉ c.support := fun h ↦ hx₀t (cycle_mem_t h)
  have hxt : x ∈ t := (hHverts hxa).1
  have hxx₀ : x ≠ x₀ := fun h ↦ hx₀t (h ▸ hxt)
  let e : Sym2 V := s(x₁, x₂)
  by_cases hec : e ∈ c.edges
  · have hx₁c : x₁ ∈ c.support := c.fst_mem_support_of_mem_edges hec
    have hx₂c : x₂ ∈ c.support := c.snd_mem_support_of_mem_edges hec
    have spoke_ne {z : V} (hzc : z ∈ c.support) : s(x, z) ≠ e := by
      intro heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨hx, hz⟩ | ⟨hx, hz⟩
      · exact hxc (hx ▸ hx₁c)
      · exact hxc (hx ▸ hx₂c)
    obtain ⟨r, hr, hx₀r, hsub, hrsub⟩ := replace_cycle_edge_by_two
      c hc hec (by
        intro f hf hfe
        obtain ⟨u, w⟩ := f
        apply hkeep
        · simpa only [mem_edgeSet] using c.edges_subset_edgeSet hf
        · exact hfe) hx₀x₁.symm hx₀x₂ hx₀c
    refine ⟨x₁, x, r, hr, ?_, a, hsub a hac, b, hsub b hbc,
      d, hsub d hdc, hab, had, hbd, ?_, ?_, ?_⟩
    · intro hxr
      rcases hrsub x hxr with h | h
      · exact hxc h
      · exact hxx₀ h
    · exact hkeep hxa (spoke_ne hac)
    · exact hkeep hxb (spoke_ne hbc)
    · exact hkeep hxd (spoke_ne hdc)
  have cEdges : ∀ f, f ∈ c.edges → f ∈ G.edgeSet := by
    intro f hf
    obtain ⟨u, w⟩ := f
    apply hkeep
    · simpa only [mem_edgeSet] using c.edges_subset_edgeSet hf
    · intro h
      apply hec
      change s(x₁, x₂) ∈ c.edges
      rw [← h]
      exact hf
  let C : G.Walk v v := c.transfer G cEdges
  have hC : C.IsCycle := hc.transfer cEdges
  have supportC (z : V) : z ∈ C.support ↔ z ∈ c.support := by simp [C]
  have hx₀C : x₀ ∉ C.support := by simpa [supportC] using hx₀c
  have hxC : x ∉ C.support := by simpa [supportC] using hxc
  have direct (hae : s(x, a) ≠ e) (hbe : s(x, b) ≠ e)
      (hde : s(x, d) ≠ e) : HasThreeSpokeCycleTest G := by
    refine ⟨v, x, C, hC, hxC, a, ?_, b, ?_, d, ?_, hab, had, hbd,
      hkeep hxa hae, hkeep hxb hbe, hkeep hxd hde⟩
    · simpa [supportC] using hac
    · simpa [supportC] using hbc
    · simpa [supportC] using hdc
  have hard {r y z : V}
      (hrc : r ∈ c.support) (hyc : y ∈ c.support) (hzc : z ∈ c.support)
      (hry : r ≠ y) (hrz : r ≠ z) (hyz : y ≠ z)
      (hxr : H.Adj x r) (hxy : H.Adj x y) (hxz : H.Adj x z)
      (hxe : s(x, r) = e) : HasThreeSpokeCycleTest G := by
    have hxyNe : s(x, y) ≠ e := by
      intro h
      have hsame : s(x, y) = s(x, r) := h.trans hxe.symm
      exact hry (sym2_left_cancel_of_left_ne hxr.ne hsame.symm)
    have hxzNe : s(x, z) ≠ e := by
      intro h
      have hsame : s(x, z) = s(x, r) := h.trans hxe.symm
      exact hrz (sym2_left_cancel_of_left_ne hxr.ne hsame.symm)
    have hxyG : G.Adj x y := hkeep hxy hxyNe
    have hxzG : G.Adj x z := hkeep hxz hxzNe
    have hCs : ∀ q ∈ C.support, q ∈ s := by
      intro q hqC
      have hqt : q ∈ t := cycle_mem_t ((supportC q).mp hqC)
      exact hts hqt
    have hrs : r ∈ s := hts (cycle_mem_t hrc)
    have hys : y ∈ s := hts (cycle_mem_t hyc)
    have hzs : z ∈ s := hts (cycle_mem_t hzc)
    have hrC : r ∈ C.support := (supportC r).mpr hrc
    have hyC : y ∈ C.support := (supportC y).mpr hyc
    have hzC : z ∈ C.support := (supportC z).mpr hzc
    rw [Sym2.eq_iff] at hxe
    rcases hxe with ⟨hxx₁, hrx₂⟩ | ⟨hxx₂, hrx₁⟩
    · subst x
      subst r
      exact hasThreeSpokeCycle_of_fake_spoke_cycle hs7 hnlow hntwo hfree hE
        hsmaller hC hx₀C hxC hrC hyC hzC hCs hx₀s hx₁s hx₂s hx₃s
        hx₁x₂ hx₁x₃ hx₂x₃ hry hrz hyz hx₀x₁ hx₀x₂ hx₀x₃
        hxyG hxzG hx₀deg hx₁high
    · subst x
      subst r
      exact hasThreeSpokeCycle_of_fake_spoke_cycle hs7 hnlow hntwo hfree hE
        hsmaller hC hx₀C hxC hrC hyC hzC hCs hx₀s hx₂s hx₁s hx₃s
        hx₁x₂.symm hx₂x₃ hx₁x₃ hry hrz hyz
        hx₀x₂ hx₀x₁ hx₀x₃ hxyG hxzG hx₀deg hx₂high
  by_cases hae : s(x, a) = e
  · exact hard hac hbc hdc hab had hbd hxa hxb hxd hae
  by_cases hbe : s(x, b) = e
  · exact hard hbc hac hdc hab.symm hbd had hxb hxa hxd hbe
  by_cases hde : s(x, d) = e
  · exact hard hdc hac hbc had.symm hbd.symm hab hxd hxa hxb hde
  exact direct hae hbe hde

theorem false_of_core_exact_of_card_ge_seven
    {G : SimpleGraph V} {s : Finset V}
    (hs7 : 7 ≤ s.card)
    (hnlow : ¬HasLowSeparationOn G s)
    (hntwo : ¬Nonempty (TwoSeparationOn G s))
    (hfree : ¬HasThreeSpokeCycleTest G)
    (hE : (edgeSetOn G s).ncard = 2 * s.card - 3)
    (hsmaller : ∀ (K : SimpleGraph V) (u : Finset V), u.card < s.card →
      3 ≤ u.card → ¬HasThreeSpokeCycleTest K →
      (edgeSetOn K u).ncard = 2 * u.card - 3 → IsCockadeOn K u) :
    False := by
  classical
  have hs4 : 4 ≤ s.card := by omega
  have hacyc := degreeThree_induce_isAcyclic_of_core_exact
    hs7 hnlow hntwo hfree hE hsmaller
  obtain ⟨x₀, x₁, x₂, x₃, hx₀s, hx₁s, hx₂s, hx₃s,
    hx₁x₂, hx₁x₃, hx₂x₃, hx₀x₁, hx₀x₂, hx₀x₃,
    hx₀deg, hx₁high, hx₂high⟩ :=
      exists_degreeThree_vertex_with_two_high_neighbors
        hs4 hnlow hntwo hE hacyc
  have hnadj : ¬G.Adj x₁ x₂ := by
    intro hx₁x₂Adj
    apply hfree
    exact hasThreeSpokeCycle_of_triangle hs4 hnlow hntwo
      hx₀s hx₁s hx₂s hx₀x₁.ne hx₀x₂.ne hx₁x₂
      hx₀x₁ hx₀x₂ hx₁x₂Adj
  let t : Finset V := s.erase x₀
  let H : SimpleGraph V := restrictOn G t ⊔ edge x₁ x₂
  have hx₀t : x₀ ∉ t := by simp [t]
  have hx₁t : x₁ ∈ t := by
    exact Finset.mem_erase.mpr ⟨hx₀x₁.ne.symm, hx₁s⟩
  have hx₂t : x₂ ∈ t := by
    exact Finset.mem_erase.mpr ⟨hx₀x₂.ne.symm, hx₂s⟩
  have hx₃t : x₃ ∈ t := by
    exact Finset.mem_erase.mpr ⟨hx₀x₃.ne.symm, hx₃s⟩
  have htcard : t.card = s.card - 1 := by
    simp [t, Finset.card_erase_of_mem hx₀s]
  have htlt : t.card < s.card := by omega
  have ht3 : 3 ≤ t.card := by omega
  have hGt : (edgeSetOn G t).ncard = 2 * t.card - 4 := by
    have hdelete := edgeSetOn_ncard_erase_vertex (G := G) hx₀s
    change (edgeSetOn G t).ncard +
      (neighborFinsetOn G s x₀).card = (edgeSetOn G s).ncard at hdelete
    omega
  have hHexact : (edgeSetOn H t).ncard = 2 * t.card - 3 := by
    have hadd := edgeSetOn_ncard_sup_edge_restrictOn
      (G := G) hx₁t hx₂t hx₁x₂ hnadj
    change (edgeSetOn H t).ncard = (edgeSetOn G t).ncard + 1 at hadd
    omega
  have hHverts {u v : V} (huv : H.Adj u v) : u ∈ t ∧ v ∈ t := by
    change (restrictOn G t ⊔ edge x₁ x₂).Adj u v at huv
    rw [sup_adj] at huv
    rcases huv with huv | huv
    · exact ⟨huv.1, huv.2.1⟩
    · rcases (edge_adj (s := x₁) (t := x₂) u v).mp huv with ⟨h, _⟩
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hx₁t, hx₂t⟩
      · exact ⟨hx₂t, hx₁t⟩
  have hts {u : V} (hu : u ∈ t) : u ∈ s :=
    Finset.mem_of_mem_erase hu
  have hfake : H.Adj x₁ x₂ := by
    apply (sup_adj _ _ _ _).mpr
    right
    exact (edge_adj (s := x₁) (t := x₂) x₁ x₂).mpr
      ⟨Or.inl ⟨rfl, rfl⟩, hx₁x₂⟩
  have hkeep {u v : V} (huv : H.Adj u v)
      (hne : s(u, v) ≠ s(x₁, x₂)) : G.Adj u v := by
    change (restrictOn G t ⊔ edge x₁ x₂).Adj u v at huv
    rw [sup_adj] at huv
    rcases huv with huv | huv
    · exact huv.2.2
    · rcases (edge_adj (s := x₁) (t := x₂) u v).mp huv with ⟨h, _⟩
      apply (hne ?_).elim
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap
  by_cases hHtarget : HasThreeSpokeCycleTest H
  · exact hfree (hasThreeSpokeCycle_of_augmented_target hs7 hnlow hntwo
      hfree hE hsmaller hx₀s hx₁s hx₂s hx₃s hx₀t hx₁x₂ hx₁x₃
      hx₂x₃ hx₀x₁ hx₀x₂ hx₀x₃ hx₀deg hx₁high hx₂high
      hHverts hts hfake hkeep hHtarget)
  have hcockade : IsCockadeOn H t :=
    hsmaller H t htlt ht3 hHtarget hHexact
  have hG₁₃ : ¬G.Adj x₁ x₃ := by
    intro hx₁x₃Adj
    apply hfree
    exact hasThreeSpokeCycle_of_triangle hs4 hnlow hntwo
      hx₀s hx₁s hx₃s hx₀x₁.ne hx₀x₃.ne hx₁x₃
      hx₀x₁ hx₀x₃ hx₁x₃Adj
  have hG₂₃ : ¬G.Adj x₂ x₃ := by
    intro hx₂x₃Adj
    apply hfree
    exact hasThreeSpokeCycle_of_triangle hs4 hnlow hntwo
      hx₀s hx₂s hx₃s hx₀x₂.ne hx₀x₃.ne hx₂x₃
      hx₀x₂ hx₀x₃ hx₂x₃Adj
  have hp₁₃ : s(x₁, x₃) ≠ s(x₁, x₂) := by
    intro h
    exact hx₂x₃ (sym2_left_cancel_of_left_ne hx₁x₃ h).symm
  have hp₂₃ : s(x₂, x₃) ≠ s(x₁, x₂) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨hx₂x₁, hx₃x₂⟩ | ⟨hx₂x₂, hx₃x₁⟩
    · exact hx₁x₂ hx₂x₁.symm
    · exact hx₁x₃ hx₃x₁.symm
  have hH₁₃ : ¬H.Adj x₁ x₃ := fun h ↦ hG₁₃ (hkeep h hp₁₃)
  have hH₂₃ : ¬H.Adj x₂ x₃ := fun h ↦ hG₂₃ (hkeep h hp₂₃)
  apply hfree
  exact hcockade.hasThreeSpokeCycle_of_replace_edge
    hx₁t hx₂t hx₃t hx₀t hfake hH₁₃ hH₂₃
    (fun _ _ huv hne ↦ hkeep huv hne)
    hx₀x₁ hx₀x₂ hx₀x₃

theorem isCockadeOn_of_core_exact
    {G : SimpleGraph V} {s : Finset V}
    (hs3 : 3 ≤ s.card)
    (hnlow : ¬HasLowSeparationOn G s)
    (hntwo : ¬Nonempty (TwoSeparationOn G s))
    (hfree : ¬HasThreeSpokeCycleTest G)
    (hE : (edgeSetOn G s).ncard = 2 * s.card - 3)
    (hsmaller : ∀ (K : SimpleGraph V) (u : Finset V), u.card < s.card →
      3 ≤ u.card → ¬HasThreeSpokeCycleTest K →
      (edgeSetOn K u).ncard = 2 * u.card - 3 → IsCockadeOn K u) :
    IsCockadeOn G s := by
  by_cases hs6 : s.card ≤ 6
  · exact isCockadeOn_of_core_exact_of_card_le_six
      hs3 hs6 hnlow hntwo hfree hE
  · exfalso
    exact false_of_core_exact_of_card_ge_seven
      (by omega) hnlow hntwo hfree hE hsmaller

theorem exact_extremal_classification
    (G : SimpleGraph V) (s : Finset V)
    (hs3 : 3 ≤ s.card)
    (hfree : ¬HasThreeSpokeCycleTest G)
    (hE : (edgeSetOn G s).ncard = 2 * s.card - 3) :
    IsCockadeOn G s := by
  apply exact_classification_of_core
    (fun G s hs3 hnlow hntwo hfree hE hsmaller ↦
      isCockadeOn_of_core_exact (G := G) (s := s)
        hs3 hnlow hntwo hfree hE hsmaller)
  exact hs3
  exact hfree
  exact hE

theorem erdos_916_test (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : 2 ≤ Fintype.card V)
    (hE : 2 * Fintype.card V - 2 ≤ G.edgeFinset.card) :
    HasThreeSpokeCycleTest G := by
  classical
  by_cases hV2 : Fintype.card V = 2
  · exfalso
    have hmax := G.card_edgeFinset_le_card_choose_two
    norm_num [hV2] at hE hmax
    omega
  have hV3 : 3 ≤ Fintype.card V := by omega
  apply hasThreeSpokeCycle_of_extremal_classification G hV hE
  intro H hHedges hHfree
  apply exact_extremal_classification H Finset.univ
  · simpa using hV3
  · exact hHfree
  · simpa [edgeSetOn] using hHedges
