/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.MTP.Basic

namespace AKE

theorem Matching_prefixWith {A B : Type} (ab : Bool)
    (a a' : A) (t t' : ℕ) (Tb Tb' : Transcript B) :
    Matching ab (Transcript.prefixWith a t Tb) (Transcript.prefixWith a' t' Tb') ↔
      (a = a' ∧ Matching (!ab) Tb Tb' ∧
        List.IsChain (· < ·)
          ((if ab then [t, t'] else [t', t]) ++
            interleave (!ab) ((Tb.entries.map Prod.snd).zip (Tb'.entries.map Prod.snd)))) := by
  have hmap : ∀ (l l' : List (B × ℕ)),
      (l.map fun p => (Sum.inr p.1 : A ⊕ B)) = (l'.map fun p => (Sum.inr p.1 : A ⊕ B)) ↔
        l.map Prod.fst = l'.map Prod.fst := fun l l' => by
    rw [show (fun p : B × ℕ => (Sum.inr p.1 : A ⊕ B)) = Sum.inr ∘ Prod.fst from rfl,
      ← List.map_map, ← List.map_map]
    exact (List.map_injective_iff.mpr Sum.inr_injective).eq_iff
  simp only [Matching, Transcript.prefixWith, List.map_cons, List.map_map, Function.comp_def,
    List.zip_cons_cons, interleave, Sum.inl.injEq, List.cons.injEq, hmap]
  constructor
  · rintro ⟨⟨ha, hm⟩, hc⟩
    exact ⟨ha, ⟨hm, hc.sublist (List.sublist_append_right _ _)⟩, hc⟩
  · rintro ⟨ha, ⟨hm, -⟩, hc⟩
    exact ⟨⟨ha, hm⟩, hc⟩

theorem Matching_prefixWith_intro {A B : Type} (a : A) (t t' : ℕ)
    (Tb Tb' : Transcript B) (hb : Matching true Tb Tb')
    (hc : List.IsChain (· < ·)
      ([t', t] ++ interleave true ((Tb.entries.map Prod.snd).zip (Tb'.entries.map Prod.snd)))) :
    Matching false (Transcript.prefixWith a t Tb) (Transcript.prefixWith a t' Tb') :=
  (Matching_prefixWith false a a t t' Tb Tb').mpr ⟨rfl, hb, by simpa using hc⟩

end AKE
