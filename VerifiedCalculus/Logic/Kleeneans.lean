/-
Copyright  2025-26  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

import VerifiedCalculus.Logic.TopologicalBasis
import VerifiedCalculus.Logic.Omniscience

namespace Kleenean

/-
syntax "cases_simp_all₂" : tactic
macro_rules
  | `(tactic| cases_simp_all₂ a₁ a₂) =>
      `(tactic| cases a₁ <;> cases a₂; all_goals simp_all)
-/

syntax "intros_cases_simp_all₁" : tactic
macro_rules
  | `(tactic| intros_cases_simp_all₁) =>
      `(tactic| intros a₁; cases a₁; all_goals simp_all)

syntax "intros_cases_simp_all₂" : tactic
macro_rules
  | `(tactic| intros_cases_simp_all₂) =>
      `(tactic| intros a₁ a₂; cases a₁ <;> cases a₂; all_goals simp_all)

syntax "intros_cases_simp_all₄" : tactic
macro_rules
  | `(tactic| intros_cases_simp_all₄) =>
      `(tactic| intros a₁ a₂ a₃ a₄; cases a₁ <;> cases a₂ <;> cases a₃ <;> cases a₄; all_goals simp_all)


private abbrev StdRepr := Repr
private abbrev StdRepr.addAppParen := Repr.addAppParen



inductive Basic : Type where | true | indeterminate | false

instance Basic.instDecidableEq : DecidableEq Basic := by
  intros bk1 bk2; cases bk1 <;> cases bk2 <;> first
    | right; rfl | left; intro; contradiction

def known (b : Bool) : Basic :=
  match b with | .true => Basic.true | .false => Basic.false

def unknown : Basic :=
  Basic.indeterminate

def Basic.definitely (bk : Basic) : Bool :=
  match bk with | true => Bool.true | _ => Bool.false

def Basic.possibly (bk : Basic) : Bool :=
  match bk with | false => Bool.false | _ => Bool.true

theorem Basic.is_not_indeterminate : forall (bk : Basic),
     (bk ≠ .indeterminate) → bk = true ∨ bk = false := by
  intros bk H
  cases bk with
  | true => left; rfl
  | indeterminate => contradiction
  | false => right; rfl


def Basic.refines (bk1 bk2 : Basic) : Prop :=
  match bk2 with | indeterminate => True | _ => bk1 = bk2

theorem Basic.refines_refl : forall bk : Basic,
    refines bk bk := by
  unfold refines; intro bk; cases bk; all_goals simp_all

theorem Basic.refines_trans : forall {bk1 bk3} (bk2 : Basic),
    refines bk1 bk2 → refines bk2 bk3 → refines bk1 bk3 := by
  unfold refines; intros bk1 bk3 bk2; cases bk1 <;> cases bk2 <;> cases bk3; all_goals simp_all

instance Basic.instBasis: TopologicalBasis.Basis Basic where
  refines := Basic.refines
  refines_refl := Basic.refines_refl
  refines_trans := Basic.refines_trans

theorem Basic.refines_true : forall bk, refines bk true -> bk = true := by
  unfold refines; intros bk H; cases bk; all_goals simp_all
theorem Basic.refines_false : forall bk, refines bk false -> bk = false := by
  unfold refines; intros bk H; cases bk; all_goals simp_all
theorem Basic.refines_true_false : forall bk1 bk2,
    (bk1 = true ∨ bk1 = false) → refines bk2 bk1 → bk2 = bk1 := by
  unfold refines; intros bk1 bk2 Htf Hr; cases bk1 <;> cases bk2; all_goals simp_all

syntax "unfold_mono" : tactic
macro_rules
  | `(tactic| unfold_mono) =>
      `(tactic| unfold TopologicalBasis.is_monotone₂ TopologicalBasis.Basis.refines Basic.instBasis; simp only)


private def Basic.implies' (bk1 bk2 : Basic) : Basic :=
  match bk1 with
  | indeterminate =>
      match bk2 with
      | true => true
      | indeterminate => indeterminate
      | false => indeterminate
  | false => true
  | true => bk2

def Basic.implies (bk1 bk2 : Basic) : Basic :=
  match bk1, bk2 with
  | false, _ => true
  | _, true => true
  | true, false => false
  | _, _ => indeterminate

theorem Basic.implies_true : forall (bk1 bk2 : Basic),
    implies bk1 bk2 = true ↔ bk1 = false ∨ bk2 = true := by
  unfold implies; intros_cases_simp_all₂

theorem Basic.implies_false : forall (bk1 bk2 : Basic),
    implies bk1 bk2 = false ↔ bk1 = true ∧ bk2 = false := by
  unfold implies; intros_cases_simp_all₂

theorem Basic.implies_mono : TopologicalBasis.is_monotone₂ Basic.implies := by
  unfold_mono; unfold implies refines; intros_cases_simp_all₄


def Basic.not (bk : Basic) : Basic :=
  match bk with
  | false => true
  | indeterminate => indeterminate
  | true => false

theorem Basic.not_eq_implies_false (bk) : not bk = implies bk false := by
  cases bk; all_goals rfl

theorem Basic.not_not_id : forall (bk : Basic), not (not bk) = bk := by
  unfold not; intros_cases_simp_all₁

theorem Basic.not_true : forall (bk : Basic), not bk = true <-> bk = false := by
  unfold not; intros_cases_simp_all₁

theorem Basic.not_false : forall (bk : Basic), not bk = false <-> bk = true := by
  unfold not; intros_cases_simp_all₁

theorem Basic.not_mono  : TopologicalBasis.is_monotone₁ Basic.not := by
  unfold TopologicalBasis.is_monotone₁ TopologicalBasis.Basis.refines Basic.instBasis; unfold not refines; intros_cases_simp_all₂




def Basic.and (bk1 bk2 : Basic) : Basic :=
  match bk1, bk2 with
  | true, true => true
  | false, _ => false
  | _, false => false
  | _, _ => indeterminate

theorem Basic.and_eq_not_implies_not bk1 bk2 : and bk1 bk2 = not (implies bk1 (not bk2)) := by
  unfold and not implies; cases bk1 <;> cases bk2; all_goals rfl

theorem Basic.and_true : forall bk1 bk2,
    and bk1 bk2 = true ↔ bk1 = true ∧ bk2 = true := by
  unfold and; intros_cases_simp_all₂

theorem Basic.and_false : forall (bk1 bk2 : Basic),
    and bk1 bk2 = false ↔ bk1 = false ∨ bk2 = false := by
  unfold and; intros_cases_simp_all₂

theorem Basic.and_mono : TopologicalBasis.is_monotone₂ Basic.and := by
  unfold_mono; unfold and refines; intros_cases_simp_all₄


def Basic.or (bk1 bk2 : Basic) : Basic :=
  match bk1, bk2 with
  | true, _ => true
  | _, true => true
  | false, false => false
  | _, _ => indeterminate

theorem Basic.or_eq_implies_not bk1 bk2 : or bk1 bk2 = implies (not bk1) bk2 := by
  unfold or not implies; cases bk1 <;> cases bk2; all_goals rfl

theorem Basic.or_true : forall (bk1 bk2 : Basic),
    or bk1 bk2 = true ↔ bk1 = true ∨ bk2 = true := by
  unfold or; intros_cases_simp_all₂

theorem Basic.or_false : forall (bk1 bk2 : Basic),
    or bk1 bk2 = false ↔ bk1 = false ∧ bk2 = false := by
  unfold or; intros_cases_simp_all₂

theorem Basic.or_mono : TopologicalBasis.is_monotone₂ Basic.or := by
  unfold_mono; unfold or refines; intros_cases_simp_all₄


def Basic.iff (bk1 bk2 : Basic) : Basic :=
  match bk1, bk2 with
  | true, true => true
  | false, false => true
  | true, false => false
  | false, true => false
  | _, _ => indeterminate

theorem Basic.iff_eq_and_implies_symm_implies bk1 bk2 :
    iff bk1 bk2 = and (implies bk1 bk2) (implies bk2 bk1) := by
  unfold iff and implies; cases bk1 <;> cases bk2; all_goals rfl

theorem Basic.iff_true : forall (bk1 bk2 : Basic),
    iff bk1 bk2 = true ↔ (bk1 = true ∧ bk2 = true) ∨ (bk1 = false ∧ bk2 = false) := by
  unfold iff; intros_cases_simp_all₂

theorem Basic.iff_false : forall (bk1 bk2 : Basic),
    iff bk1 bk2 = false ↔ (bk1 = false ∧ bk2 = true) ∨ (bk1 = true ∧ bk2 = false) := by
  unfold iff; intros_cases_simp_all₂

theorem Basic.iff_mono : TopologicalBasis.is_monotone₂ Basic.iff := by
  unfold_mono; unfold iff refines; intros_cases_simp_all₄




abbrev is_nested := @TopologicalBasis.is_nested Basic


def Repr := { sq : Nat → Basic // is_nested sq }
def Repr.mk (seq) (nested : is_nested seq) : Repr := Subtype.mk seq nested

abbrev equivalent := @TopologicalBasis.equivalent Basic

@[instance_reducible]
instance has_equiv : HasEquiv Repr :=
  HasEquiv.mk TopologicalBasis.equivalent

private def Repr.cnst (c : Basic) : Subtype is_nested :=
  let seq (_ : Nat) := c
  have mono : is_nested seq := by
    unfold is_nested TopologicalBasis.is_nested seq
    intros m n H
    exact TopologicalBasis.Basis.refines_refl c
  mk seq mono

def Repr.true := cnst .true
def Repr.indeterminate := cnst .indeterminate
def Repr.false := cnst .false

theorem Repr.monotone_true : forall (seq : Nat -> Basic), is_nested seq →
    forall m, (seq m = .true) -> (forall n, m <= n -> seq n = .true) := by
  unfold is_nested; intros seq Hmono m Hm n Hle
  apply Basic.refines_true; rewrite [← Hm]; exact Hmono m n Hle

theorem Repr.monotone_false : forall (seq : Nat -> Basic), is_nested seq →
    forall m, (seq m = .false) -> (forall n, m <= n -> seq n = .false) := by
  unfold is_nested; intros seq Hmono m Hm n Hle
  apply Basic.refines_false; rewrite [← Hm]; exact Hmono m n Hle

theorem Repr.monotone_true_false : forall (seq : Nat -> Basic), is_nested seq →
    forall m, (seq m ≠ Basic.indeterminate) -> (forall n, m <= n -> seq n = seq m) := by
  unfold is_nested; intros seq Hmono m Hm n Hle
  apply Basic.refines_true_false
  . exact Basic.is_not_indeterminate _ Hm
  . exact Hmono m n Hle

def Repr.not (k : Repr) : Repr := TopologicalBasis.Repr.apply_monotone₁ Basic.not Basic.not_mono k

def Repr.implies (k1 k2 : Repr) : Repr := TopologicalBasis.Repr.apply_monotone₂ Basic.implies Basic.implies_mono k1 k2

def Repr.and (k1 k2 : Repr) : Repr := TopologicalBasis.Repr.apply_monotone₂ Basic.and Basic.and_mono k1 k2

def Repr.or (k1 k2 : Repr) : Repr := TopologicalBasis.Repr.apply_monotone₂ Basic.or Basic.or_mono k1 k2

def Repr.iff (k1 k2 : Repr) : Repr := TopologicalBasis.Repr.apply_monotone₂ Basic.or Basic.or_mono k1 k2


abbrev eventually_equal (s1 s2 : Repr) : Prop :=
  TopologicalBasis.eventually_equal s1.val s2.val

local infix:90 " ≡ " => eventually_equal

theorem eventually_equal_instEquivalence : Equivalence eventually_equal :=
  Equivalence.mk
    (fun s ↦ TopologicalBasis.eventually_equal_refl s.val)
    (fun H ↦ TopologicalBasis.eventually_equal_symm H)
    (fun H12 H23 ↦ TopologicalBasis.eventually_equal_trans H12 H23)



private def Repr.known_from' (seq : Nat → Basic) : Nat → Basic :=
  fun n ↦ match n with
  | Nat.zero => seq n
  | Nat.succ m =>
     match known_from' seq m with
     | .indeterminate => seq n
     | _ => known_from' seq m

private theorem Repr.known_from_seq_nested (seq : Nat → Basic)
  : is_nested (known_from' seq) :=
by
  unfold is_nested
  apply (TopologicalBasis.weak_nested_iff_strong_nested _).mp
  intro m
  let km := known_from' seq m; have Ekm : km = known_from' seq m := by rfl
  rw [←Ekm]; unfold known_from'; rw [←Ekm]
  cases km
  · case true => simp; exact Basic.refines_refl .true
  · case indeterminate => simp; exact True.intro
  · case false => simp; exact Basic.refines_refl .false

def Repr.known_from (seq : Nat → Basic) : Repr :=
  Repr.mk (known_from' seq) (known_from_seq_nested seq)


theorem Repr.is_true : forall (k : Repr),
    (exists (m : Nat), k.val m = .true) → k ≡ true := by
  unfold eventually_equal Repr.true Repr.cnst
  intros k Em
  cases Em with | intro m Hm =>
  exists m; exact monotone_true k.val k.property m Hm

theorem Repr.is_false : forall (k : Repr),
    (exists (m : Nat), k.val m = .false) → k ≡ false := by
  unfold eventually_equal Repr.false Repr.cnst; simp
  intros k m Hm
  exists m; exact monotone_false k.val k.property m Hm

theorem Repr.is_true_or_false : forall (k : Repr),
    (exists (m : Nat), k.val m ≠ .indeterminate) → k ≡ true ∨ k ≡ false := by
  unfold eventually_equal
  intros k Em
  cases Em with | intro m Hm =>
  have Hm' := Basic.is_not_indeterminate _ Hm
  have Htf := monotone_true_false k.val k.property m Hm
  cases Hm' with
  | inl Hmt => left; exists m; rw [Hmt] at Htf; unfold true cnst; exact Htf
  | inr Hmf => right; exists m; rw [Hmf] at Htf; unfold false cnst; exact Htf

theorem Repr.is_indeterminate : forall (k : Repr),
    (forall n, k.val n = Basic.indeterminate) → k ≡ Repr.indeterminate := by
  unfold eventually_equal Repr.indeterminate cnst
  intros k Hm; exists 0; simp; assumption


theorem Repr.equivalent_true_implies_eventually_true : forall {k : Repr},
    k ≈ Repr.true → eventually_equal k Repr.true := by
  intros k H; specialize (H .true)
  obtain ⟨Hmp, Hmpr⟩ := H; clear Hmp
  have HE : ∃ n1, TopologicalBasis.Basis.refines (k.val n1) Basic.true := by
    apply Hmpr; exists 0
  obtain ⟨n1, H1⟩ := HE
  exists n1
  intro n Hn
  simp_all only [forall_exists_index]
  unfold Repr.true Repr.cnst Repr.mk; simp
  apply Basic.refines_true
  apply Basic.refines_trans (k.val n1) _ H1
  exact k.property _ _ Hn

theorem Repr.equivalent_false_implies_eventually_false : forall {k : Repr},
    k ≈ Repr.false → eventually_equal k Repr.false := by
  intros k H; specialize (H .false)
  obtain ⟨Hmp, Hmpr⟩ := H; clear Hmp
  have HE : ∃ n1, TopologicalBasis.Basis.refines (k.val n1) Basic.false := by
    apply Hmpr; exists 0
  obtain ⟨n1, H1⟩ := HE
  exists n1
  intro n Hn
  simp_all only [forall_exists_index]
  unfold Repr.false Repr.cnst Repr.mk; simp
  apply Basic.refines_false
  apply Basic.refines_trans (k.val n1) _ H1
  exact k.property _ _ Hn



def setoid : Setoid Repr :=
  Setoid.mk _ TopologicalBasis.equivalent_instEquivalence

def Kleenean := TopologicalBasis.Point Basic
def quot : Kleenean.Repr → Kleenean := Quotient.mk setoid

def true := quot Repr.true
def indeterminate := quot Repr.indeterminate
def false := quot Repr.false

def not (k : Kleenean) : Kleenean := TopologicalBasis.apply_monotone₁ Basic.not Basic.not_mono k

def implies (k1 k2 : Kleenean) : Kleenean := TopologicalBasis.apply_monotone₂ Basic.implies Basic.implies_mono k1 k2

def and (k1 k2 : Kleenean) : Kleenean := TopologicalBasis.apply_monotone₂ Basic.and Basic.and_mono k1 k2

def or (k1 k2 : Kleenean) : Kleenean := TopologicalBasis.apply_monotone₂ Basic.or Basic.or_mono k1 k2

def iff (k1 k2 : Kleenean) : Kleenean := TopologicalBasis.apply_monotone₂ Basic.or Basic.or_mono k1 k2


theorem Repr.cases : LPO -> forall (k : Repr),
    k ≡ .true ∨ k ≡ .indeterminate ∨ k ≡ .false := by
  intro lpo
  intro k
  let P (bk : Basic) := bk ≠ Basic.indeterminate
  let PDec (bk : Basic) : SumBool (P bk) (¬ (P bk)) := by
    exact SumBool.ofDecidable (instDecidableNot)
  let p := fun n : Nat => P (k.val n)
  have pdec := fun n => PDec (k.val n)
  have q := lpo p pdec
  clear lpo pdec PDec
  unfold p at q
  cases q
  . case case1 Epm =>
    have Htf := is_true_or_false k Epm
    cases Htf
    . left; assumption
    . right; right; assumption
  . case case2 Apn =>
    right; left
    apply Repr.is_indeterminate
    intro n
    apply Decidable.of_not_not
    exact Apn n

theorem Repr.classes : LPO -> forall (k : Repr),
  k ≈ Repr.true ∨ k ≈ Repr.indeterminate ∨ k ≈ Repr.false :=
by
  intro lpo k
  have H := Repr.cases lpo k
  cases H
  · case inl Ht =>
      left; exact TopologicalBasis.eventually_equal_implies_equivalent Ht
  · case inr Hif =>
      cases Hif
      · case inl Hi => right; left; exact TopologicalBasis.eventually_equal_implies_equivalent Hi
      · case inr Hf => right; right; exact TopologicalBasis.eventually_equal_implies_equivalent Hf

theorem cases : LPO -> forall (qk : Kleenean),
    qk = true ∨ qk = indeterminate ∨ qk = false := by
  intro lpo
  apply Quotient.ind
  intro k
  have Kc := Repr.classes lpo k
  cases Kc
  . case inl Ht =>
      left
      unfold true
      apply Quotient.sound
      exact Ht
  . case inr Hif =>
      right
      cases Hif
      . case inl Hi =>
        left
        unfold indeterminate
        apply Quotient.sound
        exact Hi
      . case inr Hf =>
        right
        unfold false
        apply Quotient.sound
        exact Hf


private unsafe def Quot.unquot {α : Type} {r : α → α → Prop} : Quot r → α := cast lcProof

instance : StdRepr Kleenean.Basic where
  reprPrec (bk : Basic) _p :=
    match bk with
    | .true => "true"
    | .indeterminate => "indeterminate"
    | .false => "false"

instance : StdRepr Kleenean.Repr where reprPrec (k : Repr) _p :=
  let N := 7; "(Kleenean /- " ++ Std.Format.joinSep ((List.range N).map <| repr ∘ k.val) ", " ++ ", ... -/)"

unsafe instance : StdRepr Kleenean where
  reprPrec k p := let kr : Repr := Quot.unquot k; reprPrec kr p

end Kleenean

abbrev Kleenean := Kleenean.Kleenean
