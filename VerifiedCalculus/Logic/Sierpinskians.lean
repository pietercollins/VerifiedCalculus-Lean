/-
Copyright  2025-26  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

import VerifiedCalculus.Logic.TopologicalBasis
import VerifiedCalculus.Logic.Omniscience

namespace Sierpinksian

inductive Basic : Type where | true | indeterminate

instance Basic.instDecidableEq : DecidableEq Basic := by
  intros bs1 bs2; cases bs1; all_goals cases bs2; all_goals
    first | right; rfl | left; intro; contradiction

def definitely (bs : Basic) : Bool :=
  match bs with | .true => Bool.true | _ => Bool.false

theorem Basic.not_indeterminate : forall (bs : Basic),
     (bs ≠ .indeterminate) → bs = true := by
  intros bs H; cases bs with | true => rfl | indeterminate => contradiction


def refines (bs1 bs2 : Basic) : Prop :=
  match bs2 with | .indeterminate => True | _ => bs1 = bs2

theorem refines_refl : forall bs, refines bs bs := by
  unfold refines; intro bs; cases bs; all_goals simp

theorem refines_trans : forall {bs1 bs3} (bs2), refines bs1 bs2 → refines bs2 bs3 → refines bs1 bs3 := by
  unfold refines; intro bs1 bs3 bs2; cases bs1 <;> cases bs2 <;> cases bs3; all_goals simp

instance Basic.instBasis : TopologicalBasis.Basis Basic where
  refines := refines
  refines_refl := refines_refl
  refines_trans := refines_trans

theorem Basic.refines_true : forall bs, refines bs true -> bs = true := by
  unfold refines; intros bs H; cases bs; all_goals simp_all


abbrev is_nested := @TopologicalBasis.is_nested Basic

def Repr := { sq : Nat → Basic // is_nested sq }
def Repr.mk (seq) (nested : is_nested seq) : Repr := Subtype.mk seq nested

/-
abbrev equivalent := @TopologicalBasis.equivalent Basic Basic.instBasis
-/

@[instance_reducible]
instance has_equiv : HasEquiv Repr :=
  HasEquiv.mk TopologicalBasis.equivalent

private def Repr.cnst (c : Basic) : Subtype is_nested :=
  let seq (_ : Nat) := c
  have nested : is_nested seq := by
    unfold is_nested TopologicalBasis.is_nested seq
    intros m n H
    exact TopologicalBasis.Basis.refines_refl c
  mk seq nested

def Repr.true := cnst .true
def Repr.indeterminate := cnst .indeterminate

theorem monotone_true : forall (seq : Nat -> Basic), is_nested seq →
    forall m, (seq m = .true) -> (forall n, m <= n -> seq n = .true) := by
  unfold is_nested; intros seq Hmono m Hm n Hle
  apply Basic.refines_true; rewrite [← Hm]; exact Hmono m n Hle


abbrev eventually_equal (s1 s2 : Repr) : Prop :=
  TopologicalBasis.eventually_equal s1.val s2.val

local infix:90 " ≡ " => eventually_equal

theorem eventually_equal_instEquivalence : Equivalence eventually_equal :=
  Equivalence.mk
    (fun s ↦ TopologicalBasis.eventually_equal_refl s.val)
    (fun H ↦ TopologicalBasis.eventually_equal_symm H)
    (fun H12 H23 ↦ TopologicalBasis.eventually_equal_trans H12 H23)


def setoid : Setoid Repr :=
  Setoid.mk _ TopologicalBasis.equivalent_instEquivalence

def Sierpinskian := TopologicalBasis.Point Basic
def quot : Repr → Sierpinskian := Quotient.mk setoid

def true := quot Repr.true
def indeterminate := quot Repr.indeterminate



private def true_from' (seq : Nat → Basic) : Nat → Basic :=
  fun n ↦ match n with
  | Nat.zero => seq n
  | Nat.succ m =>
     match true_from' seq m with
     | .indeterminate => seq n
     | _ => true_from' seq m

private theorem Repr.true_from_nested' (seq : Nat → Basic)
  : is_nested (true_from' seq) :=
by
  unfold is_nested
  apply (TopologicalBasis.weak_nested_iff_strong_nested _).mp
  intro m
  let sm := true_from' seq m; have Esm : sm = true_from' seq m := by rfl
  rw [←Esm]; unfold true_from'; rw [←Esm]
  cases sm
  · case true => simp; exact refines_refl .true
  · case indeterminate => simp; exact True.intro

def Repr.true_from (s : Nat → Basic) : Repr :=
  mk _ (true_from_nested' s)


theorem Repr.when_true : forall (s : Repr),
    (∃ m, s.val m = .true) → s ≡ .true := by
  unfold  true cnst
  intro s Em
  obtain ⟨m, Hm⟩ := Em
  exists m; exact monotone_true s.val s.property m Hm

theorem Repr.when_indeterminate : forall (s : Repr),
    (forall n, s.val n = .indeterminate) → s ≡ .indeterminate := by
  unfold Repr.indeterminate cnst
  intros s Hm; exists 0; simp; assumption



theorem Repr.equivalent_true_implies_eventually_true : forall {s : Repr},
    s ≈ Repr.true → s ≡ Repr.true := by
  intros s H; specialize (H .true)
  obtain ⟨Hmp, Hmpr⟩ := H; clear Hmp
  have HE : ∃ n1, TopologicalBasis.Basis.refines (s.val n1) Basic.true := by
    apply Hmpr; exists 0
  obtain ⟨n1, H1⟩ := HE
  exists n1
  intro n Hn
  have P := s.property n1 n Hn
  have R : refines (s.val n) Basic.true := by
    exact refines_trans (s.val n1) P H1
  exact Basic.refines_true (s.val n) R



theorem Repr.cases : LPO -> forall (s : Repr),
    s ≡ .true ∨ s ≡ .indeterminate := by
  intro lpo
  intro s
  let P (bs : Basic) := bs ≠ Basic.indeterminate
  let PDec (bs : Basic) : SumBool (P bs) (¬ (P bs)) := by
    exact SumBool.ofDecidable (instDecidableNot)
  let p := fun n : Nat => P (s.val n)
  have pdec := fun n => PDec (s.val n)
  have q := lpo p pdec
  clear lpo pdec PDec
  unfold p at q
  cases q
  · case case1 Epm =>
    left
    apply Repr.when_true
    cases Epm with | intro n Hn =>
    exists n
    exact Basic.not_indeterminate (s.val n) Hn
  · case case2 Apn =>
    right
    apply Repr.when_indeterminate
    intro n
    apply Decidable.of_not_not
    exact Apn n


theorem Repr.classes : LPO -> forall (s : Repr),
    s ≈ Repr.true ∨ s ≈ Repr.indeterminate := by
  intro lpo s
  have H := cases lpo s
  cases H
  · case inl Ht => left; exact TopologicalBasis.eventually_equal_implies_equivalent Ht
  · case inr Hi => right; exact TopologicalBasis.eventually_equal_implies_equivalent Hi

theorem cases : LPO -> forall (qs : Sierpinskian),
    qs = true ∨ qs = indeterminate := by
  intro lpo
  apply Quotient.ind
  intro s
  have Kc := Repr.classes lpo s
  cases Kc
  . case inl Ht =>
      left
      unfold true
      apply Quotient.sound
      exact Ht
  . case inr Hif =>
      right
      unfold indeterminate
      apply Quotient.sound
      exact Hif



private abbrev Repr.apply_mono₂ (op : Basic → Basic → Basic) (Mop : TopologicalBasis.is_monotone₂ op) (s1 s2 : Repr) : Repr :=
  TopologicalBasis.Repr.apply_monotone₂ op Mop s1 s2

private abbrev apply_mono₂ (op : Basic → Basic → Basic) (Mop : TopologicalBasis.is_monotone₂ op) (s1 s2 : Sierpinskian) : Sierpinskian :=
  TopologicalBasis.apply_monotone₂ op Mop s1 s2


def Basic.and (bs1 bs2 : Basic) : Basic :=
 match bs1, bs2 with
  | true, true => true
  | _, _ => indeterminate

theorem Basic.and_mono : TopologicalBasis.is_monotone₂ Basic.and := by
  unfold TopologicalBasis.is_monotone₂ TopologicalBasis.Basis.refines Basic.instBasis; simp only
  unfold and refines
  intro r1 r2 s1 s2
  cases r1 <;> cases r2 <;> cases s1 <;> cases s2; all_goals simp_all

def Repr.and (s1 s2 : Repr) : Repr :=
  let seq := fun n ↦ Basic.and (s1.val n) (s2.val n)
  have nested := TopologicalBasis.monotone_op_preserves_nested₂ Basic.and_mono _ _ s1.property s2.property
  mk seq nested

def and (s1 s2 : Sierpinskian) : Sierpinskian :=
  let f (s1 s2) := quot (Repr.and s1 s2)
  have H (s1 s2 s1' s2' : Repr) : s1 ≈ s1' → s2 ≈ s2' → f s1 s2 = f s1' s2' :=
    fun H1 H2 ↦ Quotient.sound (TopologicalBasis.elementwise_op_preserves_equivalence₂ Basic.and_mono H1 H2)
  Quotient.lift₂ f H s1 s2


def Basic.or (bs1 bs2 : Basic) : Basic :=
 match bs1, bs2 with
  | indeterminate, indeterminate => indeterminate
  | _, _ => true

theorem Basic.or_mono : TopologicalBasis.is_monotone₂ Basic.or := by
  unfold TopologicalBasis.is_monotone₂ TopologicalBasis.Basis.refines Basic.instBasis; simp only
  unfold or refines
  intros r1 r2 s1 s2; cases r1 <;> cases r2 <;> cases s1 <;> cases s2; all_goals simp_all

def Repr.or (s1 s2 : Repr) : Repr :=
  let seq := fun n ↦ Basic.or (s1.val n) (s2.val n)
  have nested := TopologicalBasis.monotone_op_preserves_nested₂ Basic.or_mono _ _ s1.property s2.property
  mk seq nested

def or (s1 s2 : Sierpinskian) : Sierpinskian :=
  let f (s1 s2) := quot (Repr.or s1 s2)
  have H (s1 s2 s1' s2' : Repr) : s1 ≈ s1' → s2 ≈ s2' → f s1 s2 = f s1' s2' :=
    fun H1 H2 ↦ Quotient.sound (TopologicalBasis.elementwise_op_preserves_equivalence₂ Basic.or_mono H1 H2)
  Quotient.lift₂ f H s1 s2


theorem Basic.and_true : forall (bs1 bs2 : Basic),
    and bs1 bs2 = true ↔ bs1 = true ∧ bs2 = true := by
  unfold and; intros bs1 bs2; cases bs1; all_goals cases bs2; all_goals simp_all

theorem Repr.and_true' : forall {s1 s2 : Repr},
  and s1 s2 ≡ true ↔ s1 ≡ true ∧ s2 ≡ true :=
by
  intro s1 s2
  obtain ⟨sq1, M1⟩ := s1
  obtain ⟨sq2, M2⟩ := s2
  unfold and true cnst mk; dsimp
  unfold eventually_equal; dsimp
  apply Iff.intro
  · intro H; obtain ⟨m, H⟩ := H;
    constructor
    · exists m; intro n Hmn; specialize H n Hmn
      exact ((Basic.and_true _ _).mp H).left
    · exists m; intro n Hmn; specialize H n Hmn
      exact ((Basic.and_true _ _).mp H).right
  · intro H12; have H1 := H12.left; have H2 := H12.right; clear H12
    obtain ⟨m1, H1⟩ := H1; obtain ⟨m2, H2⟩ := H2
    let m := max m1 m2; exists m; intro n Hmn
    apply (Basic.and_true _ _).mpr
    constructor
    · apply H1; apply Nat.le_trans _ Hmn; exact Nat.le_max_left m1 m2
    · apply H2; apply Nat.le_trans _ Hmn; exact Nat.le_max_right m1 m2

theorem Repr.and_true : forall (s1 s2 : Repr),
  and s1 s2 ≈ true ↔ s1 ≈ true ∧ s2 ≈ true :=
by
  intro s1 s2
  apply Iff.intro
  · intro H;
    have HE := equivalent_true_implies_eventually_true H
    have HA := Repr.and_true'.mp HE
    apply And.intro <;> apply TopologicalBasis.eventually_equal_implies_equivalent
    · exact HA.left
    · exact HA.right
  · intro H12; have H1 := H12.left; have H2 := H12.right; clear H12
    apply TopologicalBasis.eventually_equal_implies_equivalent
    apply and_true'.mpr
    apply And.intro <;> apply equivalent_true_implies_eventually_true
    · exact H1
    · exact H2

theorem and_true : forall (s1 s2 : Sierpinskian), and s1 s2 = true ↔ s1 = true ∧ s2 = true := by
  intro s1 s2;
  unfold true quot
  apply @Quotient.inductionOn₂ _ _ _ _ _ s1 s2
  intro sr1 sr2
  apply Iff.intro
  · intros H12
    have E12 := (Repr.and_true sr1 sr2).mp (Quotient.exact H12)
    obtain ⟨E1,E2⟩ := E12
    exact And.intro (Quotient.sound E1) (Quotient.sound E2)
  · intro H12; obtain ⟨H1,H2⟩ := H12
    apply Quotient.sound; apply (Repr.and_true sr1 sr2).mpr
    exact And.intro (Quotient.exact H1) (Quotient.exact H2)


theorem Basic.or_true : forall (bs1 bs2 : Basic),
    or bs1 bs2 = true ↔ bs1 = true ∨ bs2 = true := by
  unfold or; intros bs1 bs2; cases bs1; all_goals cases bs2; all_goals simp_all

theorem Repr.or_true' : forall {s1 s2 : Repr},
  or s1 s2 ≡ true ↔ s1 ≡ true ∨ s2 ≡ true :=
by
  intro s1 s2
  obtain ⟨sq1, M1⟩ := s1
  obtain ⟨sq2, M2⟩ := s2
  unfold or true cnst mk; dsimp
  unfold eventually_equal; dsimp
  apply Iff.intro
  · intro H; obtain ⟨m, H⟩ := H; simp_all
    have Hm := (Basic.or_true _ _).mp (H m (Nat.le_refl m))
    cases Hm with
    | inl H1 => left; exists m; exact monotone_true sq1 M1 m H1
    | inr H2 => right; exists m; exact monotone_true sq2 M2 m H2
  · intro H;
    cases H with
    | inl H1 =>
        obtain ⟨m,H1⟩ := H1; exists m; intros n Hmn; specialize H1 n Hmn
        apply (Basic.or_true _ _).mpr; left; exact H1
    | inr H2 =>
        obtain ⟨m,H2⟩ := H2; exists m; intros n Hmn; specialize H2 n Hmn
        apply (Basic.or_true _ _).mpr; right; exact H2

theorem Repr.or_true : forall (s1 s2 : Repr),
  or s1 s2 ≈ true ↔ s1 ≈ true ∨ s2 ≈ true :=
by
  intro s1 s2
  apply Iff.intro
  · intro H;
    have HE := equivalent_true_implies_eventually_true H
    have HA := Repr.or_true'.mp HE
    cases HA with
    | inl H1 => left; exact TopologicalBasis.eventually_equal_implies_equivalent H1
    | inr H2 => right; exact TopologicalBasis.eventually_equal_implies_equivalent H2
  · intro H12; cases H12 with
    | inl H1 =>
        apply TopologicalBasis.eventually_equal_implies_equivalent
        apply or_true'.mpr
        left
        exact equivalent_true_implies_eventually_true H1
    | inr H2 =>
        apply TopologicalBasis.eventually_equal_implies_equivalent
        apply or_true'.mpr
        right
        exact equivalent_true_implies_eventually_true H2


theorem or_true : forall (s1 s2 : Sierpinskian), or s1 s2 = true ↔ s1 = true ∨ s2 = true := by
  intro s1 s2;
  unfold true quot
  apply @Quotient.inductionOn₂ _ _ _ _ _ s1 s2
  intro sr1 sr2
  apply Iff.intro
  · intros H12
    have E12 := (Repr.or_true sr1 sr2).mp (Quotient.exact H12)
    cases E12 with
    | inl H1 => left; exact Quotient.sound H1
    | inr H2 => right; exact Quotient.sound H2
  · intro H12
    apply Quotient.sound; apply (Repr.or_true sr1 sr2).mpr
    cases H12 with
    | inl H1 => left; exact Quotient.exact H1;
    | inr H2 => right; exact Quotient.exact H2;

end Sierpinksian


abbrev Sierpinksian := Sierpinksian.Sierpinskian
