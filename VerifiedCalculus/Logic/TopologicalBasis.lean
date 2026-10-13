/-
Copyright  2026  Pieter Collins
Released under the GNU GPLv3 as described in the file LICENSE.
Authors: Pieter Collins
-/

import VerifiedCalculus.Logic.Induction

namespace TopologicalBasis

class Basis (B : Type) : Type where
  refines : B → B → Prop
  refines_refl : forall b, refines b b
  refines_trans : forall {b1 b3} (b2), refines b1 b2 → refines b2 b3 → refines b1 b3

local infix:80 " ⊏ " => Basis.refines

class RefinableBasis (B : Type) : Type extends Basis B where
  refinement : B → B → B
  refinement_symm : forall b1 b2, refinement b1 b2 = refinement b2 b1
  refinement_refines_first : forall b1 b2, refines (refinement b1 b2) b1
  refinement_refines_second : forall b1 b2, refines (refinement b1 b2) b2

class ConsistencyBasis (B : Type) : Type extends Basis B where
  inconsistent : B → B → Prop
  refines_consistent : forall b1 b2 b3,
    refines b1 b2 → refines b1 b3 → ¬ inconsistent b2 b3
  inconsistent_refines : forall b1 b2 b3,
    refines b1 b2 → inconsistent b2 b3 → inconsistent b1 b3


section

variable {B : Type}

def eventually_equal (sq1 sq2 : Nat → B) : Prop :=
  ∃ m, ∀ n, m ≤ n → sq1 n = sq2 n

local infix:90 " ≡ " => eventually_equal

theorem eventually_equal_refl : forall s : Nat → B, s ≡ s := by
  intros s; exists 0; intros n Hle; exact Eq.refl (s n)

theorem eventually_equal_symm : forall {s1 s2 : Nat → B}, s1 ≡ s2 → s2 ≡ s1 := by
  unfold eventually_equal; simp
  intros s1 s2 m H12; exists m; intros n Hle
  exact Eq.symm (H12 n Hle)

theorem eventually_equal_trans : forall {s1 s2 s3 : Nat → B}, s1 ≡ s2 → s2 ≡ s3 → s1 ≡ s3 := by
  unfold eventually_equal
  intros s1 s2 s3 H12 H23
  obtain ⟨m12, H12⟩ := H12
  obtain ⟨m23, H23⟩ := H23
  let m13 := max m12 m23; exists m13
  intros n Hm13le
  have Hm12le : m12 <= n := Nat.le_trans (Nat.le_max_left m12 m23) Hm13le
  have Hm23le : m23 <= n := Nat.le_trans (Nat.le_max_right m12 m23) Hm13le
  exact Eq.trans (H12 n Hm12le) (H23 n Hm23le)

theorem eventually_equal_isEquivalence : Equivalence (@eventually_equal B) :=
  Equivalence.mk eventually_equal_refl eventually_equal_symm eventually_equal_trans

end

local infix:90 (name := evEqOp) " ≡ " => eventually_equal



section

variable {B : Type} [Bs : Basis B]

def is_nested (seq : Nat -> B) : Prop :=
  forall (m n : Nat), m <= n -> seq n ⊏ seq m

abbrev NestedSequence {B : Type} [Bs : Basis B] := { sq : Nat → B // is_nested sq }

def is_eventually_nested (seq : Nat -> B) : Prop :=
  forall (n : Nat), exists m, forall l, m <= l -> seq l ⊏ seq n

theorem weak_nested_iff_strong_nested (seq : Nat -> B) :
  (forall (m : Nat), seq (m.succ) ⊏ seq m) ↔
    (forall (m n : Nat), m <= n -> seq n ⊏ seq m) :=
by
  apply Iff.intro
  · intros H m n
    apply Induction.weak_implies_strong_induction
    intro k; apply Bs.refines_trans (seq k)
    · exact H k
    · exact Bs.refines_refl (seq m)
  · intros H m
    exact H m m.succ (Nat.le_succ m)

def is_convergent {B} [Bs : ConsistencyBasis B] (seq : Nat -> B) : Prop :=
  forall b : B, exists n, seq n ⊏ b ∨ exists n, Bs.inconsistent (seq n) b

end


theorem elementwise_op_preserves_eventually_equal₁ {B1 B2 : Type} :
  forall (op : B1 → B2), forall {sq1 sq1' : Nat → B1},
    sq1 ≡ sq1' → (fun n ↦ op (sq1 n)) ≡ (fun n ↦ op (sq1' n)) :=
by
  unfold eventually_equal
  rintro op sq1 sq1' ⟨m, H⟩
  exists m; intros n Hnm; dsimp
  rw [H]; exact Hnm

theorem elementwise_op_preserves_eventually_equal₂ {B1 B2 B3 : Type} :
  forall (op : B1 → B2 → B3), forall {sq1 sq1' : Nat → B1}, forall {sq2 sq2' : Nat → B2},
    sq1 ≡ sq1' → sq2 ≡ sq2' → (fun n ↦ op (sq1 n) (sq2 n)) ≡ (fun n ↦ op (sq1' n) (sq2' n)) :=
by
  unfold eventually_equal
  rintro op sq1 sq1' sq2 sq2' ⟨m1, H1⟩ ⟨m2, H2⟩
  exists max m1 m2; intros n Hnm; dsimp
  rw [H1, H2]
  · exact Nat.le_trans (Nat.le_max_right m1 m2) Hnm
  · exact Nat.le_trans (Nat.le_max_left m1 m2) Hnm


section

variable {B1 : Type} [Bs1 : Basis B1] {B2 : Type} [Bs2 : Basis B2]

def is_monotone₁ (op : B1 → B2) :=
  forall {b1 b1'}, b1' ⊏ b1 → op b1' ⊏ op b1

theorem monotone_op_preserves_nested₁ :
  forall {op : B1 → B2}, is_monotone₁ op →
    forall (sq1 : Nat → B1), is_nested sq1 → is_nested (fun n ↦ op (sq1 n)) :=
by
  intros op Hop sq1 H1
  unfold is_nested
  intros m n Hmn; simp
  exact Hop (H1 m n Hmn)

variable {B3 : Type} [Bs3 : Basis B3]

def is_monotone₂ (op : B1 → B2 → B3) :=
  forall {b1 b2 b1' b2'}, b1' ⊏ b1 → b2' ⊏ b2 → op b1' b2' ⊏ op b1 b2

theorem monotone_op_preserves_nested₂ :
  forall {op : B1 → B2 → B3}, is_monotone₂ op →
    forall (sq1 : Nat → B1) (sq2 : Nat → B2),
      is_nested sq1 → is_nested sq2 → is_nested (fun n ↦ op (sq1 n) (sq2 n)) :=
by
  intros op Hop sq1 sq2 H1 H2
  unfold is_nested
  intros m n Hmn; simp
  exact Hop (H1 m n Hmn) (H2 m n Hmn)

private def apply₁ {α β γ} (op : β → γ) (f : α → β) : α → γ := fun a ↦ op (f a)
private def apply₂ {α β₁ β₂ γ} (op : β₁ → β₂ → γ) (f₁ : α → β₁) (f₂ : α → β₂) : α → γ := fun a ↦ op (f₁ a) (f₂ a)

def Repr.apply_monotone₁ (op : B1 → B2) (Mop : is_monotone₁ op)
    (sq1 : @NestedSequence B1 Bs1) : @NestedSequence B2 Bs2 :=
  Subtype.mk (apply₁ op sq1.val) (monotone_op_preserves_nested₁ Mop _ sq1.property)

def Repr.apply_monotone₂ (op : B1 → B2 → B3) (Mop : is_monotone₂ op)
    (sq1 : @NestedSequence B1 Bs1) (sq2 : @NestedSequence B2 Bs2) : @NestedSequence B3 Bs3 :=
  Subtype.mk (apply₂ op sq1.val sq2.val) (monotone_op_preserves_nested₂ Mop _ _ sq1.property sq2.property)

end


section

variable {B : Type} [Bs : Basis B]

def equivalent (rp1 rp2 : {sq : Nat → B // is_nested sq}) : Prop :=
  ∀ b, (∃ n1, Bs.refines (rp1.val n1) b) ↔ (∃ n2, Bs.refines (rp2.val n2) b)

theorem equivalent_refl : forall s : @NestedSequence B Bs,
    equivalent s s := by
  unfold equivalent
  intro s b; simp

theorem equivalent_symm : forall {s1 s2 : @NestedSequence B Bs},
    equivalent s1 s2 → equivalent s2 s1 := by
  unfold equivalent; simp
  intro s1 H1 s2 H2 H12 b; specialize H12 b
  exact iff_comm.mp H12

theorem equivalent_trans : forall {s1 s2 s3 : @NestedSequence B Bs},
    equivalent s1 s2 → equivalent s2 s3 → equivalent s1 s3 := by
  unfold equivalent; simp
  intros s1 H1 s2 H2 s3 H3 H12 H23 b
  specialize H12 b; specialize H23 b
  exact Iff.trans H12 H23

theorem equivalent_instEquivalence : Equivalence (@equivalent B Bs) :=
  Equivalence.mk equivalent_refl equivalent_symm equivalent_trans


theorem eventually_equal_implies_equivalent : forall {s1 s2 : @NestedSequence B Bs},
  eventually_equal s1.val s2.val → equivalent s1 s2 :=
by
  unfold eventually_equal equivalent
  intros k1 k2 H  b; obtain ⟨m, H⟩ := H
  apply Iff.intro
  · rintro ⟨n1, H1⟩
    let n2 := max m n1; exists n2
    rw [← H _ (Nat.le_max_left m n1)]
    apply Bs.refines_trans (k1.val n1) _ H1
    exact k1.property n1 _ (Nat.le_max_right m n1)
  · rintro ⟨n2, H2⟩
    let n1 := max m n2; exists n1
    rw [H _ (Nat.le_max_left m n2)]
    apply Bs.refines_trans (k2.val n2) _ H2
    exact k2.property n2 _ (Nat.le_max_right m n2)

end


/- Do we need this? -/
instance E {B : Type} [Bs : Basis B] : HasEquiv (@NestedSequence B Bs) := { Equiv := fun sq sq' ↦ equivalent sq sq' }

def setoid {B : Type} [Bs : Basis B] : Setoid (@NestedSequence B Bs) := Setoid.mk _ equivalent_instEquivalence


section

variable {B1 : Type} [Bs1 : Basis B1] {B2 : Type} [Bs2 : Basis B2] {B3 : Type} [Bs3 : Basis B3]

private theorem elementwise_op_preserves_equivalence_unidirectional₁ :
  forall {op : B1 → B2} (Mop : is_monotone₁ op),
    forall {sq1 sq1' : @NestedSequence B1 Bs1},
      sq1 ≈ sq1' →
        let sq2 := Repr.apply_monotone₁ op Mop sq1
        let sq2' := Repr.apply_monotone₁ op Mop sq1'
          forall b2, (∃ n2, sq2.val n2 ⊏ b2) → (∃ n2', sq2'.val n2' ⊏ b2) :=
by
  unfold Repr.apply_monotone₁ apply₁; simp
  intro op Mop sq1 M1 sq1' M1' E1  b2  n2 H2
  specialize E1 (sq1 n2)
  have R1 : ∃ n1, sq1 n1 ⊏ sq1 n2 := by exists n2; exact Basis.refines_refl (sq1 n2)
  have R1' := E1.mp R1; obtain ⟨n1', R1'⟩ := R1'; clear E1 R1
  let n2' := n1'; exists n2'
  apply Bs2.refines_trans _ _ H2
  apply Mop
  · apply Bs1.refines_trans _ _ R1'; apply M1'; exact Nat.le_refl n1'

theorem elementwise_op_preserves_equivalence₁ : forall {op : B1 → B2} (Mop : is_monotone₁ op),
  forall {sq1 sq1' : @NestedSequence B1 Bs1},
    sq1 ≈ sq1' → Repr.apply_monotone₁ op Mop sq1 ≈ Repr.apply_monotone₁ op Mop sq1' :=
by
  intro op Mop sq1 sq1' E1
  intro b2
  apply Iff.intro
  · exact elementwise_op_preserves_equivalence_unidirectional₁ Mop E1 _
  · apply elementwise_op_preserves_equivalence_unidirectional₁ Mop (equivalent_symm E1) _


private theorem elementwise_op_preserves_equivalence_unidirectional₂ :
  forall {op : B1 → B2 → B3} (Mop : is_monotone₂ op),
    forall {sq1 sq1' : @NestedSequence B1 Bs1} {sq2 sq2' : @NestedSequence B2 Bs2},
      sq1 ≈ sq1' → sq2 ≈ sq2' →
        let sq3 := Repr.apply_monotone₂ op Mop sq1 sq2
        let sq3' := Repr.apply_monotone₂ op Mop sq1' sq2'
          forall b3, (∃ n3, sq3.val n3 ⊏ b3) → (∃ n3', sq3'.val n3' ⊏ b3) :=
by
  unfold Repr.apply_monotone₂ apply₂; simp
  intro op Mop sq1 M1 sq1' M1' sq2 M2 sq2' M2' E1 E2  b3  n3 H3
  specialize E1 (sq1 n3); specialize E2 (sq2 n3)
  have R1 : ∃ n1, sq1 n1 ⊏ sq1 n3 := by exists n3; exact Basis.refines_refl (sq1 n3)
  have R1' := E1.mp R1; obtain ⟨n1', R1'⟩ := R1'; clear E1 R1
  have R2 : ∃ n2, sq2 n2 ⊏ sq2 n3 := by exists n3; exact Basis.refines_refl (sq2 n3)
  have R2' := E2.mp R2; obtain ⟨n2', R2'⟩ := R2'; clear E2 R2
  let n3' := max n1' n2'; exists n3'
  apply Bs3.refines_trans _ _ H3
  apply Mop
  · apply Bs1.refines_trans _ _ R1'; apply M1'; exact Nat.le_max_left n1' n2'
  · apply Bs2.refines_trans _ _ R2'; apply M2'; exact Nat.le_max_right n1' n2'

theorem elementwise_op_preserves_equivalence₂ : forall {op : B1 → B2 → B3} (Mop : is_monotone₂ op),
  forall {sq1 sq1' : @NestedSequence B1 Bs1} {sq2 sq2' : @NestedSequence B2 Bs2},
    sq1 ≈ sq1' → sq2 ≈ sq2' → Repr.apply_monotone₂ op Mop sq1 sq2 ≈ Repr.apply_monotone₂ op Mop sq1' sq2' :=
by
  intro op Mop sq1 sq1' sq2 sq2' E1 E2
  intro b3
  apply Iff.intro
  · exact elementwise_op_preserves_equivalence_unidirectional₂ Mop E1 E2 _
  · apply elementwise_op_preserves_equivalence_unidirectional₂ Mop
    exact equivalent_symm E1; exact equivalent_symm E2

end


abbrev Point (B : Type) [Bs : Basis B] := Quotient (Setoid.mk _ (@equivalent_instEquivalence B Bs))

section

variable {B1 : Type} [Bs1 : Basis B1] {B2 : Type} [Bs2 : Basis B2] {B3 : Type} [Bs3 : Basis B3]

def apply_monotone₁
  (op : B1 → B2) (Mop : TopologicalBasis.is_monotone₁ op)
    (p1 : Point B1) : Point B2 :=
  let f := fun p ↦ Quotient.mk _ (Repr.apply_monotone₁ op Mop p)
  let H := fun _pr _pr' HE ↦ Quotient.sound (elementwise_op_preserves_equivalence₁ Mop HE)
  Quotient.lift f H p1

def apply_monotone₂
  (op : B1 → B2 → B3) (Mop : TopologicalBasis.is_monotone₂ op)
    (p1 : Point B1) (p2 : Point B2) : Point B3 :=
  let f := fun p1 p2 ↦ Quotient.mk _ (Repr.apply_monotone₂ op Mop p1 p2)
  have H := fun _pr1 _pr2 _pr1' _pr2' HE1 HE2 ↦
    Quotient.sound (elementwise_op_preserves_equivalence₂ Mop HE1 HE2)
  Quotient.lift₂ f H p1 p2

end

end TopologicalBasis
