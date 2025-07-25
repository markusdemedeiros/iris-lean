/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros, Alexander Bai
-/

import Iris.Instances.UPred
import Iris.BI
import Iris.Algebra.Frac
import Iris.Algebra.DFrac
import Iris.Algebra.CMRA


/-! # The reverse direction of bupd_sep does not hold
Counterexample courtesy of Alexander Bai -/

section BupdSepCounterexample

open Iris
open Iris.BI.BIBase

def SepBupd [BI PROP] [BIUpdate PROP] (P Q : PROP) : Prop :=
    iprop(|==> (P ∗ Q) ⊢ (|==> P) ∗ (|==> Q))


local instance : UCMRA (LeibnizO Nat) where
  pcore n := some ⟨0⟩
  op x y := ⟨x.1 + y.1⟩
  ValidN _ x := x.1 % 2 = 0
  Valid x := x.1 % 2 = 0
  op_ne.ne := sorry -- Leibniz
  pcore_ne := sorry --OK
  validN_ne := by sorry -- Leibniz
  valid_iff_validN := by simp
  validN_succ := by simp
  validN_op_left := by sorry -- Not. All sub-states must be valid.
  assoc := sorry
  comm := sorry
  pcore_op_left := sorry -- True
  pcore_idem := sorry -- True
  pcore_op_mono := sorry -- True
  extend := sorry
  unit := ⟨0⟩
  unit_valid := by simp -- Unit must always be valud
  unit_left_id := sorry -- True
  pcore_unit := sorry -- pcore must always exist for unit


inductive MyAuth where
| auth (x : Nat)
| frag (x : Nat)
| invalid

@[simp] def MyAuth.pcore : MyAuth → Option MyAuth
| auth x  => some (frag x)
| frag x  => some (frag x)
| invalid => none

@[simp] def MyAuth.op : MyAuth → MyAuth → MyAuth
| invalid, _ => invalid
| _, invalid => invalid
| auth _, auth _ => invalid
| auth x, frag y => if x = y then auth x else invalid
| frag x, auth y => if x = y then auth x else invalid
| frag x, frag y => frag (x + y)

@[simp] def MyAuth.valid : MyAuth → Prop
| auth _  => True
| frag _  => True
| invalid => False


local instance : OFE MyAuth where
  Equiv x y := x = y
  Dist _ x y := x = y
  dist_eqv := fun {n} => Eq_Equivalence
  equiv_dist := by exact fun {x y} => Iff.symm (forall_const Nat)
  dist_lt := by exact fun {n} {x y} {m} a a_1 => a


local instance : UCMRA MyAuth where
  pcore := MyAuth.pcore
  op := MyAuth.op
  ValidN _ := MyAuth.valid
  Valid := MyAuth.valid
  op_ne.ne _ _ _ H := H ▸ rfl
  pcore_ne {_ _ x _} := by
    simp
    intro H; rw [H]
    cases x <;> simp
    all_goals intro H; rw [H]
  validN_ne H := by
    rw [H]
    exact id
  valid_iff_validN := by
    intro x
    cases x <;> simp
  validN_succ := by simp
  validN_op_left := by
    intro _ x y
    cases x <;> cases y <;> simp
  assoc := by
    intro x y z
    cases x <;> cases y <;> cases z <;> simp
    · rename_i x y z
      if h : y = z
        then sorry
        else sorry
    -- Reasonably sure this is true
    all_goals sorry
  comm := sorry -- Def true
  pcore_op_left {x cx} := by
    cases x <;> simp <;> intro H <;> simp [H.symm]
    sorry -- True
  pcore_idem := sorry -- True
  pcore_op_mono := sorry -- True
  extend := sorry
  unit := sorry
  unit_valid := by sorry
  unit_left_id := sorry -- True
  pcore_unit := sorry -- pcore must always exist for unit







/-
-- TODO: replace by  Numbers CMRA when is merged
local instance : UCMRA (LeibnizO Nat) where
  pcore n := n
  op x y := ⟨x.1 + y.1⟩
  ValidN _ _ := True
  Valid _ := True
  op_ne.ne := sorry
  pcore_ne := sorry
  validN_ne := by simp
  valid_iff_validN := by simp
  validN_succ := by simp
  validN_op_left := by simp
  assoc := sorry
  comm := sorry
  pcore_op_left := sorry
  pcore_idem := sorry
  pcore_op_mono := sorry
  extend := sorry
  unit := ⟨0⟩
  unit_valid := by simp
  unit_left_id := sorry
  pcore_unit := sorry


theorem not_bupd_sep : ¬(sep_bupd_def (PROP := UPred (LeibnizO Nat)) (UPred.ownM ⟨1⟩) (UPred.ownM ⟨2⟩)) := by
  intro H
  have H := H 0 ⟨3⟩ trivial ?G
  case G =>
    rintro k ⟨y⟩ ⟨rfl⟩ _
    exists ⟨3 + y⟩
    refine ⟨trivial, ?_⟩
    simp [BI.sep, UPred.sep]
    exists ⟨1⟩
    exists ⟨2 + y⟩
    refine ⟨?_, ?_, ?_⟩
    · simp [CMRA.op]; congr 1; omega
    · exists ⟨0⟩
    · exists ⟨y⟩
  simp [BI.sep, UPred.sep] at H
  -- let H1 : ((UPred.bupd iprop(UPred.ownM { car := 1 } ∗ UPred.ownM { car := 2 })) : UPred (LeibnizO Nat)) := sorry
  sorry
  -/







/-

theorem not_bupd_sep : ¬(sep_bupd_def (PROP := UPred (LeibnizO Nat)) (UPred.ownM ⟨1⟩) (UPred.ownM ⟨1⟩)) := by
  intro H
  have H := H 0 ⟨1⟩ sorry ?G
  case G =>
    rintro k ⟨y⟩ ⟨rfl⟩ _
    exists ⟨1 + y⟩
    obtain ⟨rfl⟩ : y = 0 := by cases y <;> simp_all [CMRA.ValidN, CMRA.op]; omega
    sorry
    -- exists ⟨1 + y⟩
    -- refine ⟨trivial, ?_⟩
    -- simp [BI.sep, UPred.sep]
    -- exists ⟨1⟩
    -- exists ⟨2 + y⟩
    -- refine ⟨?_, ?_, ?_⟩
    -- · simp [CMRA.op]; congr 1; omega
    -- · exists ⟨0⟩
    -- · exists ⟨y⟩
  simp [BI.sep, UPred.sep] at H
  -- let H1 : ((UPred.bupd iprop(UPred.ownM { car := 1 } ∗ UPred.ownM { car := 2 })) : UPred (LeibnizO Nat)) := sorry
  sorry



-/
theorem bupd_sep [UCMRA M] {m1 m2 : M} : ¬ SepBupd (PROP := UPred M) (UPred.ownM m1) (UPred.ownM m2) := by
  intro H
  simp only [SepBupd, BI.sep, UPred.sep, BUpd.bupd, UPred.bupd, BI.Entails, UPred.Entails, UPred.ownM] at H


  -- intro H'
  -- suffices
  -- ¬(∀ x1 x2, ¬ (m ≡{n}≡ x1 • x2 ∧
  --     (∀ (k : Nat) (yf : M), k ≤ n → ✓{k} x1 • yf → ∃ x', ✓{k} x' • yf ∧ P.holds k x') ∧
  --       ∀ (k : Nat) (yf : M), k ≤ n → ✓{k} x2 • yf → ∃ x', ✓{k} x' • yf ∧ Q.holds k x')) by
  --   apply Classical.not_forall_not.mp
  --   intro H
  --   apply this
  --   intro x1 x2 HK
  --   apply (H x1)
  --   exists x2
  -- intro H
  -- have H'' := H' n UCMRA.unit (by omega) ?G
  -- case G =>
  --   apply CMRA.validN_ne
  --   · apply OFE.Dist.symm (CMRA.unit_right_id_dist m)
  --   · apply Hv
  -- rcases H'' with ⟨x', Hx'⟩
  -- simp only [not_and] at H
  sorry


  /-

  -- The sus part is that we have to be able to prove that we can split the state here.
  -- What I did below seems so close to working, but it does not, because we can't split the
  -- state up beforehand.
  apply Classical.not_forall_not.mp ?_
  intro H1
  apply (H1 m)
  exists UCMRA.unit
  refine ⟨OFE.Dist.symm (CMRA.unit_right_id_dist m), ?_⟩
  refine forall_and.mp (fun k => ?_)
  refine forall_and.mp (fun yf => ?_)
  refine forall_and.mp (fun Hk => ?_)
  refine ⟨?_, ?_⟩
  · intro H1
    obtain ⟨z, ⟨Hz, a, b, H2, H3, H4⟩⟩ := H' k yf Hk H1
    exists a
    refine ⟨?_, H3⟩
    apply CMRA.validN_op_left (y := b)
    apply CMRA.validN_ne _ Hz
    -- True
    sorry
  · intro Hv
    have X := H' k UCMRA.unit Hk sorry
    sorry
  -/
/-


inductive Diamond where | Bot | Lft | Rgt | Top | Err

def Diamond.op : Diamond → Diamond → Diamond
| Err, _ => Err
| _, Err => Err
| Bot, x   => x
| x, Bot   => x
| Top, _   => Err
| _ , Top  => Err
| Rgt, Rgt => Err
| Lft, Lft => Err
| Lft, Rgt => Top
| Rgt, Lft => Top

/-
local instance : UCMRA (LeibnizO Diamond) where
  pcore n := some ⟨Diamond.Bot⟩
  op x y := ⟨Diamond.op x.1 y.1⟩
  ValidN n x := ¬ x = ⟨.Err⟩
  Valid x := ¬ x = ⟨.Err⟩
  op_ne.ne := by
    intro n x y H
    rw [H]
  pcore_ne := fun _ H => by exact exists_eq_right'.mpr H
  validN_ne := by
    intro n x y H
    rw [H]
    exact id
  valid_iff_validN := by simp
  validN_succ := by simp
  validN_op_left := by intro n x y H; rcases x with ⟨⟨_⟩⟩ <;> rcases y with ⟨⟨_⟩⟩ <;> simp_all [Diamond.op]
  assoc := by
    intro x y z
    rcases x with ⟨⟨_⟩⟩ <;> rcases y with ⟨⟨_⟩⟩ <;> rcases z with ⟨⟨_⟩⟩ <;>  simp_all [Diamond.op]
  comm := by
    intro x y
    rcases x with ⟨⟨_⟩⟩ <;> rcases y with ⟨⟨_⟩⟩ <;> simp_all [Diamond.op]
  pcore_op_left := by
    rintro ⟨x⟩ ⟨cx⟩ ⟨rfl⟩
    rcases x <;> simp [Diamond.op]
  pcore_idem := by rintro _ _ H; rw [H.symm]
  pcore_op_mono := by
    rintro ⟨x⟩ ⟨cx⟩ H y
    exists ⟨Diamond.Bot⟩
    rw [H]
    simp
    cases cx <;> simp [Diamond.op]
  extend := by
    intro n x y1 y2 Hv H21
    exists y1
    exists y2
  unit := ⟨Diamond.Bot⟩
  unit_valid := by simp
  unit_left_id := by
    intro x
    rcases x with ⟨⟨_⟩⟩ <;> simp [Diamond.op]
  pcore_unit := rfl

theorem not_bupd_sep' : ¬(sep_bupd_def (PROP := UPred (LeibnizO Diamond)) (UPred.ownM ⟨Diamond.Lft⟩) (UPred.ownM ⟨Diamond.Rgt⟩)) := by
  intro H
  have H' := H 0 ⟨Diamond.Lft⟩ (by simp [CMRA.ValidN])
  sorry
-/


local instance : UCMRA (LeibnizO Diamond) where
  pcore n := some ⟨Diamond.Bot⟩ -- Has to be this way because unit
  op x y := ⟨Diamond.op x.1 y.1⟩

  -- Unit has to be valid
  ValidN n x := x = ⟨.Bot⟩
  Valid x := x = ⟨.Bot⟩
  op_ne.ne := by
    intro n x y H
    rw [H]
  pcore_ne := fun _ H => by exact exists_eq_right'.mpr H
  validN_ne := by
    intro n x y H
    rw [H]
    exact id
  valid_iff_validN := by simp
  validN_succ := by simp
  validN_op_left := by intro n x y H; rcases x with ⟨⟨_⟩⟩ <;> rcases y with ⟨⟨_⟩⟩ <;> simp_all [Diamond.op]
  assoc := by
    intro x y z
    rcases x with ⟨⟨_⟩⟩ <;> rcases y with ⟨⟨_⟩⟩ <;> rcases z with ⟨⟨_⟩⟩ <;>  simp_all [Diamond.op]
  comm := by
    intro x y
    rcases x with ⟨⟨_⟩⟩ <;> rcases y with ⟨⟨_⟩⟩ <;> simp_all [Diamond.op]
  pcore_op_left := by
    rintro ⟨x⟩ ⟨cx⟩ ⟨rfl⟩
    rcases x <;> simp [Diamond.op]
  pcore_idem := by rintro _ _ H; rw [H.symm]
  pcore_op_mono := by
    rintro ⟨x⟩ ⟨cx⟩ H y
    exists ⟨Diamond.Bot⟩
    rw [H]
    simp
    cases cx <;> simp [Diamond.op]
  extend := by
    intro n x y1 y2 Hv H21
    exists y1
    exists y2
  unit := ⟨Diamond.Bot⟩
  unit_valid := by simp
  unit_left_id := by
    intro x
    rcases x with ⟨⟨_⟩⟩ <;> simp [Diamond.op]
  pcore_unit := rfl

theorem not_bupd_sep' : ¬(sep_bupd_def (PROP := UPred (LeibnizO Diamond)) (UPred.ownM ⟨Diamond.Lft⟩) (UPred.ownM ⟨Diamond.Rgt⟩)) := by
  intro H
  have H' := H 0 ⟨Diamond.Bot⟩ (by simp [CMRA.ValidN])
  simp [BI.sep, UPred.sep, BUpd.bupd, UPred.bupd] at H'
  have H'' := H' ?G
  case G =>
    rintro k yf ⟨rfl⟩ H
    rcases yf with ⟨⟨_⟩⟩ <;> simp [CMRA.op, Diamond.op, CMRA.ValidN] at H
    exists ⟨Diamond.Bot⟩
    refine ⟨?_, ?_⟩; simp [CMRA.op, Diamond.op, CMRA.ValidN]
    exists ⟨Diamond.Bot⟩
    exists ⟨Diamond.Bot⟩
    simp [CMRA.op, Diamond.op, CMRA.ValidN]
    simp [UPred.ownM]
    sorry
  sorry




/-
-- Core of Ex must be itself (totality)

inductive MyE | Bot | Ex (auth : LeibnizO Nat)

structure MyA where
  auth : Option (LeibnizO MyE)
  frag : LeibnizO Nat

instance : UCMRA (LeibnizO MyA) where
  pcore x := some ⟨none, x.1.frag⟩
  op x y := sorry
  ValidN n x := sorry
  Valid x := sorry
  op_ne.ne := sorry
  pcore_ne := sorry
  validN_ne := by sorry
  valid_iff_validN := by sorry
  validN_succ := by sorry
  validN_op_left := by sorry
  assoc := sorry
  comm := sorry
  pcore_op_left := sorry
  pcore_idem := sorry
  pcore_op_mono := sorry
  extend := sorry
  unit := sorry
  unit_valid := by sorry
  unit_left_id := sorry
  pcore_unit := sorry

-/


-/
end BupdSepCounterexample
