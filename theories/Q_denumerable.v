(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)

(************************************************************************)
(* Copyright 2005 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *) 
(* GNU Lesser General Public License Version 2.1                        *)
(************************************************************************)

(** We start by some general notions for expressing the bijection *)

Definition identity (A:Type) := fun (a:A) => a.
Definition compose (A B C:Type) (g:B->C) (f:A->B) := fun (a:A) => g(f a).

Section Denumerability.

(** What it means to have the same cardinality *)
Definition same_cardinality (A:Type) (B:Type) :=
 {f:A->B & { g:B->A | 
  (forall b,(compose _ _ _ f g) b = (identity B) b) /\
   forall a,(compose _ _ _ g f) a = (identity A) a}}.

(** What it means to be a denumerable *)
Definition is_denumerable A := same_cardinality A nat.

Lemma same_cardinality_transitive :
 forall A B C, same_cardinality A B -> same_cardinality B C -> same_cardinality A C.
Proof.
 intros A B C [f [g [HAB1 HAB2]]] [h [k [HBC1 HBC2]]];
 repeat (match goal with [id1: forall (_:_), compose _ _ _ _ _ _  = identity _ _  |- _ ]=> 
                            unfold compose in id1; unfold identity in id1 end);
 exists (compose _ _ _ h f);
 exists (compose _ _ _ g k);
 unfold compose; unfold identity;
 split;
  [ intro c; rewrite (HAB1 (k c))
  | intro a; rewrite (HBC2 (f a))
  ]; trivial.
Defined.

Lemma is_denumerable_transitive :
 forall A B, is_denumerable A -> same_cardinality B A -> is_denumerable B.
Proof.
 intros A B HA HBA; apply (same_cardinality_transitive B A nat HBA HA).
Defined.

End Denumerability.

(** We first prove that [Z] is denumerable *)

From Coq Require Import ZArith.
From Coq Require Import Lia.

(** An injection from [Z] to [nat] *)
Definition Z_to_nat_i (z:Z) :nat :=
   match z with 
   | Z0 => O
   | Zpos p => Nat.double (nat_of_P p)
   | Zneg p => pred (Nat.double (nat_of_P p))
   end.

(** Some lemmas about parity. *)
Lemma odd_pred2n: forall n : nat, Nat.Odd_alt n -> {p : nat | n = pred (Nat.double p)}.
Proof.
 intros n H_odd;
 apply Nat.Odd_alt_Odd in H_odd;
 rewrite (Nat.Odd_double _ H_odd);
 exists (S (Nat.div2 n));
 generalize (Nat.div2 n);
 clear n H_odd; intros n;
 unfold Nat.double;
 rewrite Nat.add_succ_r;
 reflexivity.
Defined.

Lemma even_2n : forall n : nat, Nat.Even_alt n -> {p : nat | n = Nat.double p}.
Proof.
intros n H_even; exists (Nat.div2 n).
apply Nat.Even_alt_Even in H_even.
apply Nat.Even_double; assumption.
Defined.

Lemma even_odd_exists_dec : forall n, {p : nat | n = Nat.double p} + {p : nat | n = pred (Nat.double p)}.
Proof. 
 intro n;
 destruct (Nat.Even_Odd_dec n) as [H_parity|H_parity];
 [ left; apply Nat.Even_alt_Even in H_parity; apply (even_2n _ H_parity)
 | right; apply Nat.Odd_alt_Odd in H_parity; apply (odd_pred2n _ H_parity)].
Defined.

(** An injection from [nat] to [Z] *)
Definition nat_to_Z_i (n:nat) := 
  match even_odd_exists_dec n with
  | inl s => let (k, _) := s in Z_of_nat k
  | inr s => let (k, _) := s in Z.opp (Z_of_nat k)
  end.

Lemma double_eq_half_eq:forall m n, Nat.double m = Nat.double n -> m = n.
Proof.
 unfold Nat.double; intros m n; lia.
Defined.

Lemma parity_mismatch_not_eq:forall m n, Nat.Even_alt m -> Nat.Odd_alt n -> m <> n.
Proof.
 intros m n H_even H_odd H_eq; subst m.
 apply Nat.Even_alt_Even in H_even.
 apply Nat.Odd_alt_Odd in H_odd.
 apply (Nat.Even_Odd_False n); trivial.
Defined.

Lemma even_double : forall n, Nat.Even_alt (Nat.double n).
Proof.
 intro n;
 unfold Nat.double;
 replace (n + n) with (2*n);
 [apply Nat.Even_alt_Even; exists n; reflexivity | lia].
Defined.

Lemma double_S_neq_pred:forall m n, ~Nat.double (S m) = pred (Nat.double n).
Proof.
 intros m [|n].
 unfold Nat.double; lia.
 apply (parity_mismatch_not_eq (Nat.double (S m)) (pred (Nat.double (S n))));
 try apply even_double;
 replace (pred (Nat.double (S n))) with (S (Nat.double n));
 [ constructor; apply even_double
 | unfold Nat.double; lia].
Defined.

Lemma eq_add_pred : forall n m : nat, pred n = pred m -> {n = m} + {n < 2 /\ m < 2}.
Proof.
 intros [|[|n]] m;
 simpl;
 intros H;
 try (right; lia);
 left;
 rewrite (f_equal S H);
 apply (Nat.lt_succ_pred 0);
 lia.
Defined.

(** We prove that the maps [Z_to_nat_i] is the right inverse of [nat_to_Z_i].*)

Lemma nat_to_Z_to_nat_i : forall (z:Z), nat_to_Z_i (Z_to_nat_i z) = z.
Proof.
 intros [|p|p];
 unfold nat_to_Z_i.
 simpl; 
   case (even_odd_exists_dec 0); intros [k Hk];
     [transitivity (Z_of_nat 0)
       |transitivity (Z.opp (Z_of_nat 0))
     ]; trivial;
  try apply (f_equal Z.opp);
    apply (f_equal Z_of_nat);
      unfold Nat.double in Hk; lia.

 case (even_odd_exists_dec (Z_to_nat_i (Zpos p)) ); intros [k Hk].
  unfold Z_to_nat_i in Hk;
  rewrite <- (double_eq_half_eq _ _ Hk);
  symmetry; apply Zpos_eq_Z_of_nat_o_nat_of_P.

  apply False_ind;
  unfold Z_to_nat_i in Hk;
  destruct (ZL4 p) as [m Hm];
  rewrite Hm in Hk;
  apply (double_S_neq_pred m k);
  assumption.


 case (even_odd_exists_dec (Z_to_nat_i (Zneg p)) ); intros [k Hk].
  unfold Z_to_nat_i in Hk;
  unfold Nat.double in Hk;
  destruct (ZL4 p) as [m Hm]; lia.

  unfold Z_to_nat_i in Hk;
  case (eq_add_pred _ _ Hk).
   intro Hk';
   rewrite <- (double_eq_half_eq _ _ Hk');
   symmetry;
   apply Z.opp_inj;
   rewrite Zopp_neg;
   rewrite Z.opp_involutive;
   apply Zpos_eq_Z_of_nat_o_nat_of_P.

   intros [H_nat_p_lt_2 _];
   apply False_ind;
   destruct (ZL4 p) as [m Hm];
   rewrite Hm in H_nat_p_lt_2;
   unfold Nat.double in H_nat_p_lt_2;
   rewrite Nat.add_succ_r in H_nat_p_lt_2;
   lia.
Defined.

(** We prove that the maps [Z_to_nat_i] is the left inverse of [nat_to_Z_i].*)

Lemma Z_to_nat_to_Z_i : forall (n:nat), Z_to_nat_i (nat_to_Z_i n) = n.
Proof.
 intros [|n];
 unfold nat_to_Z_i.
 case (even_odd_exists_dec 0);
 intros [k Hk];
 transitivity (Z_to_nat_i (Z_of_nat 0)); trivial;
 apply (f_equal Z_to_nat_i);
 simpl; unfold Nat.double in Hk; lia.

 case (even_odd_exists_dec (S n)); intros [[|k] Hk]; rewrite Hk; trivial; simpl;
 [apply (f_equal Nat.double);
  apply nat_of_P_o_P_of_succ_nat_eq_succ
 |transitivity (pred (Nat.double (S k))); trivial;
  apply (f_equal pred);
  apply (f_equal Nat.double);
  apply nat_of_P_o_P_of_succ_nat_eq_succ
 ].
Defined. 

(** And hence [Z] is denumerable: *)

Theorem Z_is_denumerable:is_denumerable Z.
Proof.
 exists Z_to_nat_i; exists nat_to_Z_i;
 split;
 [ apply Z_to_nat_to_Z_i
 | apply nat_to_Z_to_nat_i
 ].
Defined.

(** Next we prove that [Q] and [Z] have the same cardinality *)

From QArithSternBrocot Require Import Q_field.

(** Here there is not much to prove, as [Z] and [Q] are isomorphic data-types.*)

(** An injection from [positive] to [Qpositive]: *)
Fixpoint positive_to_Qpositive_i (p:positive) : Qpositive := 
   match p with 
   | xI p => nR (positive_to_Qpositive_i p)
   | xO p => dL (positive_to_Qpositive_i p)
   | xH => One
   end. 

(** An injection from [Z] to [Q] *)
Definition Z_to_Q_i (z:Z) :=
   match z with 
   | Z0 => Zero
   | Zpos p => Qpos (positive_to_Qpositive_i p)
   | Zneg p => Qneg (positive_to_Qpositive_i p)
   end. 

(** An injection from [Qpositive] to [positive] *) 
Fixpoint Qpositive_to_positive_i (qp:Qpositive) : positive := 
   match qp with 
   | nR qp => xI (Qpositive_to_positive_i qp)
   | dL qp => xO (Qpositive_to_positive_i qp)
   | One => xH
   end. 

(** An injection from [Q] to [Z] *)
Definition Q_to_Z_i (q:Q) :=
   match q with 
   | Zero => Z0
   | Qpos qp => Zpos (Qpositive_to_positive_i qp)
   | Qneg qp => Zneg (Qpositive_to_positive_i qp)
   end. 

(** Proof that [Qpositive_to_positive_i] is the left inverse of [positive_to_Qpositive_i]:*)
Lemma Qpositive_to_positive_to_Qpositive_i : forall (p:positive), Qpositive_to_positive_i (positive_to_Qpositive_i p) = p.
Proof.
 intros p;
 induction p as [p|p|]; trivial;
 simpl;
 rewrite IHp; trivial.
Defined.

(** Proof that [Qpositive_to_positive_i] is the right inverse of [positive_to_Qpositive_i]:*)
Lemma positive_to_Qpositive_to_positive_i : forall qp, positive_to_Qpositive_i (Qpositive_to_positive_i qp) = qp.
Proof.
 intros p;
 induction p as [p|p|]; trivial;
 simpl;
 rewrite IHp; trivial.
Defined.

(** Proof that [Q_to_Z_i] is the left inverse of [Z_to_Q_i]:*)
Lemma Q_to_Z_to_Q_i : forall (z:Z), Q_to_Z_i (Z_to_Q_i z) = z.
Proof.
 intros [|p|p]; trivial;
 simpl;
 rewrite Qpositive_to_positive_to_Qpositive_i; trivial.
Defined.

(** Proof that [Q_to_Z_i] is the right inverse of [Z_to_Q_i]:*)
Lemma Z_to_Q_to_Z_i : forall (q:Q), Z_to_Q_i (Q_to_Z_i q) = q.
Proof.
 intros [|qp|qp]; trivial;
 simpl;
 rewrite positive_to_Qpositive_to_positive_i; trivial.
Defined.

(** And hence [Q] is denumerable: *)
Theorem Q_is_denumerable: is_denumerable Q.
Proof.
 apply is_denumerable_transitive with Z.
 apply Z_is_denumerable.
 exists Q_to_Z_i; exists Z_to_Q_i;
 split;
 [ apply Q_to_Z_to_Q_i
 | apply Z_to_Q_to_Z_i
 ].
Defined.
