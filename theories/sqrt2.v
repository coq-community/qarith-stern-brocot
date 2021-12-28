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

Require Import ArithRing.
Require Import Compare_dec.
Require Import Wf_nat.
Require Import Arith.
Require Import Lia.
 
Theorem minus_minus : forall a b c : nat, a - b - c = a - (b + c).
intros a; elim a; auto.
intros n' Hrec b; case b; auto.
Qed.
 
Remark expand_mult2 : forall x : nat, 2 * x = x + x.
intros x; ring.
Qed.
 
Theorem lt_neq : forall x y : nat, x < y -> x <> y.
unfold not in |- *; intros x y H H1; elim (Nat.lt_irrefl x);
 pattern x at 2 in |- *; rewrite H1; auto.
Qed.

#[local] Hint Resolve lt_neq : core.
 
Theorem monotonic_inverse :
 forall f : nat -> nat,
 (forall x y : nat, x < y -> f x < f y) ->
 forall x y : nat, f x < f y -> x < y.
intros f Hmon x y Hlt; case (le_gt_dec y x); auto.
intros Hle; apply Nat.lt_eq_cases in Hle.
destruct Hle as [Hlt'|Heq].
elim (Nat.lt_asymm _ _ Hlt); apply Hmon; auto.
elim (lt_neq _ _ Hlt); rewrite Heq; auto.
Qed.
 
Theorem mult_lt : forall a b c : nat, c <> 0 -> a < b -> a * c < b * c.
intros a b c; elim c.
intros H; elim H; auto.
intros c'; case c'.
intros; lia.
intros c'' Hrec Hneq Hlt;
 repeat rewrite <- (fun x : nat => mult_n_Sm x (S c'')).
lia.
Qed.
 
Remark add_sub_square_identity :
 forall a b : nat,
 (b + a - b) * (b + a - b) = (b + a) * (b + a) + b * b - 2 * ((b + a) * b).
intros a b; rewrite (Nat.add_comm b a) at 1 2; rewrite Nat.add_sub.
repeat rewrite Nat.mul_add_distr_r || rewrite <- (Nat.mul_comm (b + a)).
replace (b * b + a * b + (b * a + a * a) + b * b) with
 (b * b + a * b + (b * b + a * b + a * a)); try (ring; fail).
rewrite expand_mult2; repeat rewrite Nat.add_sub; auto with *.
Qed.
 
Theorem sub_square_identity :
 forall a b : nat, b <= a -> (a - b) * (a - b) = a * a + b * b - 2 * (a * b).
intros a b H.
apply Nat.sub_add in H; rewrite Nat.add_comm in H.
rewrite <- H.
apply add_sub_square_identity.
Qed.
 
Theorem square_monotonic : forall x y : nat, x < y -> x * x < y * y.
intros x; case x.
intros y; case y; simpl in |- *; auto with *.
intros x' y Hlt; apply Nat.lt_trans with (S x' * y).
rewrite (Nat.mul_comm (S x') y); apply mult_lt; auto.
apply mult_lt; lia.
Qed.
 
Theorem root_monotonic : forall x y : nat, x * x < y * y -> x < y.
exact (monotonic_inverse (fun x : nat => x * x) square_monotonic).
Qed.
 
Remark square_recompose : forall x y : nat, x * y * (x * y) = x * x * (y * y).
intros; ring.
Qed.
 
Remark mult2_recompose : forall x y : nat, x * (2 * y) = x * 2 * y.
intros; ring.
Qed.

Section sqrt2_decrease.

Variables (p q : nat) (pos_q : 0 < q) (hyp_sqrt : p * p = 2 * (q * q)).
 
Theorem sqrt_q_non_zero : 0 <> q * q.
generalize pos_q; case q.
intros H; elim (Nat.nlt_0_r 0); auto.
intros n H.
simpl in |- *; discriminate.
Qed.

#[local] Hint Resolve sqrt_q_non_zero : core.
 
Ltac solve_comparison :=
  apply root_monotonic; repeat rewrite square_recompose; rewrite hyp_sqrt;
   rewrite mult2_recompose; apply mult_lt; auto with arith.
 
Theorem comparison1 : q < p.
replace q with (1 * q); try ring.
replace p with (1 * p); try ring.
solve_comparison.
Qed.
 
Theorem comparison2 : 2 * p < 3 * q.
solve_comparison.
Qed.
 
Theorem comparison3 : 4 * q < 3 * p.
solve_comparison.
Qed.

#[local] Hint Resolve comparison1 comparison2 comparison3: arith.
 
Theorem comparison4 : 3 * q - 2 * p < q.
apply Nat.add_lt_mono_l with (2 * p).
rewrite Nat.add_comm; rewrite Nat.sub_add;
 try (simple apply Nat.lt_le_incl; auto with arith).
replace (3 * q) with (2 * q + q); try ring.
apply Nat.add_lt_le_mono; auto.
repeat rewrite (Nat.mul_comm 2); apply mult_lt; auto with arith.
Qed.
 
Remark mult_minus_distr_l : forall a b c : nat, a * (b - c) = a * b - a * c.
intros a b c; repeat rewrite (Nat.mul_comm a); apply Nat.mul_sub_distr_r.
Qed.
 
Remark minus_eq_decompose :
 forall a b c d : nat, a = b -> c = d -> a - c = b - d.
intros a b c d H H0; rewrite H; rewrite H0; auto.
Qed.
 
Theorem new_equality :
 (3 * p - 4 * q) * (3 * p - 4 * q) = 2 * ((3 * q - 2 * p) * (3 * q - 2 * p)).
repeat rewrite sub_square_identity; auto with arith.
repeat rewrite square_recompose; rewrite mult_minus_distr_l.
apply minus_eq_decompose; try rewrite hyp_sqrt; ring.
Qed.

End sqrt2_decrease.

#[local] Hint Resolve Nat.lt_le_incl comparison2: sqrt.
 
Theorem sqrt2_not_rational :
 forall p q : nat, q <> 0 -> p * p = 2 * (q * q) -> False.
intros p q; generalize p; clear p; elim q using (well_founded_ind lt_wf).
clear q; intros q Hrec p Hneq; 
 pose proof Hneq as Hlt_O_q; apply Nat.neq_0_lt_0 in Hlt_O_q;
 intros Heq.
apply (Hrec (3 * q - 2 * p) (comparison4 _ _ Hlt_O_q Heq) (3 * p - 4 * q)).
apply sym_not_equal; apply lt_neq; apply Nat.add_lt_mono_l with (2 * p);
 rewrite <- plus_n_O; rewrite Nat.add_comm; rewrite Nat.sub_add; auto with *.
apply new_equality; auto.
Qed.
