Require Import VST.msl.msl_direct.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.

Open Local Scope logic.

Lemma orp_derives {A} {ND : NatDed A}: forall P1 P2 Q1 Q2 : A,
  P1 |-- Q1 ->
  P2 |-- Q2 ->
  P1 || P2 |-- Q1 || Q2.
Proof.
  intros.
  apply orp_left.
  apply orp_right1. trivial.
  apply orp_right2. trivial.
Qed.

Lemma exp_derives {A} {ND : NatDed A} {B}: forall (P Q : B -> A),
  (forall b, P b |-- Q b) ->
  EX b : B, P b |-- EX b : B, Q b.
Proof.
  intros.
  apply exp_left. intro b.
  apply exp_right with b. trivial.
Qed.

Lemma FF_right {A} `{NatDed A}: forall P Q,
  P |-- FF ->
  P |-- Q.
Proof. 
  intros. 
  apply derives_trans with FF; auto. 
  apply FF_left.
Qed.

(* NEGATIONS *)
Definition notp {A} `{NatDed A} : A -> A :=
  fun P => (P --> FF).
Notation " '!' P " := (notp P) (at level 30) : logic.

Lemma notp_derives {A} `{NatDed A}: forall P Q : A,
  P |-- Q ->
  !Q |-- !P.
Proof. intros. apply imp_derives; auto. Qed.

(* The following two lemmas are not stated in some kind of minimal form. *)
Lemma notp_left {A} `{NatDed A}: forall P Q,
  P && !P |-- Q.
Proof.
  intros.
  apply FF_right.
  apply modus_ponens.
Qed.

Lemma notp_right {A} `{NatDed A}: forall P Q,
  P && Q |-- FF ->
  P |-- !Q.
Proof.
  intros.
  unfold notp.
  rewrite <- imp_andp_adjoint. trivial.
Qed.

Lemma notp_TT {A} `{NatDed A}:
  !TT = FF.
Proof.
  apply pred_ext.
  rewrite <- (TT_andp (! TT)).
  apply modus_ponens.
  apply FF_left.
Qed.

Lemma notp_FF {A} `{NatDed A}:
  !FF = TT.
Proof.
  apply pred_ext.
  apply TT_right.
  apply notp_right.
  apply andp_left2. trivial.
Qed.

Lemma contradiction_FF {A} `{NatDed A}: forall P,
  P && !P = FF.
Proof.
  intro. apply pred_ext.
  apply modus_ponens.
  apply FF_left.
Qed.

Lemma notnot2 {A} `{NatDed A}: forall P : A,
  P |-- ! (! P).
Proof.
  intro. 
  apply notp_right.
  apply notp_left.
Qed.

Lemma notnotnot {A} `{NatDed A}: forall P : A,
  ! (! (! P)) |-- !P.
Proof.
  intro.
  apply notp_right.
  eapply derives_trans.
  * apply andp_derives.
    apply derives_refl.
    apply notnot2.
  * rewrite andp_comm.
    apply notp_left.
Qed.

Lemma deMorgan_orp1 {A} `{NatDed A}: forall (P Q : A),
  !(P || Q) |-- (!P) && (!Q).
Proof.
  intros.
  apply andp_right; apply notp_derives.
  apply orp_right1; trivial.
  apply orp_right2; trivial.
Qed.

Lemma deMorgan_orp2 {A} `{NatDed A}: forall (P Q : A),
  (!P) && (!Q) |-- !(P || Q).
Proof.
  intros.
  apply notp_right.
  rewrite andp_comm.
  rewrite imp_andp_adjoint.
  apply orp_left.
  rewrite <- imp_andp_adjoint.
  rewrite <- andp_assoc.
  rewrite imp_andp_adjoint.
  apply notp_left.
  rewrite andp_comm.
  rewrite <- imp_andp_adjoint.
  rewrite <- andp_assoc.
  rewrite imp_andp_adjoint.
  apply notp_left.
Qed.

Lemma deMorgan_orp {A} `{NatDed A}: forall (P Q : A),
  !(P || Q) = (!P) && (!Q).
Proof. intros. apply pred_ext. apply deMorgan_orp1. apply deMorgan_orp2. Qed.

Lemma deMorgan_andp2 {A} `{NatDed A}: forall (P Q : A),
  (!P) || (!Q) |-- !(P && Q).
Proof.
  intros.
  apply orp_left; apply notp_derives.
  apply andp_left1; trivial.
  apply andp_left2; trivial.
Qed.

Lemma contrapositive2 {A} `{NatDed A}: forall (P Q : A),
  Q --> P |-- (!P) --> (!Q).
Proof.
  intros.
  rewrite <- imp_andp_adjoint.
  apply notp_right.
  rewrite andp_comm.
  rewrite <- andp_assoc.
  rewrite imp_andp_adjoint.
  eapply derives_trans.
  apply modus_ponens.
  rewrite <- imp_andp_adjoint.
  apply modus_ponens.
Qed.

Lemma deMorgan_exp1 {A} `{NatDed A} {B}: forall (P : B -> A),
  !(EX b : B, P b) |-- ALL b : B, !(P b).
Proof.
  intros.
  apply allp_right. intro x.
  apply notp_derives.
  apply exp_right with x. trivial.
Qed.

Lemma deMorgan_exp2 {A} `{NatDed A} {B}: forall (P : B -> A),
  ALL b : B, !(P b) |-- !(EX b : B, P b).
Proof.
  intros.
  apply notp_right.
  rewrite andp_comm.
  rewrite imp_andp_adjoint.
  apply exp_left. intro x.
  rewrite <- imp_andp_adjoint.
  rewrite andp_comm.
  rewrite imp_andp_adjoint.
  apply allp_left with x. trivial.
Qed.

Lemma deMorgan_exp {A} `{NatDed A} {B}: forall (P : B -> A),
  !(EX b : B, P b) = ALL b : B, !(P b).
Proof. intros. apply pred_ext. apply deMorgan_exp1. apply deMorgan_exp2. Qed.

Lemma deMorgan_allp2 {A} `{NatDed A} {B}: forall (P : B -> A),
  EX b : B, !(P b) |-- !(ALL b : B, P b).
Proof.
  intros.
  apply exp_left. intro x.
  apply notp_derives.
  apply allp_left with x. trivial.
Qed.

(* CLASSICAL *)
Class ClassicNatDed (A : Type) {ND : NatDed A} : Type :=
  LEM_right : forall P : A, TT |-- P || !P.

Lemma LEM_cases {A} `{ClassicNatDed A} : forall P Q R,
  P && Q |-- R ->
  (!P) && Q |-- R ->
  Q |-- R.
Proof.
  intros.
  rewrite <- (TT_andp Q).
  rewrite imp_andp_adjoint.
  eapply derives_trans. apply (LEM_right P).
  apply orp_left; rewrite <- imp_andp_adjoint; trivial.
Qed.

Lemma notnot1 {A} `{ClassicNatDed A} : forall (P : A),
  ! (!P) |-- P.
Proof.
  intro.
  apply (LEM_cases P).
  apply andp_left1. trivial.
  apply notp_left.
Qed.

Lemma notnot {A} `{ClassicNatDed A} : forall (P : A),
  ! (! P) = P.
Proof. intros. apply pred_ext. apply notnot1. apply notnot2. Qed.

Lemma PBC {A} `{ClassicNatDed A} : forall (P Q : A),
  P && (! Q) |-- FF ->
  P |-- Q.
Proof.
  intros.
  eapply derives_trans.
  apply notp_right. apply H0.
  apply notnot1.
Qed.

Lemma deMorgan_andp1 {A} `{ClassicNatDed A}: forall (P Q : A),
  ! (P && Q) |-- (! P) || (! Q).
Proof.
  intros.
  apply (LEM_cases Q).
  apply (LEM_cases P).
  rewrite <- andp_assoc. apply notp_left.
  apply orp_right1. apply andp_left1. trivial.
  apply orp_right2. apply andp_left1. trivial.
Qed.

Lemma deMorgan_andp {A} `{ClassicNatDed A}: forall (P Q : A),
  ! (P && Q) = (! P) || (! Q).
Proof. intros. apply pred_ext. apply deMorgan_andp1. apply deMorgan_andp2. Qed.

Lemma contrapositive1 {A} `{ClassicNatDed A}: forall (P Q : A),
  (!P) --> (!Q) |-- Q --> P.
Proof.
  intros.
  rewrite <- imp_andp_adjoint.
  apply (LEM_cases P).
  apply andp_left1. trivial.
  rewrite <- andp_assoc.
  rewrite imp_andp_adjoint.
  eapply derives_trans.
  apply modus_ponens.
  rewrite <- imp_andp_adjoint.
  rewrite andp_comm.
  apply notp_left.
Qed.

Lemma contrapositive {A} `{ClassicNatDed A}: forall (P Q : A),
  (!P) --> (!Q) = Q --> P.
Proof. intros. apply pred_ext. apply contrapositive1. apply contrapositive2. Qed.

Lemma deMorgan_allp1 {A} `{ClassicNatDed A} {B}: forall (P : B -> A),
  ! (ALL b : B, P b) |-- EX b : B, ! (P b).
Proof.
  intros.
  apply PBC.
  rewrite andp_comm. rewrite imp_andp_adjoint.
  pose proof (notnot (ALL b : B, P b)). unfold notp at 1 in H0. rewrite H0. clear H0.
  apply allp_right. intro x.
  apply PBC.
  rewrite andp_comm. rewrite imp_andp_adjoint.
  pose proof (notnot (EX b : B, notp (P b))). unfold notp at 1 in H0. rewrite H0. clear H0.
  apply exp_right with x. trivial.
Qed.

Lemma deMorgan_allp {A} `{ClassicNatDed A} {B}: forall (P : B -> A),
  ! (ALL b : B, P b) = EX b : B, ! (P b).
Proof. intros. apply pred_ext. apply deMorgan_allp1. apply deMorgan_allp2. Qed.
