Require Import VST.msl.msl_direct.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.

Require Import neg_logic.

Open Local Scope logic.

(* MODAL LOGIC *)
Class ModLog (RT : Type) (A: Type) (ND: NatDed A) : Type := mkModLog {
  box : RT -> A -> A;
  modal_N : forall R P, TT |-- P -> TT |-- box R P;
  modal_K : forall R P Q, box R (P --> Q) |-- (box R P) -->  (box R Q);
  (* Sometimes axiom A is called axiom BF, see https://plato.stanford.edu/entries/logic-modal/ *)
  modal_A : forall R B P, ALL b : B, box R (P b) |-- box R (ALL b : B, P b);
}.
Notation " '[' R ']' " := (box R) : logic.

(* Here we are classical... not clear if there is a better/alternative way forward yet... *)
Definition diamond {RT} {A} {ND : NatDed A} {ML: ModLog RT A ND} : RT -> A -> A :=
  fun rt P => ! ([rt] (!P)).
(*
Notation " '<' R '>' " := (diamond R) : logic.
*)

Class ModLogSeq {RT : Type} {A : Type} {ND : NatDed A} (ML : @ModLog RT A ND) : Type := mkModLogSeq {
  seqR : RT -> RT -> RT;
  seqR_box: forall R1 R2 (P : A),
    [seqR R1 R2] P = [R1] ([R2] P);
}.

Class ModLogDual {RT : Type} {A: Type} {ND : NatDed A} (ML : @ModLog RT A ND) : Type := mkModLogDual {
  antiR : RT -> RT;
  antiR_involution : forall R, antiR (antiR R) = R;
  antidiamond_box_adjoint : forall R P Q,
    diamond (antiR R) P |-- Q  <->
    P |-- [R] Q;
}.

(* CORRESPONDENCE CLASSES *)

Section CorrespondenceClasses.

Context {A RT : Type}.
Context {ND : NatDed A}.
Context {ML : ModLog RT A ND}.

(* reflexivity *)
Class Modal_T (R : RT) :=
  modal_T : forall P, [R] P |-- P.

(* transitivity *)
Class Modal_4 (R : RT) :=
  modal_4 : forall P, [R] P |-- [R] ([R] P).

(* density *)
Class Modal_C4 (R : RT) :=
  modal_C4 : forall P, [R] ([R] P) |-- [R] P.

(* serial, i.e. total *)
Class Modal_D (R : RT) :=
  modal_D : forall P, [R] P |-- diamond R P.
  (* I'm not sure what this one is called in the literature. *)

(* functional *)
Class Modal_CD (R : RT) :=
  modal_CD : forall P, diamond R P |-- [R] P.

(* symmetric *)
Class Modal_B (R : RT) :=
  modal_B : forall P, P |-- [R] (diamond R P).
 
(* finite chains *)
Class Modal_W  (R : RT) :=
  modal_W : forall P, ([R] P |-- P) -> (TT |-- P).

End CorrespondenceClasses.

Section ModalLogic.

Context {A RT : Type}.
Context {ND : NatDed A}.
Context {ML : ModLog RT A ND}.

Section ModalLogic_K.

Lemma box_TT: forall R,
  [R] TT = TT.
Proof.
  intro. apply pred_ext.
  apply TT_right.
  apply modal_N.
  apply TT_right.
Qed.

Lemma box_positive: forall R P (Q : A),
      P |-- Q         -> 
  [R] P |-- [R] Q.
Proof.
  intros.
  rewrite <- (TT_andp ([R] P)).
  rewrite imp_andp_adjoint.
  apply derives_trans with ([R] (P --> Q)).
  apply modal_N. rewrite <- imp_andp_adjoint.
  rewrite TT_andp. trivial.
  apply modal_K.
Qed.

Lemma box_andp: forall R (P Q : A),
  [R] (P && Q) = ([R] P) && ([R] Q).
Proof.
  intros. apply pred_ext.
  * apply andp_right; apply box_positive.
    apply andp_left1; auto. apply andp_left2; auto.
  * rewrite imp_andp_adjoint.
    eapply derives_trans.
    apply box_positive.
    rewrite <- imp_andp_adjoint; auto.
    apply modal_K.
Qed.

Lemma box_orp2 {R : RT}: forall P (Q : A),
  ([R] P) || ([R] Q) |-- [R] (P || Q).
Proof.
  intros.
  apply orp_left; apply box_positive.
  apply orp_right1; trivial.
  apply orp_right2; trivial.
Qed.

Lemma box_allp {B}: forall R (P : B -> A),
  [R] (ALL b : B, P b) = ALL b : B, [R] (P b).
Proof.
  intros. apply pred_ext.
  apply allp_right. intro b.
  apply box_positive. apply allp_left with b. apply derives_refl.
  apply modal_A.
Qed.

Lemma box_exp2 {B}: forall R (P : B -> A),
  EX b : B, [R] (P b) |-- [R] (EX b : B, P b).
Proof.
  intros.
  apply exp_left. intro x.
  apply box_positive.
  apply exp_right with x.
  trivial.
Qed.

Lemma deMorgan_box1 `{CND: @ClassicNatDed A ND}: forall R (P : A),
  ! ([R] P) |-- diamond R (! P).
Proof.
  intros. unfold diamond.
  apply notp_derives.
  apply box_positive.
  apply notnot1. (* classical *)
Qed.

Lemma deMorgan_box2: forall R (P : A),
  diamond R (! P) |-- ! ([R] P).
Proof.
  intros. unfold diamond.
  apply notp_derives.
  apply box_positive.
  apply notnot2.
Qed.

Lemma deMorgan_box `{CND: @ClassicNatDed A ND}: forall R (P : A),
  ! ([R] P) = diamond R (! P).
Proof. intros. apply pred_ext. apply deMorgan_box1. apply deMorgan_box2. Qed.

Lemma deMorgan_diamond1 `{CND: @ClassicNatDed A ND}: forall R (P : A),
  ! (diamond R P) |-- [R] (! P).
Proof.
  intros. unfold diamond.
  apply notnot1. (* classical *)
Qed.

Lemma deMorgan_diamond2: forall R (P : A),
  [R] (! P) |-- ! (diamond R P).
Proof.
  intros.
  apply notnot2.
Qed.

Lemma deMorgan_diamond `{CND: @ClassicNatDed A ND}: forall R (P : A),
  ! (diamond R P) = [R] (! P).
Proof. intros. apply pred_ext. apply deMorgan_diamond1. apply deMorgan_diamond2. Qed.

Lemma diamond_FF: forall R,
  diamond R FF = FF.
Proof.
  intro. apply pred_ext.
  * unfold diamond.
    rewrite notp_FF, box_TT, notp_TT. trivial.
  * apply FF_left.
Qed.

Lemma diamond_positive: forall R P (Q : A),
            P |-- Q               -> 
  diamond R P |-- diamond R Q.
Proof.
  intros. unfold diamond.
  apply notp_derives.
  apply box_positive.
  apply notp_derives.
  trivial.
Qed.

Definition NTD (R : RT) : A := diamond R TT.
Lemma diamond_WN: forall R (P : A),
     TT |-- P ->
  NTD R |-- diamond R P.
Proof.
  intros.
  apply diamond_positive.
  trivial.
Qed.

Lemma diamond_orp1 `{CND: @ClassicNatDed A ND}: forall R (P Q : A),
  diamond R (P || Q) |-- (diamond R P) || (diamond R Q).
Proof.
  intros. unfold diamond.
  rewrite deMorgan_orp.
  rewrite box_andp.
  apply deMorgan_andp1. (* classic *)
Qed.

Lemma diamond_orp2: forall R (P Q : A),
  (diamond R P) || (diamond R Q) |-- diamond R (P || Q).
Proof.
  intros.
  eapply derives_trans.
  apply deMorgan_andp2.
  rewrite <- box_andp.
  apply notp_derives.
  apply box_positive.
  rewrite deMorgan_orp. trivial.
Qed.

Lemma diamond_orp `{CND: @ClassicNatDed A ND}: forall R (P Q : A),
  diamond R (P || Q) = (diamond R P) || (diamond R Q).
Proof. intros. apply pred_ext. apply diamond_orp1. apply diamond_orp2. Qed.

Lemma diamond_andp1: forall R P (Q : A),
  diamond R (P && Q) |-- (diamond R P) && (diamond R Q).
Proof.
  intros.
  apply andp_right; apply diamond_positive.
  apply andp_left1; trivial.
  apply andp_left2; trivial.
Qed.

Lemma diamond_allp1 {B}: forall R (P : B -> A),
  diamond R (ALL b : B, P b) |-- ALL b : B, diamond R (P b).
Proof.
  intros.
  apply allp_right. intro x.
  apply diamond_positive.
  apply allp_left with x. trivial.
Qed.

Lemma diamond_exp1 `{CND: @ClassicNatDed A ND} {B}: forall R (P : B -> A),
  diamond R (EX b : B, P b) |-- EX b : B, diamond R (P b).
Proof.
  intros. unfold diamond.
  eapply derives_trans.
  2: apply deMorgan_allp1. (* classic *)
  apply notp_derives.
  rewrite <- box_allp.
  apply box_positive.
  apply deMorgan_exp2.
Qed.

Lemma diamond_exp2 {B}: forall R (P : B -> A),
  EX b : B, diamond R (P b) |-- diamond R (EX b : B, P b).
Proof.
  intros.
  apply exp_left. intro x.
  apply diamond_positive.
  apply exp_right with x. trivial.
Qed.

Lemma diamond_exp `{CND: @ClassicNatDed A ND} {B}: forall R (P : B -> A),
  diamond R (EX b : B, P b) = EX b : B, diamond R (P b).
Proof. intros. apply pred_ext. apply diamond_exp1. apply diamond_exp2. Qed.

End ModalLogic_K.

(* reflexivity *)
Section ModalLogic_T.

Context {R : RT}.
Context {MLT : Modal_T R}.

Instance Modal_T_Modal_C4: Modal_C4 R.
Proof.
  intro.
  apply modal_T.
Qed.

Instance Modal_T_Modal_D: Modal_D R.
Proof.
  intro.
  apply notp_right.
  rewrite <- box_andp.
  rewrite contradiction_FF.
  apply modal_T.
Qed.

Lemma diamond_CT: forall P : A,
  P |-- diamond R P.
Proof.
  intro.
  apply notp_right.
  eapply derives_trans.
  apply andp_derives.
  trivial.
  apply modal_T.
  apply notp_left.
Qed.

End ModalLogic_T.

(* transitivity *)
(* density *)
Section ModalLogic_4_C4.

Context {R : RT}.
Context {ML4 : Modal_4 R}.
Context {MLC4 : Modal_C4 R}.

Lemma modal4C4  : forall P,
  [R] P = [R] ([R] P).
Proof. intros. apply pred_ext. apply modal_4. apply modal_C4. Qed.

End ModalLogic_4_C4.

(* serial, i.e. total *)
Section ModalLogic_D.

Context {R : RT}.
Context {MLD : Modal_D R}.

Lemma box_notp1: forall (P : A),
  [R] (! P) |-- ! ([R] P).
Proof.
  intro.
  apply notp_right.
  rewrite <- box_andp.
  rewrite andp_comm.
  rewrite contradiction_FF.
  pattern FF at 2. rewrite <- (diamond_FF R).
  apply modal_D.
Qed.

Lemma diamond_notp2: forall P : A,
  !(diamond R P) |-- diamond R (! P).
Proof.
  intros.
  apply notp_derives.
  eapply derives_trans.
  apply modal_D.
  apply notp_derives.
  apply box_positive.
  apply notnot2.
Qed.

Lemma diamond_N: forall P : A,
  TT |-- P ->
  TT |-- diamond R P.
Proof.
  intros.
  apply derives_trans with (NTD R).
  rewrite <- (box_TT R).
  apply modal_D.
  apply diamond_WN. trivial.
Qed.

Lemma diamond_antiK {CND: @ClassicNatDed A ND}: forall P (Q : A),
  (diamond R P) --> (diamond R Q) |-- diamond R (P --> Q).
Proof.
  intros.
  apply (LEM_cases (diamond R P)).
  * eapply derives_trans.
    apply modus_ponens.
    apply diamond_positive.
    rewrite <- imp_andp_adjoint.
    apply andp_left1. trivial.
  * apply andp_left1.
    eapply derives_trans.
    apply diamond_notp2.
    apply diamond_positive.
    rewrite <- imp_andp_adjoint.
    rewrite andp_comm.
    apply notp_left.
Qed.

End ModalLogic_D.

(* functional *)
Section ModalLogic_CD.

Context {R : RT}.
Context {MLCD : Modal_CD R}.

Lemma box_notp2 {CND: @ClassicNatDed A ND}: forall (P : A),
  ! ([R] P) |-- [R] (! P).
Proof.
  intros.
  eapply derives_trans.
  apply deMorgan_box1. (* classic *)
  apply modal_CD.
Qed.

Lemma diamond_K: forall P (Q : A),
  diamond R (P --> Q) |-- (diamond R P) --> (diamond R Q).
Proof.
  intros.
  eapply derives_trans.
  * apply modal_CD.
  * eapply derives_trans.
    + apply box_positive.
      apply contrapositive2.
    + eapply derives_trans.
      - apply modal_K.
      - apply contrapositive2.
Qed.

Lemma diamond_notp1: forall P : A,
  diamond R (! P) |-- !(diamond R P).
Proof.
  intro. unfold notp at 2.
  rewrite <- (diamond_FF R).
  apply diamond_K.
Qed.

Lemma box_antiK {CND: @ClassicNatDed A ND}: forall P Q : A,
  [R] P --> [R] Q |-- [R] (P --> Q).
Proof.
  intros.
  apply (LEM_cases ([R] P)).
  eapply derives_trans.
  apply modus_ponens.
  apply box_positive.
  rewrite <- imp_andp_adjoint.
  apply andp_left1. trivial.
  apply andp_left1.
  eapply derives_trans.
  apply box_notp2.
  apply box_positive.
  rewrite <- imp_andp_adjoint.
  rewrite andp_comm.
  apply notp_left.
Qed.

Lemma box_K_eq {CND: @ClassicNatDed A ND}: forall P Q : A,
  [R] (P --> Q) = [R] P --> [R] Q.
Proof. intros. apply pred_ext. apply modal_K. apply box_antiK. Qed.

Lemma box_orp1 {CND : ClassicNatDed A}: forall P (Q : A),
  [R] (P || Q) |-- ([R] P) || ([R] Q).
Proof.
  intros.
  apply (LEM_cases ([R] P)).
  apply andp_left1. apply orp_right1. trivial.
  apply orp_right2.
  eapply derives_trans.
  apply andp_derives.
  apply box_notp2.
  trivial.
  rewrite <- box_andp.
  apply box_positive.
  rewrite andp_comm.
  rewrite distrib_orp_andp.
  apply orp_left.
  apply notp_left.
  apply andp_left1. trivial.
Qed.

Lemma box_orp {CND : ClassicNatDed A}: forall P (Q : A),
  [R] (P || Q) = ([R] P) || ([R] Q).
Proof. intros. apply pred_ext. apply box_orp1. apply box_orp2. Qed.

Lemma diamond_andp2 {CND : ClassicNatDed A}: forall P (Q : A),
  diamond R P && diamond R Q |--
  diamond R (P && Q).
Proof.
  intros.
  unfold diamond.
  rewrite <- deMorgan_orp.
  apply notp_derives.
  rewrite deMorgan_andp.
  apply box_orp1.
Qed.

Lemma diamond_andp {CND : ClassicNatDed A}: forall P (Q : A),
  diamond R (P && Q) = diamond R P && diamond R Q .
Proof. intros. apply pred_ext. apply diamond_andp1. apply diamond_andp2. Qed.

Lemma weakD {CND : ClassicNatDed A}: forall (P : A),
  [R] P |-- diamond R P || [R] FF.
Proof.
  intro.
  apply (LEM_cases (diamond R P)).
  apply andp_left1. apply orp_right1. trivial.
  apply orp_right2.
  unfold diamond. rewrite notnot.
  rewrite <- box_andp.
  apply box_positive.
  rewrite andp_comm.
  apply notp_left.
Qed.

Lemma box_exp1 {CND : ClassicNatDed A} {B}: inhabited B -> forall P,
  box R (EX b : B, P b) |-- EX b : B, box R (P b).
Proof.
  intros.
  eapply derives_trans.
  apply weakD.
  apply orp_left.
  rewrite diamond_exp.
  apply exp_derives. intro b.
  apply modal_CD.
  destruct H as [b].
  apply exp_right with b.
  apply box_positive.
  apply FF_left.
Qed.

Lemma diamond_allp2 {CND : ClassicNatDed A} {B}: inhabited B -> forall (P : B -> A),
  ALL b : B, diamond R (P b) |-- diamond R (ALL b : B, P b).
Proof.
  intros. unfold diamond.
  apply PBC.
  rewrite notnot.
  rewrite deMorgan_allp.
  rewrite <- deMorgan_exp.
  rewrite andp_comm.
  rewrite imp_andp_adjoint.
  eapply derives_trans. 2: apply notnot2.
  apply box_exp1. trivial.
Qed.

Lemma diamond_allp {CND : ClassicNatDed A} {B}: inhabited B -> forall (P : B -> A),
  diamond R (ALL b : B, P b) = ALL b : B, diamond R (P b).
Proof. intros. apply pred_ext. apply diamond_allp1. apply diamond_allp2. trivial. Qed.

End ModalLogic_CD.

(* total function *)
Section ModalLogic_D_CD.

Context {R : RT}.
Context {MLD : Modal_D R}.
Context {MLCD : Modal_CD R}.

Lemma box_notp {CND: @ClassicNatDed A ND}: forall (P : A),
  [R] (! P) = ! ([R] P).
Proof. intros. apply pred_ext. apply box_notp1. apply box_notp2. Qed.

Lemma diamond_not: forall P Q : A,
  diamond R (! P) = !(diamond R P).
Proof. intros. apply pred_ext. apply diamond_notp1. apply diamond_notp2. Qed.

Lemma diamond_K_eq {CND: @ClassicNatDed A ND}: forall P Q : A,
  diamond R (P --> Q) = diamond R P --> diamond R Q.
Proof. intros. apply pred_ext. apply diamond_K. apply diamond_antiK. Qed.

End ModalLogic_D_CD.

(* reflexive and functional, i.e. the identity relation *)
Section ModalLogic_T_CD.

Context {R : RT}.
Context {MLT : Modal_T R}.
Context {MLCD : Modal_CD R}.

Lemma diamond_T: forall P : A,
  diamond R P |-- P.
Proof.
  intro.
  eapply derives_trans.
  apply modal_CD.
  apply modal_T.
Qed.

Lemma diamond_T_eq: forall P : A,
  diamond R P = P.
Proof. intro. apply pred_ext. apply diamond_T. apply diamond_CT. Qed.

End ModalLogic_T_CD.

Section ModalLogic_seq.

Context {MLS: ModLogSeq ML}.

Lemma seqR_diamond1 {CND: @ClassicNatDed A ND}: forall R1 R2 (P : A),
    diamond (seqR R1 R2) P |-- diamond R1 (diamond R2 P).
Proof.
  intros. unfold diamond.
  apply notp_derives.
  rewrite seqR_box.
  apply box_positive.
  apply notnot1.
Qed.

Lemma seqR_diamond2 : forall R1 R2 (P : A),
    diamond R1 (diamond R2 P) |-- diamond (seqR R1 R2) P.
Proof.
  intros. unfold diamond.
  apply notp_derives.
  rewrite seqR_box.
  apply box_positive.
  apply notnot2.
Qed.

Lemma seqR_diamond {CND: @ClassicNatDed A ND}: forall R1 R2 (P : A),
    diamond (seqR R1 R2) P = diamond R1 (diamond R2 P).
Proof. intros. apply pred_ext. apply seqR_diamond1. apply seqR_diamond2. Qed.

End ModalLogic_seq.

(* dual *)
Section ModalLogic_dual.

Context {MLD: ModLogDual ML}.

Lemma diamond_antibox_adjoint: forall R (P Q : A),
  diamond R P |-- Q  <->
  P |-- [antiR R] Q.
Proof.
  split; intro.
  rewrite <- antidiamond_box_adjoint.
  rewrite antiR_involution. trivial.
  rewrite <- antidiamond_box_adjoint in H.
  rewrite antiR_involution in H. trivial.
Qed.

Lemma diamond_antibox_left: forall R P,
  diamond R ([antiR R] P) |-- P.
Proof.
  intros.
  rewrite diamond_antibox_adjoint.
  trivial.
Qed.

Lemma antibox_diamond2: forall R P,
  P |-- [antiR R] (diamond R P).
Proof.
  intros.
  apply diamond_antibox_adjoint.
  trivial.
Qed.

Section ModalLogic_CD_dualD.

Context {R : RT}.
Context {MLCD : Modal_CD R}.
Context {MLDD : Modal_D (antiR R)}.

Lemma antibox_diamond_adjoint: forall P Q : A,
  P |-- diamond R Q ->
  [antiR R] P |-- Q.
Proof.
  intros.
  eapply derives_trans.
  apply modal_D.
  rewrite diamond_antibox_adjoint.
  rewrite antiR_involution.
  eapply derives_trans.
  apply H.
  apply modal_CD.
Qed.

Lemma antibox_diamond1: forall P,
  [antiR R] (diamond R P) |-- P.
Proof.
  intros.
  apply antibox_diamond_adjoint.
  trivial.
Qed.

Lemma antibox_diamond_eq: forall P,
  [antiR R] (diamond R P) = P.
Proof. intro. apply pred_ext. apply antibox_diamond1. apply antibox_diamond2. Qed.

Section ModalLogic_CD_dualD_dualCD.

Context {MLDCD : Modal_CD (antiR R)}.

Lemma diamond_antibox_right {CND: @ClassicNatDed A ND}: forall P,
  NTD R && P |-- diamond R ([antiR R] P).
Proof.
  intro. unfold NTD.
  rewrite imp_andp_adjoint.
  rewrite diamond_antibox_adjoint.
  rewrite box_K_eq.
  rewrite antibox_diamond_eq.
  rewrite <-imp_andp_adjoint.
  rewrite TT_andp. trivial.
Qed.

Lemma diamond_MN {CND: @ClassicNatDed A ND}: forall P Q : A,
  [antiR R] P |-- Q ->
  NTD R && P |-- diamond R Q.
Proof.
  intros.
  eapply derives_trans.
  apply diamond_antibox_right.
  apply diamond_positive.
  trivial.
Qed.

Lemma dot_WCK {CND: @ClassicNatDed A ND}: forall P Q,
  NTD R && ((diamond R P) --> (diamond R Q)) |-- diamond R (P --> Q).
Proof.
  intros. apply diamond_MN.
  eapply derives_trans.
  apply modal_K.
  do 2 rewrite antibox_diamond_eq.
  trivial.
Qed.

End ModalLogic_CD_dualD_dualCD.

End ModalLogic_CD_dualD.

End ModalLogic_dual.

(* symmetric *)
Section ModalLogic_B.

End ModalLogic_B.


(* finite chains *)
Section ModalLogic_W.

End ModalLogic_W.

End ModalLogic.

