Require Import VST.msl.msl_direct.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.

Require Import neg_logic.
Require Import modal_logic.

Open Local Scope logic.

Lemma sa_prop_left {A : Type}: forall (P : Prop) (Q : pred A),
  (P -> predicates_sa.derives (predicates_sa.prop True) Q) -> 
       (predicates_sa.derives (predicates_sa.prop P) Q).
Proof. compute; auto. Qed.

Lemma sa_prop_right {A}: forall (P : Prop) (Q : pred A),
  P -> (predicates_sa.derives Q (predicates_sa.prop P)).
Proof. compute; auto. Qed.

Lemma sa_prop_imp_prop_left {A}: forall (P Q: Prop), 
  @predicates_sa.derives A (predicates_sa.imp (predicates_sa.prop P) (predicates_sa.prop Q)) (predicates_sa.prop (P -> Q)).
Proof. compute; auto. Qed.

Lemma sa_allp_prop_left {A}: forall (B: Type) (P: B -> Prop), 
  @predicates_sa.derives A (predicates_sa.allp (fun b => predicates_sa.prop (P b))) (predicates_sa.prop (forall b, P b)).
Proof. compute; auto. Qed.

Instance NDdirect A : NatDed (pred A).
apply (mkNatDed (pred A) predicates_sa.andp 
                            predicates_sa.orp 
                            (@predicates_sa.exp A) 
                            (@predicates_sa.allp A) 
                            predicates_sa.imp 
                            predicates_sa.prop 
                            (@predicates_sa.derives A)).
apply predicates_sa.pred_ext.
apply predicates_sa.derives_refl.
apply predicates_sa.derives_trans.
apply predicates_sa.andp_right.
apply predicates_sa.andp_left1.
apply predicates_sa.andp_left2.
apply predicates_sa.orp_left.
apply predicates_sa.orp_right1.
apply predicates_sa.orp_right2.
intros. eapply predicates_sa.exp_right. apply H.
intros. eapply predicates_sa.exp_left. apply H.
intros. eapply predicates_sa.allp_left. apply H.
intros. eapply predicates_sa.allp_right. apply H.
apply predicates_sa.imp_andp_adjoint.
(* These ones aren't in the library for some reason. *)
apply sa_prop_left.
apply sa_prop_right.
apply sa_prop_imp_prop_left.
apply sa_allp_prop_left.
Defined.

Require Import Classical.
Instance CNDdirect A : (@ClassicNatDed (pred A) (NDdirect A)).
repeat intro. destruct (classic (P a)). left; trivial. right; trivial. Qed.

Instance MLdirect (A : Type): @ModLog (A -> A -> Prop) (pred A) (NDdirect A).
  apply (mkModLog (A -> A -> Prop) (pred A) _ (fun (R : A -> A -> Prop) P a => forall a', R a a' -> P a')).
  + repeat intro. apply H. apply I.
  + repeat intro. eapply H; auto.
  + repeat intro. eapply H; auto.
Defined.

Instance MLSdirect (A : Type): @ModLogSeq (A -> A -> Prop) (A -> Prop) (NDdirect A) (MLdirect A).
  apply (mkModLogSeq _ _ _ _ (fun R1 R2 x y => exists z, R1 x z /\ R2 z y)).
  intros. apply pred_ext.
  * repeat intro.
    specialize (H a'0). apply H.
    exists a'. split; trivial.
  * repeat intro.
    destruct H0 as [z [? ?]].
    specialize (H z H0 a' H1). trivial.
Defined.

Lemma diamond_unfold: forall A R (P : pred A) a,
  (diamond R P) a <-> exists a', R a a' /\ P a'.
Proof.
  split; intro.
  + apply NNPP. intro.
    apply H. repeat intro.
    apply H0.
    exists a'. split; trivial.
  + destruct H as [a' [? ?]].
    intro.
    specialize (H1 a' H).
    destruct H1. trivial.
Qed.

Instance MLDdirect (A : Type): @ModLogDual (A -> A -> Prop) (A -> Prop) (NDdirect A) (MLdirect A).
  apply (mkModLogDual _ _ _ _ (fun R x y => R y x)).
  + intros. extensionality x y. trivial.
  + split; repeat intro.
    * apply H. intro. specialize (H2 a H1). destruct H2. trivial. 
    * rewrite diamond_unfold in H0. destruct H0 as [a' [? ?]].
      specialize (H a' H1 a H0). trivial.
Defined.

(* Instantiating correspondence theory *)
(* Note: we could do these things both ways? *)
Lemma reflexive_T {A}: forall (R : A -> A -> Prop),
  (forall a, R a a) ->
  Modal_T R.
Proof.
  repeat intro.
  specialize (H a).
  specialize (H0 a H).
  trivial.
Qed.

Lemma transitive_4 {A}: forall (R : A -> A -> Prop),
  (forall a1 a2 a3, R a1 a2 -> R a2 a3 -> R a1 a3) ->
  Modal_4 R.
Proof.
  repeat intro.
  specialize (H a a' a'0 H1 H2).
  specialize (H0 a'0 H).
  trivial.
Qed.

Lemma dense_C4 {A}: forall (R : A -> A -> Prop),
  (forall a1 a2, R a1 a2 -> exists a12, R a1 a12 /\ R a12 a2) ->
  Modal_C4 R.
Proof.
  repeat intro.
  specialize (H a a' H1).
  destruct H as [a12 [? ?]].
  specialize (H0 a12 H a' H2).
  trivial.
Qed.

Lemma serial_D {A}: forall (R : A -> A -> Prop),
  (forall a1, exists a2, R a1 a2) ->
  Modal_D R.
Proof.
  repeat intro.
  specialize (H a).
  destruct H as [a' ?].
  specialize (H0 a' H).
  specialize (H1 a' H).
  destruct H1. trivial.
Qed.

Lemma functional_CD {A}: forall (R : A -> A -> Prop),
  (forall a1 a2 a3, R a1 a2 -> R a1 a3 -> a2 = a3) ->
  Modal_CD R.
Proof.
  repeat intro.
  rewrite diamond_unfold in H0.
  destruct H0 as [a'' [? ?]].
  specialize (H a a' a'' H1 H0). subst a''.
  trivial.
Qed.

Lemma symmetric_B {A}: forall (R : A -> A -> Prop),
  (forall a1 a2, R a1 a2 -> R a2 a1) ->
  Modal_B R.
Proof.
  repeat intro.
  apply H in H1.
  specialize (H2 a H1).
  destruct H2. trivial.
Qed.

Inductive finite_chains {A} (R : A -> A -> Prop) : A -> Prop :=
 | re : forall w, 
   (forall w', R w w' -> finite_chains R w') -> (* if every reachable state will end *)
   finite_chains R w. (* then we will end *)

Lemma finite_chains_W {A}: forall (R : A -> A -> Prop),
  (forall w, finite_chains R w) ->
  Modal_W R.
Proof.
  repeat intro. clear H1.
  specialize (H a).
  induction H.
  apply H0.
  repeat intro.
  specialize (H1 a' H2).
  trivial.
Qed.

Lemma sa_exclude_elsewhere {A} {J : Join A} {PA: @Perm_alg A J} {SA: @Sep_alg A J} : forall (P Q : pred A),
  (predicates_sa.sepcon P Q) |-- (predicates_sa.sepcon (predicates_sa.andp P (predicates_sa.ewand Q TT)) Q).
Proof. 
  intros.
  simpl.
  do 2 intro. destruct H as [h1 [h2 [? [? ?]]]].
  exists h1, h2. repeat (split; trivial).
  exists h2, a. auto.
Qed.

Instance SLdirect A {J : Join A} {PA: @Perm_alg A J} {SA: @Sep_alg A J} : @SepLog (pred A) (NDdirect A).
apply (mkSepLog (pred A) (NDdirect A) emp 
                                      predicates_sa.sepcon 
                                      predicates_sa.wand 
                                      predicates_sa.ewand); simpl.
apply predicates_sa.sepcon_assoc.
apply predicates_sa.sepcon_comm.
intros. rewrite predicates_sa.wand_sepcon_adjoint. tauto.
apply predicates_sa.sepcon_andp_prop.
intros. apply predicates_sa.sepcon_derives; trivial.
apply predicates_sa.ewand_sepcon.
apply predicates_sa.ewand_TT_sepcon.
apply sa_exclude_elsewhere. (* not in MSL *)
apply predicates_sa.ewand_conflict.
Defined.

Instance CSdirect A {J : Join A} {PA: @Perm_alg A J} {CA: @Canc_alg A J} {SA: @Sep_alg A J} : @ClassicalSep (pred A) (NDdirect A) (SLdirect A).
constructor. intro.
apply pred_ext; repeat intro.
destruct H as [a0 [a1 [? [? ?]]]].
spec H1 a0 a (join_comm H). subst a0. trivial.
exists a, (core a). split.
apply join_comm, core_unit.
split; trivial.
apply core_identity.
Defined.


