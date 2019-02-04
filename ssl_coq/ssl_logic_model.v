Require Import VST.msl.msl_direct.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.

Require Import ssl_shares.
Require Import neg_logic.
Require Import modal_logic.
Require Import ssl_logic.
Require Import ssl_algebra.
Require Import logics_direct.

(* Now we show that our logics have a model. *)

Definition precisely' {A} {J : Join A} (P : pred A) : pred A :=
  fun w => forall w1 w2, P w1 -> P w2 -> join_sub w1 w -> join_sub w2 w -> w1 = w2.

Instance PSLdirect (A : Type) {J : Join A} {PA : @Perm_alg A J} {SA : @Sep_alg A J} {CA : @Canc_alg A J} : @PreciseSepLog (pred A) (NDdirect A) (@SLdirect A J PA SA).
  apply (mkPreciseSepLog _ _ _ predicates_sa.precise precisely'); repeat intro.
  + destruct H0, H0, H0, H0, H1, H1, H1, H2, H3.
    spec H x x1 H2 H3. spec H. exists x0. trivial. spec H. exists x2. trivial. subst x1. clear H3.
    pose proof (join_canc (join_comm H0) (join_comm H1)). subst x2.
    exists x, x0. split; trivial. split; trivial. split; trivial.
  + destruct H3, H4. spec H (fun w' => w' = x) (fun w' => w' = x0). spec H a H0.
    assert ((P * (fun w' : A => w' = x) && (P * (fun w' : A => w' = x0))) a)%logic. {
        split; [exists w1, x | exists w2, x0]; tauto. }
    apply H in H5. destruct H5 as [wa [wb [? [? [? ?]]]]]. subst x x0.
    apply (join_canc H3 H4).
  + split; repeat intro.
    - eapply H; eauto.
    - eapply H; eauto. apply I.
  + destruct H. eapply H; eauto.
  + destruct H2 as [x1 ?].
    destruct H3 as [x2 ?].
    spec H0 x1 x2 a. spec H0.
    destruct H4, H5.
    rewrite andp_assoc.
    split; trivial. split; [exists w1, x | exists w2, x0]; split; auto; split; auto; apply I.
    compute in H0. subst x2.
    eapply H; eauto.
  + destruct H2 as [w1a [w1b [? [? ?]]]].
    destruct H3 as [w2a [w2b [? [? ?]]]].
    assert (w1a = w2a). {
      eapply H; eauto; eapply join_sub_trans.
      exists w1b; eauto.
      eauto.
      exists w2b; eauto.
      eauto. }
    subst w2a.
    assert (w1b = w2b). {
      eapply H0; eauto; eapply join_sub_trans.
      exists w1a; eauto.
      eauto.
      exists w1a. apply join_comm in H3. apply H3.
      trivial. }
    subst w2b.
    eapply join_eq; eauto.
(*
  + eapply H; eauto.
    destruct H2. exists w1, x. repeat (split; auto).

  + split; repeat intro.
    - destruct H0 as [[a1 [a2 [? [? ?]]]] [a3 [a4 [? [? ?]]]]].
      spec H a a1 a3 H1 H4. spec H. exists a2; trivial. spec H. exists a4; trivial. subst a3.
      exists a1, a2. split; trivial. split; trivial. split; trivial.
      pose proof (join_canc (join_comm H0) (join_comm H3)). subst a4. trivial.
    - destruct H2, H3. spec H (fun w' => w' = x) (fun w' => w' = x0).
      assert ((P * (fun w' : A => w' = x) && (P * (fun w' : A => w' = x0))) w)%logic. {
        split; [exists w1, x | exists w2, x0]; tauto. }
        apply H in H4. destruct H4 as [wa [wb [? [? [? ?]]]]]. subst x x0.
      pose proof (join_canc H2 H3). trivial.
  + destruct H1.
  + do 4 red in H0, H1.
    destruct H2, H3.
    pose proof (H0 _ _ H2). subst x.
    pose proof (H1 _ _ H3). subst x0.
    eapply same_identity.
    * repeat intro. auto.
    * apply H2.
    * repeat intro. auto.
    * apply H3.
*)
(*
  + destruct H1 as [wa [wb [? [? ?]]]].
    destruct H2 as [wa' [wb' [? [? ?]]]].
    destruct H0 as [w' [w'' [? [? ?]]]].
    pose proof (H a wa wa' H5 H7).
    pose proof (H a w' wa H9 H5).
    assert (join_sub wa a) by (apply join_sub_trans with w1; trivial; exists wb; trivial).
    spec H11; trivial.
    spec H11. apply join_sub_trans with w2; trivial. exists wb'; trivial.
    spec H12. exists w''. trivial.
    spec H12 H13. subst wa' w'. clear H7 H9.
    spec H10 wb wb' H6 H8.
    spec H10.
    destruct H3. destruct (join_assoc H1 H3) as [f [? ?]].
    pose proof (join_canc (join_comm H0) (join_comm H9)). subst f. exists x. trivial.
    spec H10.
    destruct H4. destruct (join_assoc H2 H4) as [f [? ?]].
    pose proof (join_canc (join_comm H0) (join_comm H9)). subst f. exists x. trivial.
    subst wb'.
    apply (join_eq H1 H2).
*)
Defined.

Instance SSA_ScaledSepLog (A : Type) {J : Join A} {PA : @Perm_alg A J} {SA : @Sep_alg A J} {CA : @Canc_alg A J} {SSA : @SSA A J}: 
  @ScaledSepLog (pred A) (A -> A -> Prop) (NDdirect A) (SLdirect A) (PSLdirect A) (MLdirect A) (MLSdirect A).
  apply (mkSSL _ _ _ _ _ _ _ (fun sh a => a = force sh a) (fun sh a b => mul sh b = a)).
  + repeat intro. rewrite force_identity; trivial.
  + repeat intro. apply pred_ext; repeat intro.
    - destruct H as [a1 [a2 [? [? ?]]]].
      rewrite H0, H1 in H.
      rewrite (force_join_eq pi a1 a2 a); auto.
    - destruct (join_ex_units a) as [ea ?].
      exists ea, a.
      split; trivial.
      apply unit_identity in u.
      rewrite (force_identity ea u).
      split; trivial.
  + intros. split; repeat intro.
    - rewrite diamond_unfold in H0. destruct H0 as [a' [? ?]].
      subst a.
      specialize (H a' H1). simpl in H.
      pattern a' at 1. rewrite H.
      rewrite mul_force. rewrite force_mul. trivial.
    - spec H (mul pi' a). spec H. 
      rewrite diamond_unfold. exists a.
      split; trivial.
      rewrite force_mul in H.
      rewrite <- mul_force in H.
      apply mul_inj in H.
      trivial.
  + intro. apply functional_CD.
    intros. rewrite <- H0 in H.
    apply mul_inj in H. trivial.
  + apply reflexive_T. apply mul_top.
  + intros. extensionality a b. unfold seqR. simpl.
    apply prop_ext; split; intro.
    destruct H as [? [? ?]].
    subst x. rewrite <- mul_mul. trivial.
    rewrite <- mul_mul in H.
    exists (mul sh2 b). split; auto.
  + split; repeat intro.
    - rewrite diamond_unfold in H0, H1.
      destruct H0 as [wb1 [? ?]]. destruct H1 as [wb2 [? ?]].
      subst w1 w2.
      specialize (H (force pfullshare w) wb1 wb2 H4 H5).
      f_equal. destruct H2, H3. apply H; clear H H4 H5;
      eapply join_sub_trans; apply cjoin_sub_join_sub.
      apply force_join_sub_full. 2: apply force_join_sub_full.
      pose proof (force_join_sub_hom (mul sh wb1) w).
      spec X. exists x. trivial. spec X pfullshare.
      rewrite force_mul in X. trivial.
      pose proof (force_join_sub_hom (mul sh wb2) w).
      spec X. exists x0. trivial. spec X pfullshare.
      rewrite force_mul in X. trivial.
    - spec H w (mul sh w1) (mul sh w2).
      spec H. rewrite diamond_unfold. exists w1. tauto.
      spec H. rewrite diamond_unfold. exists w2. tauto.
      spec H. eapply join_sub_trans. 2: apply H2. apply cjoin_sub_join_sub. apply mul_join_sub.
      spec H. eapply join_sub_trans. 2: apply H3. apply cjoin_sub_join_sub. apply mul_join_sub.
      apply mul_inj in H. trivial.
  + intros. apply pred_ext; repeat intro.
    - rewrite diamond_unfold in H. destruct H as [a' [? [? ?]]].
      split; auto.
      rewrite (mul_identity a' H0 sh) in H.
      subst a'. trivial.
    - destruct H.
      specialize (H0 (mul sh a)). simpl in H0.
      do 2 rewrite (mul_identity a H sh) in H0.
      spec H0; trivial.
      apply H0.
      split; trivial.
  + repeat intro. (* dot_plus1 *)
    rewrite diamond_unfold in H0. destruct H0 as [b [? ?]].
    pose proof (mul_join _ _ _ H b (mul sh3 b)). 
    destruct H2 as [_ ?]. spec H2; trivial.
    exists (mul sh1 b), (mul sh2 b).
    subst a. split; trivial.
    do 2 rewrite diamond_unfold.
    split; exists b; split; trivial.
  + repeat intro. (* dot_plus2 *)
    destruct H1 as [a1 [a2 [? [? ?]]]].
    rewrite diamond_unfold in *.
    destruct H3 as [a1' [? ?]].
    destruct H4 as [a2' [? ?]].
    subst a1 a2.
    assert (a1' = a2'). {
      apply (H (force pfullshare a) a1' a2' H5 H6).
      - eapply join_sub_trans with (force pfullshare (mul sh1 a1')).
        rewrite force_mul.
        apply cjoin_sub_join_sub.
        apply force_join_sub_full.
        apply cjoin_sub_join_sub.
        apply force_join_sub_hom.
        exists (mul sh2 a2'); trivial.
      - eapply join_sub_trans with (force pfullshare (mul sh2 a2')).
        rewrite force_mul.
        apply cjoin_sub_join_sub.
        apply force_join_sub_full.
        apply cjoin_sub_join_sub.
        apply force_join_sub_hom.
        exists (mul sh1 a1'); auto. }
    subst a2'.
    specialize (H2 a1').
    apply H2; trivial.
    pose proof (mul_join _ _ _ H0 a1' a).
    rewrite H3 in H1. auto.
  + intros. apply pred_ext; repeat intro. (* dot_star *)
    - rewrite diamond_unfold in H1. destruct H1 as [a' [? ?]].
      destruct H2 as [a'1 [a'2 [? [? ?]]]].
      pose proof (H _ H3). pose proof (H0 _ H4). simpl in H5, H6.
      rewrite H5, H6 in H2.
      pose proof (force_join_eq _ _ _ _ H2).
      rewrite <- H7 in H2, H1.
      rewrite <- H1.
      exists (mul pi' (force pi a'1)), (mul pi' (force pi a'2)).
      repeat split; repeat rewrite diamond_unfold.
      * apply force_mul_join_hom. trivial.
      * exists (force pi a'1).
        rewrite mul_force.
        rewrite <- H5.
        split; trivial.
      * exists (force pi a'2).
        rewrite mul_force.
        rewrite <- H6.
        split; trivial.
    - destruct H1 as [a1 [a2 [? [? ?]]]].
      rewrite diamond_unfold in *.
      destruct H3 as [a1' [? ?]].
      destruct H4 as [a2' [? ?]].
      rewrite <- H3 in H1.
      rewrite <- H4 in H1.
      pose proof (H _ H5).
      pose proof (H0 _ H6). simpl in *.
      rewrite H7, H8 in H1.
      do 2 rewrite mul_force in H1.
      pose proof (force_join_eq _ _ _ _ H1).
      rewrite <- mul_force in H9.
      specialize (H2 _ H9).
      apply H2. clear H2.
      exists a1', a2'.
      split.
      rewrite <- H9 in H1.
      do 2 rewrite <- mul_force in H1.
      rewrite H7, H8.
      apply force_mul_join_hom in H1. trivial.
      split; trivial.
Defined.

Instance SSA_FracIndLog (A : Type) {J : Join A} {PA : @Perm_alg A J} {SA : @Sep_alg A J} {CA : @Canc_alg A J} {SSA : @SSA A J} {FBA: @FracBoundedAlg A J SSA}:
  @FracIndLog (pred A) (A -> A -> Prop) (NDdirect A) (SLdirect A) (PSLdirect A) (MLdirect A) (MLSdirect A) (SSA_ScaledSepLog A).
  apply (mkFracIndLog _ _ _ _ _ _ _ _ (fun a b => join_sub b a) (fun sh a b => exists b' b'', join b b' b'' /\ (uniform sh && !emp)%logic b' /\ join_sub b'' a)).
  + apply reflexive_T. apply join_sub_refl.
  + apply transitive_4. intros. eapply join_sub_trans; eauto.
  + intro. apply transitive_4. intros.
    destruct H as [b1 [b2 [? [? ?]]]].
    destruct H0 as [b3 [b4 [? [? ?]]]].
    exists b3, b4. split; trivial. split; trivial.
    eapply join_sub_trans. apply H4.
    eapply join_sub_trans. exists b1. apply H. trivial.
  + intro. apply finite_chains_W. intro. remember (quantum w pi).
    assert (n >= quantum w pi) by (subst; constructor). clear Heqn.
    revert w H. induction n; intros; constructor; intros; 
    destruct H0 as [w1 [w2 [? [[? ?] ?]]]];
    pose proof (quantum_sub w2 w pi H3);
    pose proof (quantum_uniform w' w1 w2 pi H2 H1 H0).
    - exfalso. omega.
    - spec IHn w'. spec IHn. omega. apply IHn.
  + intro. simpl. extensionality x y. apply prop_ext. split; intro.
    - destruct H as [z [[b' [b'' [? [? [? ?]]]]] ?]].
      exists b'. destruct H2.
      apply join_comm in H2.
      destruct (join_assoc H2 H) as [? [? ?]].
      exists x2. split; trivial. split; trivial.
      apply join_sub_trans with b''.
      exists x1. apply join_comm. trivial.
      exists x0. trivial.
    - destruct H as [b' [b'' [? [? ?]]]].
      exists y. split.
      exists b', b''. repeat (split; trivial).
      apply join_sub_refl.
  + intro. simpl. extensionality x y. apply prop_ext. split; intro.
    - destruct H as [z [? [b' [b'' [? [? [? ?]]]]]]].
      exists b', b''. split; trivial. split; trivial.
      eapply join_sub_trans. exists x0. apply H2. trivial.
    - destruct H as [b' [b'' [? [? ?]]]].
      exists x. split. apply join_sub_refl.
      exists b', b''. repeat (split; trivial).
  + repeat intro.
    destruct H. destruct H as [a1 [a2 [? [? ?]]]].
    exists a1, a2. split; trivial.
    split; split; trivial; simpl; intros; apply H0; eapply join_sub_trans; eauto.
  + repeat intro.
    destruct H0. destruct H0 as [a1 [a2 [? [? ?]]]].
    exists a1, a2. split; trivial.
    split; split; trivial. simpl in *. intros.
    apply H1. destruct H4 as [b' [b'' [? [? ?]]]].
    exists b', b''. split; trivial. split; trivial.
    eapply join_sub_trans. apply H6. exists a2. trivial.
    apply H1.
    exists a1, a. split. apply join_comm. trivial.
    split. apply H. trivial.
    apply join_sub_refl.
Qed.
