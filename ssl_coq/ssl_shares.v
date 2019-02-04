Require Import VST.msl.msl_direct.

Lemma feq_app {A} {B} : forall f g : A -> B,
  f = g ->
  forall a, f a = g a.
Proof.
  intros. subst. trivial.
Qed.

Program Definition pcomp (p : pshare) (Pf : p <> pfullshare) : pshare :=
  Share.comp p.
Next Obligation.
  do 2 intro.
  apply unit_self_unit in H. clear x.
  destruct p. destruct H as [? _]. simpl in *.
  rewrite Share.glb_idem in H.
  apply Pf. apply exist_ext.
  apply Share.ord_antisym.
  apply Share.top_correct.
  rewrite <- (Share.comp_inv x).
  rewrite H.
  rewrite Share.ord_spec1.
  rewrite <- (Share.comp_inv fullshare).
  rewrite <- Share.demorgan1.
  rewrite Share.lub_bot.
  trivial.
Qed.

Program Definition plub (p1 p2 : pshare) : pshare :=
  Share.lub p1 p2.
Next Obligation.
  do 2 intro.
  destruct p1, p2, H.
  simpl in *.
  rewrite <- H0 in H.
  rewrite Share.lub_assoc in H.
  rewrite <- Share.distrib2 in H.
  rewrite Share.glb_absorb in H. clear H0 x.
  assert (x0 = Share.bot). {
    apply Share.ord_antisym.
    rewrite Share.ord_spec2.
    pattern Share.bot at 1.
    rewrite <- H.
    rewrite <- Share.lub_assoc.
    rewrite Share.lub_idem. trivial.
    apply Share.bot_correct. }
  subst x0.
  apply (n Share.bot).
  rewrite <- identity_unit_equiv.
  apply bot_identity.
Qed.

Lemma rel_nonunit_nonunit : forall p1 p2 : pshare,
  nonunit (Share.rel (proj1_sig p1) (proj1_sig p2)).
Proof.
  destruct p1, p2.
  intro. intro.
  apply (@share_rel_nonidentity x x0).
  intro. apply (n x).
  rewrite identity_unit_equiv in H0. trivial.
  intro. apply (n0 x0).
  rewrite identity_unit_equiv in H0. trivial.
  rewrite identity_unit_equiv.
  simpl in H.
  eapply unit_self_unit.
  apply H.
Qed.

Program Definition pbow (p1 p2 : pshare) : pshare :=
  Share.rel p1 p2.
Next Obligation.
  apply rel_nonunit_nonunit.
Qed.

Class Shares (t : Type) : Type := mkShares {
  shares_J : Join t;
  shares_P : Perm_alg t;
  shares_S : Sep_alg t;
  shares_C : Canc_alg t;
  share_0 : t;
  share_0_identity : identity share_0;
  share_identity_0 : forall x : t, identity x -> x = share_0;
  share_1 : t;
  share_1_top : forall x : t, join_sub x share_1;
  share_mult : t -> t -> t;
  share_mult_share_1 : forall x,
    share_mult x share_1 = x;
  share_share_1_mult : forall x,
    share_mult share_1 x = x;
  share_mult_share_0 : forall x,
    share_mult x share_0 = share_0;
  share_share_0_mult : forall x,
    share_mult share_0 x = share_0;
  share_mult_canc_left : forall x y z,
    x <> share_0 ->
    share_mult x y = share_mult x z ->
    y = z;
  share_mult_canc_right : forall x y z,
    x <> share_0 ->
    share_mult y x = share_mult z x ->
    y = z;
  share_mult_assoc : forall a b c : t,
    share_mult a (share_mult b c) = share_mult (share_mult a b) c;
  share_join_mult : forall a b c d : t,
    join a b c ->
    join (share_mult a d) (share_mult b d) (share_mult c d);
  share_mult_join : forall a b c d : t,
    join (share_mult a d) (share_mult b d) (share_mult c d) ->
    join a b c;
}.

Goal forall a b c d : pshare,
  join a b c ->
  join (pbow d a) (pbow d b) (pbow d c).
Proof.
  unfold pbow. intros.
  destruct H. unfold lifted_obj in *. split; simpl in *.
  rewrite <- Share.rel_preserves_glb.
  rewrite H. apply Share.rel_bot1.
  rewrite <- Share.rel_preserves_lub.
  rewrite H0. trivial.
Qed.

Goal forall a b c d : pshare,
  join (pbow d a) (pbow d b) (pbow d c) ->
  join a b c.
Proof.
  unfold pbow. intros.
  destruct H. split; unfold lifted_obj in *; simpl in *.
  rewrite <- Share.rel_preserves_glb in H.
  pose proof (Share.rel_bot1 (proj1_sig d)).
  rewrite <- H1 in H.
  apply Share.rel_inj_l in H. trivial.
  pose proof (pshare_not_identity d).
  intro. apply H2. rewrite identity_unit_equiv. destruct d. simpl in *. subst x.
  split. apply Share.glb_bot. apply Share.lub_bot.
  rewrite <- Share.rel_preserves_lub in H0.
  apply Share.rel_inj_l in H0. trivial.
  pose proof (pshare_not_identity d).
  intro. apply H1. rewrite identity_unit_equiv. destruct d. simpl in *. subst x.
  split. apply Share.glb_bot. apply Share.lub_bot.
Qed.

Existing Instance shares_J.
Existing Instance shares_P.
Existing Instance shares_S.
Existing Instance shares_C.

Lemma share_top_1 {A} `{Shares A}: forall x : A,
  (forall y : A, join_sub y x) ->
  x = share_1.
Proof.
  intros.
  specialize (H0 share_1).
  pose proof (share_1_top x).
  destruct H0 as [y ?].
  destruct H1 as [z ?].
  destruct (join_assoc H0 H1) as [e [? ?]].
  apply split_identity in H2.
  apply join_comm in H0. apply H2 in H0. auto.
  eapply unit_identity. apply join_comm in H3. apply H3.
Qed.
