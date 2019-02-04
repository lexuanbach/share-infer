Require Import VST.msl.msl_direct.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.

Require Import ssl_shares.
Require Import neg_logic.
Require Import modal_logic.
Require Import ssl_logic.

(* We use these so that SSAs can be built with positive SAs *)
Definition non_positive (T : Type) {J : Join T} : Prop :=
  exists t, unit_for t t.

Inductive wjoin_sub {A} {J : Join A} : A -> A -> Type :=
  | wjoin_sub_refl : forall a, wjoin_sub a a
  | wjoin_sub_sub  : forall a b c, join a b c -> wjoin_sub a c.

Lemma wjoin_sub_cjoin_sub {A} {J : Join A} {PA : @Perm_alg A J} {SA : @Sep_alg A J}: forall a1 a2,
  wjoin_sub a1 a2 -> cjoin_sub a1 a2.
Proof.
  intros.
  destruct X.
  exists (core a).
  apply join_comm.
  apply core_unit.
  exists b. trivial.
Qed.

Lemma cjoin_sub_join_sub {A} {J : Join A}: forall a b : A,
  cjoin_sub a b ->
  join_sub a b.
Proof.
  intros. destruct X. exists x. trivial.
Qed.

Class SSA (A : Type) {J : Join A} : Type := mkSSA {
  force : pshare -> A -> A;
  mul : pshare -> A -> A;

  force_force: forall a sh sh', force sh (force sh' a) = force sh a; (* Do we use this one yet? *)
  force_mul: forall a sh sh', force sh (mul sh' a) = force sh a;
  mul_force: forall a sh sh', mul sh (force sh' a) = force (pbow sh' sh) a;
  mul_mul : forall pi1 pi2 a, mul pi1 (mul pi2 a) = mul (pbow pi2 pi1) a;

  (* True on Q and T *)
  force_identity' : non_positive A -> forall a, identity a -> forall pi, force pi a = a;
  force_join_sub_full' : forall a, wjoin_sub a (force pfullshare a);
  force_join_sub_hom': forall a b, wjoin_sub a b -> forall sh, wjoin_sub (force sh a) (force sh b);

  (* Not true on Q  -- is this essentially disjointness at the SSA level? *)
  force_join_eq: forall pi a b c, join (force pi a) (force pi b) c -> force pi c = c;

  (* True on Q and T *)
  mul_top : forall a, mul pfullshare a = a;
  mul_identity' : non_positive A -> forall a, identity a -> forall sh, mul sh a = a;
  mul_inj : forall sh a1 a2, mul sh a1 = mul sh a2 -> a1 = a2;

  (* Probably true on both *)
  mul_join : forall sh1 sh2 sh3,
    join sh1 sh2 sh3 -> forall b c,
    join (mul sh1 b) (mul sh2 b) c <-> c = mul sh3 b;

  (* True on T, overly weak on Q? *)
  force_mul_join_hom : forall sh sh' a b c, 
    join (force sh' a) (force sh' b) (force sh' c) <->
    join (mul sh (force sh' a)) (mul sh (force sh' b)) (mul sh (force sh' c));

  mul_join_sub' : forall sh a, wjoin_sub (mul sh a) a;
}.

(* When we have the appropriate additional axioms, which we expect to have by the end (but maybe not
   as we build the structure compositionally) we can get stronger versions of some of the properties. *)

Lemma force_identity {A} {J : Join A} {S : @SSA A J} {PA : @Perm_alg A J} {CA : @Canc_alg A J} {SA : @Sep_alg A J}: 
  forall a, identity a -> forall pi, force pi a = a.
Proof.
  intros.
  apply force_identity'; trivial.
  exists a.
  rewrite <- identity_unit_equiv. trivial.
Qed.

Lemma mul_identity {A} {J : Join A} {S : @SSA A J} {PA : @Perm_alg A J} {CA : @Canc_alg A J} {SA : @Sep_alg A J}: 
  forall a, identity a -> forall sh, mul sh a = a.
Proof.
  intros.
  apply mul_identity'; trivial.
  exists a.
  rewrite <- identity_unit_equiv. trivial.
Qed.

Lemma force_join_sub_full {A} {J : Join A} {S : @SSA A J} {PA : @Perm_alg A J} {SA : @Sep_alg A J}: 
  forall a, cjoin_sub a (force pfullshare a).
Proof.
  intros.
  apply wjoin_sub_cjoin_sub.
  apply force_join_sub_full'.
Qed.

Lemma force_join_sub_hom {A} {J : Join A} {S : @SSA A J} {PA : @Perm_alg A J} {SA : @Sep_alg A J}: 
  forall a b, cjoin_sub a b -> forall sh, cjoin_sub (force sh a) (force sh b).
Proof.
  intros.
  apply wjoin_sub_cjoin_sub.
  apply force_join_sub_hom'.
  destruct X.
  apply wjoin_sub_sub with x.
  trivial.
Qed.

Lemma mul_join_sub {A} {J : Join A} {S : @SSA A J} {PA : @Perm_alg A J} {SA : @Sep_alg A J}:
  forall sh (a : A), cjoin_sub (mul sh a) a.
Proof.
  intros.
  apply wjoin_sub_cjoin_sub.
  apply (mul_join_sub' sh a).
Qed.

(*Lemma mul_join_hom {A} {J : Join A} {S : @SSA A J} {PA : @Perm_alg A J} {SA : @Sep_alg A J}:
  forall a b c sh,
  join a b c ->
  join (mul sh a) (mul sh b) (mul sh c).
Proof.
  intros.
  destruct (mul_join_sub sh a) as [a' ?].
  destruct (mul_join_sub sh b) as [b' ?].
  apply join_comm in H0.
  destruct (join_assoc H0 H) as [xyb' [? ?]].
  apply join_comm in H1.
  apply join_comm in H2.
  destruct (join_assoc H1 H2) as [xy [? ?]].
  apply join_comm in H4.
  
*)

Class FracBoundedAlg (A : Type) {J : Join A} {ssa : @SSA A J} : Type := mkFracBoundedAlg {
  quantum: A -> share -> nat;
  quantum_sub: forall (a b : A) (pi : share), join_sub a b -> quantum a pi <= quantum b pi;
  quantum_uniform: forall a b c pi, (~identity b) -> b = force pi b -> join a b c -> quantum a pi < quantum c pi;
}.

(* Now we present a series of constuctors *)
Lemma pshare_not_nonpositive: ~non_positive pshare.
Proof.
  intro. 
  destruct H. red in H. destruct H. destruct x. simpl in *.
  rewrite Share.glb_idem in H.
  apply (n Share.bot). subst.
  split. rewrite Share.glb_bot. trivial. rewrite Share.lub_bot. trivial.
Qed.

Instance pshare_SSA : SSA pshare.
  apply (@mkSSA _ _ (fun a _ => a) (fun a b => pbow b a)); intros; auto.
  + unfold pbow. simpl. apply exist_ext. rewrite Share.rel_assoc. trivial.
  + exfalso. apply pshare_not_nonpositive; trivial. 
  + case (eq_dec a pfullshare). intro. subst. apply wjoin_sub_refl.
    intros. apply wjoin_sub_sub with (pcomp a n).
    split; simpl. rewrite Share.comp2. trivial. rewrite Share.comp1. trivial.
  + apply wjoin_sub_refl.
  + apply join_self in H. trivial.
  + unfold pbow. destruct a. simpl. apply exist_ext. apply Share.rel_top1.
  + exfalso. apply pshare_not_nonpositive; trivial.
  + destruct a1, a2. unfold pbow in H. simpl in H. inversion H.
    apply Share.rel_inj_r in H1. subst. apply exist_ext. trivial.
    intro. destruct sh. simpl in *. subst x1. apply (n1 Share.bot). 
    split. rewrite Share.glb_bot. trivial. rewrite Share.lub_bot. trivial.
  + split; intro. destruct H0. unfold pbow in *. destruct sh1, sh2, sh3, b, c. simpl in *.
    apply exist_ext. rewrite <- Share.rel_preserves_lub in H1. rewrite <- H1.
    destruct H. simpl in *. rewrite H2. trivial.
    subst c. unfold pbow. destruct sh1, sh2, sh3, b. destruct H. split; simpl in *.
    rewrite <- Share.rel_preserves_glb. rewrite H. rewrite Share.rel_bot1. trivial.
    rewrite <- Share.rel_preserves_lub. rewrite H0. trivial.
  + unfold pbow. split; intro.
    - destruct H. unfold lifted_obj in *. split; simpl.
      rewrite Share.glb_idem in H. rewrite H. rewrite Share.rel_bot2. apply Share.glb_bot.
      rewrite Share.lub_idem. trivial.
    - exfalso. unfold pbow in H. destruct H as [? _]. unfold lifted_obj in *.
      simpl in *.
      rewrite <- Share.rel_preserves_glb in H.
      rewrite Share.glb_idem in H.
      pose proof (rel_nonunit_nonunit sh' sh).
      rewrite H in H0.
      apply H0 with Share.bot.
      split. apply Share.glb_idem. apply Share.lub_idem.
  + case (eq_dec sh pfullshare); intro.
    subst sh. replace (pbow a pfullshare) with a. apply wjoin_sub_refl.
    destruct a. apply exist_ext. simpl. rewrite Share.rel_top1. trivial.
    apply wjoin_sub_sub with (pbow a (pcomp sh n)). unfold pbow. destruct sh, a. split; simpl in *.
    rewrite <- Share.rel_preserves_glb. rewrite Share.comp2. rewrite Share.rel_bot1. trivial.
    rewrite <- Share.rel_preserves_lub. rewrite Share.comp1. rewrite Share.rel_top1. trivial.
Qed.

Instance semiprod_SSA (A : Type) (B : Type) {J_A : Join A} {PA_A : @Perm_alg A J_A} {SA_A : @Sep_alg A J_A} {CA_A : @Canc_alg A J_A} {SSA_A : @SSA A J_A} : @SSA (A * B) (Join_prod A J_A B (Join_equiv B)).
Proof.
  apply (@mkSSA _ _ (fun a p => (force a (fst p), snd p)) (fun a p => (mul a (fst p), snd p))); intros; try destruct a; try destruct b; try destruct c; simpl; try f_equal.
  + apply force_force.
  + apply force_mul.
  + apply mul_force.
  + apply mul_mul.
  + apply force_identity'. destruct H. destruct x. exists a0. destruct H. apply H.
    rewrite identity_unit_equiv. rewrite identity_unit_equiv in H0. destruct H0. apply H0.
  + pose proof (force_join_sub_full' a). destruct X. left.
    right with (b0,b). split; trivial.
  + assert (wjoin_sub a a0). inversion X. left. destruct b1. subst. right with a2. destruct H. trivial.
    assert (b0 = b). inversion X. trivial. destruct b1. destruct H. destruct H2; simpl in *; congr. subst b0.
    pose proof (force_join_sub_hom' _ _ X0 sh).
    clear -X1. inversion X1; subst. left.
    right with (b0, b). split; trivial.
  + destruct H. simpl in *. apply force_join_eq in H. trivial.
  + apply mul_top.
  + apply mul_identity. rewrite identity_unit_equiv. rewrite identity_unit_equiv in H0. destruct H0. apply H0.
  + inversion H. destruct a1, a2. simpl in *. subst b0. f_equal.
    apply mul_inj in H1. trivial.
  + split ;intro.
    destruct H0. destruct H1; simpl in *. subst b0. f_equal.
    rewrite (mul_join _ _ _ H) in H0. trivial.
    inversion H0. subst b0. split. 2: split; trivial. simpl.
    rewrite (mul_join _ _ _ H). trivial.
  + split; intros [? ?]; simpl in *; split; trivial.
    rewrite (force_mul_join_hom sh sh') in H. trivial.
    simpl. rewrite (force_mul_join_hom sh sh'). trivial.
  + pose proof (mul_join_sub' sh a). inversion X.
    repeat rewrite H0. left. subst.
    right with (b0, b). split; trivial.
Defined.

Definition wjoin_sub_full_fun (A : Type) (B : Type) (f : A -> B)
  {J_B : Join B} {PA_B : @Perm_alg B J_B} {SA_B : @Sep_alg B J_B} {CA_B : @Canc_alg B J_B}
  {SSA_B : @SSA B J_B} : A -> B.
intro x.
pose proof (force_join_sub_full' (f x)).
destruct X.
exact (core (f x)).
exact b.
Defined.

Instance SSA_fun (A : Type) (B : Type) 
  {J_B : Join B} {PA_B : @Perm_alg B J_B} {SA_B : @Sep_alg B J_B} {CA_B : @Canc_alg B J_B}
  {SSA_B : @SSA B J_B} : SSA (A -> B).
  apply (mkSSA (A -> B) _ (fun sh f x => force sh (f x)) (fun sh f x => mul sh (f x))); intros; try extensionality.
  + apply force_force.
  + apply force_mul.
  + apply mul_force.
  + apply mul_mul.
  + apply force_identity'. destruct H. exists (x0 x). apply H.
    rewrite identity_unit_equiv in H0. rewrite identity_unit_equiv.
    spec H0 x. apply H0.
  + apply wjoin_sub_sub with (wjoin_sub_full_fun _ _ a).
    intro x. unfold wjoin_sub_full_fun.
    case (force_join_sub_full' (a x)); intros.
    apply join_comm. apply core_unit.
    trivial.
  + (* This one is really a pain... *)
    inversion X; subst.
    apply wjoin_sub_refl.
    assert (forall x, wjoin_sub (force sh (a x)) (force sh (b x))). {
      intro x. spec H x.
      apply force_join_sub_hom'.
      apply wjoin_sub_sub with (b0 x).
      trivial. }
    assert (forall x, {y : B | join (force sh (a x)) y (force sh (b x))}). {
      intro. spec X0 x. inversion X0.
      exists (core (force sh (a x))).
      apply join_comm. apply core_unit.
      exists b1. trivial. }
    apply wjoin_sub_sub with (fun x => proj1_sig (X1 x)).
    intro x.
    destruct X1. simpl. trivial.
  + spec H x. apply force_join_eq in H. trivial.
  + apply mul_top.
  + apply mul_identity.
    rewrite identity_unit_equiv.
    rewrite identity_unit_equiv in H0.
    spec H0 x. trivial.
  + pose proof (feq_app _ _ H x). simpl in H0.
    apply mul_inj with sh. trivial.
  + split; intros.
    extensionality x. spec H0 x.
    rewrite mul_join in H0; eauto.
    intro x. pose proof (feq_app _ _ H0 x). rewrite H1.
    rewrite mul_join; eauto.
  + split; intros ? x; spec H x.
    rewrite <- force_mul_join_hom. trivial.
    rewrite force_mul_join_hom. apply H.
  + assert (forall x, {y : B | join (mul sh (a x)) y (a x)}). {
      intro. pose proof (mul_join_sub sh (a x)).
      destruct X. exists x0. trivial. }
    apply wjoin_sub_sub with (fun x => proj1_sig (X x)).
    intro x.
    destruct X. apply j.
Defined.
