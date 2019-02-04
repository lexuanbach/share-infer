Require Import VST.msl.msl_direct.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.

Require Import neg_logic.
Require Import modal_logic.
Require Import ssl_shares.
Require Import ssl_logic.

Open Scope logic.

(* EXAMPLES: PROOF THEORY *)

Section Examples_ProofTheory.

Variable addr : Type.
Variable null : addr.
Definition value : Type := addr.

Variables heapR Pred : Type.

Variable ND : @NatDed Pred.
Variable CND : @ClassicNatDed Pred ND.
Variable SL : @SepLog Pred ND.
Variable CSL : @ClassicalSep Pred ND SL.
Variable PSL : @PreciseSepLog Pred ND SL.
Variable ML : @ModLog heapR Pred ND.
Variable MLS : @ModLogSeq heapR Pred ND ML.
Variable SSL : @ScaledSepLog Pred heapR ND SL PSL ML MLS.
Variable FIL : @FracIndLog Pred heapR ND SL PSL ML MLS SSL.
Variable CL : @CorecLog heapR Pred ND SL ML MLS.

(* Maps-to *)
Variable SML : @ScaledMapsLog Pred (addr * value) heapR ND SL PSL ML MLS SSL.
Definition maps_to a pi v := !!!(a <> null) * maps_to' pi (a,v).
Variable maps_to_eq: forall a p1 p2 v1 v2,
  (maps_to a p1 v1 * TT) && (maps_to a p2 v2 * TT) |-- !!(v1 = v2).

Lemma maps_to_nonempty: forall a pi v,
  maps_to a pi v |-- !Emp.
Proof.
  intros.
  rewrite <- (emp_sepcon (! Emp)).
  apply sepcon_derives.
  apply andp_left1. trivial.
  apply maps_to'_nonempty.
Qed.

Lemma maps_to_uniform: forall a pi v,
  maps_to a pi v |-- uniform pi.
Proof.
  intros.
  rewrite <- star_uniform.
  apply sepcon_derives.
  apply uniform_prop.
  apply maps_to'_uniform.
Qed.

Lemma maps_to_precise: forall a pi v,
  precise (maps_to a pi v).
Proof.
  intros.
  apply star_precise.
  apply prop_precise.
  apply maps_to'_precise.
Qed.

Lemma dot_maps_to: forall pi1 a pi2 v, 
  dot pi1 (maps_to a pi2 v) = maps_to a (pbow pi2 pi1) v.
Proof.
  intros.
  unfold maps_to.
  rewrite (dot_star _ _ pi2 _).
  rewrite dot_prop.
  rewrite dot_maps_to'. trivial.
  apply uniform_prop.
  apply maps_to'_uniform.
Qed.

(* Lists *)

Definition listF (rec : addr -> Pred) : addr -> Pred :=
  fun a => !!! (a = null) ||
               EX n : value, maps_to a pfullshare n * rec n.

Lemma covariant_listF : covariant listF.
Proof.
  apply covariant_orp.
  apply covariant_const.
  apply covariant_exp. intro.
  apply covariant_sepcon.
  apply covariant_const.
  apply covariant_const'.
Qed.

Definition plist : addr -> Pred := corec listF.

Lemma plist_unfold : 
  plist = fun a => !!! (a = null) ||
                   EX n : value, maps_to a pfullshare n * plist n.
Proof. unfold plist at 1. rewrite corec_fold_unfold. trivial. apply covariant_listF. Qed.

Lemma plist_uniform: forall x, 
  plist x |-- uniform pfullshare.
Proof.
  intros. rewrite <- (andp_TT (plist x)).
  rewrite andp_comm. rewrite imp_andp_adjoint.
  apply derives_trans with (ALL x : addr, plist x --> uniform pfullshare).
  2: apply allp_left with x; apply derives_refl. clear -FIL CND CSL.
  apply (shrinking_W pfullshare).
  apply allp_right. intro r.
  rewrite <- imp_andp_adjoint.
  pattern plist at 2. rewrite plist_unfold.
  rewrite andp_comm. rewrite distrib_orp_andp.
  apply orp_left.
  + apply andp_left1. apply andp_left1. apply uniform_emp.
  + rewrite imp_andp_adjoint. apply exp_left. intro n.
    rewrite <- imp_andp_adjoint.
    apply conj_shrinking_entailswithin_uniform.
    apply andp_right.
    apply maps_to_uniform. apply maps_to_nonempty.
    rewrite andp_comm.
    rewrite imp_andp_adjoint.
    eapply derives_trans. apply within_T.
    apply allp_left with n.
    apply derives_refl.
Qed.

Lemma plist_precise: forall x,
  precise (plist x).
Proof.
  intro. rewrite precise_precisely'.
  rewrite <- (TT_andp (plist x * TT)).
  rewrite imp_andp_adjoint.
  apply derives_trans with (ALL x : addr, plist x * TT --> precisely (plist x)).
  2: apply allp_left with x; trivial. clear x.
  apply (shrinking_W pfullshare).
  apply allp_right. intro x.
  eapply derives_trans.
  2: rewrite plist_unfold. 2: apply derives_refl.
  rewrite <- imp_andp_adjoint.
  apply orp_induct. (* YES! *)
  apply precise_derives_precisely.
  apply prop_precise.
  apply exp_induct. intro n. (* YES! *)
{ rewrite sepcon_assoc.
  eapply derives_trans.
  2: apply star_precisely2, maps_to_precise. (* YES! *)
  rewrite andp_comm.
  rewrite <- shrinkingR_withinR. rewrite seqR_box.
  eapply derives_trans.
  apply (conj_shrinking_star1 (maps_to x pfullshare n)). (* YES! *)
  apply andp_right. apply maps_to_uniform. apply maps_to_nonempty.
  apply sepcon_derives. apply andp_left1. apply derives_refl.
  apply andp_left2.
  eapply derives_trans; try apply within_T.
  apply allp_left with n.
  apply precisely_strengthen. }
{ intros a b. eapply derives_trans.
  2: apply (maps_to_eq x pfullshare pfullshare a b).
  apply andp_derives;
  rewrite sepcon_assoc;
  apply sepcon_derives; trivial;
  apply TT_right. }
{ rewrite imp_andp_adjoint, wand_sepcon_adjoint.
  unfold sprop. rewrite andp_comm. rewrite imp_andp_adjoint.
  apply prop_left. intro. subst x.
  rewrite <- imp_andp_adjoint. rewrite <- wand_sepcon_adjoint. rewrite <- imp_andp_adjoint.
  apply andp_left2.
  rewrite wand_sepcon_adjoint.
  apply exp_left. intro n.
  unfold maps_to.
  repeat rewrite wand_sepcon_adjoint.
  apply andp_left2. apply prop_left.
  intro. destruct H. trivial. }
Qed.

Lemma plist_mult_unfold: forall sh x,
  dot sh (plist x) = !!! (x = null) ||
                     EX n : value,
                       maps_to x sh n * 
                       dot sh (plist n).
Proof.
  intros. pattern plist at 1. rewrite plist_unfold.
  rewrite dot_orp.
  rewrite dot_prop.
  rewrite dot_exp.
  assert (pbow pfullshare sh = sh). {
      unfold pbow, pfullshare. destruct sh. apply exist_ext. simpl.
      unfold fullshare. rewrite Share.rel_top2. trivial. }
  apply pred_ext; 
  apply orp_derives; trivial; 
  apply exp_derives; intro n;
  do 3 (try rewrite (dot_star _ _ pfullshare _));
  try apply uniform_star;
  try apply uniform_star;
  try apply plist_uniform;
  try apply maps_to'_uniform;
  try apply maps_to_uniform;
  try apply uniform_prop;
  repeat rewrite dot_maps_to;
  try rewrite H; trivial.
Qed.

Lemma plist_split: forall sh1 sh2 sh x, 
  join sh1 sh2 pfullshare ->
  dot sh (plist x) = dot sh1 (dot sh (plist x)) * dot sh2 (dot sh (plist x)).
Proof.
  intros.
  pattern (dot sh (plist x)) at 1.
  rewrite <- (dot_top (dot sh (plist x))).
  pose proof (dot_precise (plist x) sh).
  destruct H0.
  rewrite (dot_plus _ (H0 (plist_precise x)) _ _ _ H).
  trivial.
Qed.

(* Trees *)
Variable S1 : addr -> addr.

Definition treeF (rec : addr -> Pred) : addr -> Pred :=
  fun a => !!! (a = null) ||
               EX l : value, EX r : value, 
               maps_to a pfullshare l * 
               maps_to (S1 a) pfullshare r *
               rec l *
               rec r.

Lemma covariant_treeF : covariant treeF.
Proof.
  apply covariant_orp.
  apply covariant_const.
  apply covariant_exp. intro.
  apply covariant_exp. intro.
  apply covariant_sepcon.
  apply covariant_sepcon.
  apply covariant_sepcon.
  apply covariant_const.
  apply covariant_const.
  apply covariant_const'.
  apply covariant_const'.
Qed.

Definition ptree : addr -> Pred := corec treeF.

Lemma ptree_unfold : 
  ptree = fun a => !!! (a = null) ||
                   EX l : value, EX r : value,
                   maps_to a pfullshare l * 
                   maps_to (S1 a) pfullshare r *
                   ptree l *
                   ptree r.
Proof.
  unfold ptree at 1. rewrite corec_fold_unfold. trivial. apply covariant_treeF.
Qed.

Lemma ptree_uniform: forall x, 
  ptree x |-- uniform pfullshare.
Proof.
  intros. rewrite <- (andp_TT (ptree x)).
  rewrite andp_comm. rewrite imp_andp_adjoint.
  apply derives_trans with (ALL x : addr, ptree x --> uniform pfullshare).
  2: apply allp_left with x; apply derives_refl. clear -FIL CND CSL.
  apply (shrinking_W pfullshare).
  apply allp_right. intro rt.
  rewrite <- imp_andp_adjoint.
  pattern ptree at 2. rewrite ptree_unfold.
  rewrite andp_comm. rewrite distrib_orp_andp.
  apply orp_left.
  + apply andp_left1. apply andp_left1. apply uniform_emp.
  + rewrite imp_andp_adjoint. apply exp_left. intro l. apply exp_left. intro r.
    rewrite <- imp_andp_adjoint.
    repeat rewrite sepcon_assoc.
    apply conj_shrinking_entailswithin_uniform.
    apply andp_right.
    apply maps_to_uniform. apply maps_to_nonempty.
    eapply derives_trans.
    apply conj_within_star.
    rewrite <- star_uniform at 1.
    apply sepcon_derives. apply andp_left1. apply maps_to_uniform.
    eapply derives_trans.
    apply conj_within_star.
    rewrite <- star_uniform at 1.
    apply sepcon_derives; rewrite andp_comm, imp_andp_adjoint; 
    eapply derives_trans; try apply within_T;
    eapply allp_left; trivial.
Qed.

Lemma ptree_precise: forall x,
  precise (ptree x).
Proof.
  intro. rewrite precise_precisely'.
  rewrite <- (TT_andp (ptree x * TT)).
  rewrite imp_andp_adjoint.
  apply derives_trans with (ALL x : addr, ptree x * TT --> precisely (ptree x)).
  2: apply allp_left with x; trivial. clear x.
  apply (shrinking_W pfullshare).
  apply allp_right. intro rt.
  eapply derives_trans.
  2: rewrite ptree_unfold. 2: apply derives_refl.
  rewrite <- imp_andp_adjoint.
  apply orp_induct. (* YES! *)
  apply precise_derives_precisely.
  apply prop_precise.
  apply exp_induct. intro l. (* YES! *)
  apply exp_induct. intro r. (* YES! *)
{ repeat rewrite sepcon_assoc.
  eapply derives_trans.
  2: apply star_precisely2, maps_to_precise. (* YES! *)
  rewrite andp_comm.
  rewrite <- shrinkingR_withinR. rewrite seqR_box.
  eapply derives_trans.
  apply (conj_shrinking_star1 (maps_to rt pfullshare l)). (* YES! *)
  apply andp_right. apply maps_to_uniform. apply maps_to_nonempty.
  apply sepcon_derives. apply andp_left1. apply derives_refl.
  apply andp_left2. apply star_precisely.
  apply precise_derives_precisely, maps_to_precise.
  apply star_precisely; eapply derives_trans; try apply within_T.
  apply allp_left with l.
  apply precisely_strengthen.
  apply allp_left with r.
  apply precisely_strengthen. }
{ intros x y. eapply derives_trans.
  2: apply (maps_to_eq (S1 rt) pfullshare pfullshare x y).
  apply andp_derives;
  rewrite (sepcon_comm (maps_to rt pfullshare l));
  repeat rewrite sepcon_assoc;
  apply sepcon_derives; trivial;
  apply TT_right. }
{ intros x y. eapply derives_trans.
  2: apply (maps_to_eq rt pfullshare pfullshare x y).
  do 2 rewrite exp_sepcon1.
  apply andp_derives; apply exp_left; intro r;
  repeat rewrite sepcon_assoc;
  apply sepcon_derives; trivial;
  apply TT_right. }
{ rewrite imp_andp_adjoint, wand_sepcon_adjoint.
  unfold sprop. rewrite andp_comm. rewrite imp_andp_adjoint.
  apply prop_left. intro. subst rt.
  rewrite <- imp_andp_adjoint. rewrite <- wand_sepcon_adjoint. rewrite <- imp_andp_adjoint.
  apply andp_left2.
  rewrite wand_sepcon_adjoint.
  apply exp_left. intro l. apply exp_left. intro r.
  unfold maps_to.
  repeat rewrite wand_sepcon_adjoint.
  apply andp_left2. apply prop_left.
  intro. destruct H. trivial. }
Qed.

Lemma ptree_mult_unfold: forall sh x,
  dot sh (ptree x) = !!! (x = null) ||
                     EX l : value, EX r : value,
                       maps_to x sh l * 
                       maps_to (S1 x) sh r *
                       dot sh (ptree l) *
                       dot sh (ptree r).
Proof.
  intros. pattern ptree at 1. rewrite ptree_unfold.
  rewrite dot_orp.
  rewrite dot_prop.
  rewrite dot_exp.
  assert (pbow pfullshare sh = sh). {
      unfold pbow, pfullshare. destruct sh. apply exist_ext. simpl.
      unfold fullshare. rewrite Share.rel_top2. trivial. }
  apply pred_ext; 
  apply orp_derives; trivial; 
  apply exp_derives; intro l;
  rewrite dot_exp;
  apply exp_derives; intro r;
  do 3 (try rewrite (dot_star _ _ pfullshare _));
  try apply uniform_star;
  try apply uniform_star;
  try apply ptree_uniform;
  try apply maps_to'_uniform;
  try apply maps_to_uniform;
  try apply uniform_prop;
  repeat rewrite dot_maps_to;
  try rewrite H; trivial.
Qed.

Lemma ptree_split: forall sh1 sh2 sh x, 
  join sh1 sh2 pfullshare ->
  dot sh (ptree x) = dot sh1 (dot sh (ptree x)) * dot sh2 (dot sh (ptree x)).
Proof.
  intros.
  pattern (dot sh (ptree x)) at 1.
  rewrite <- (dot_top (dot sh (ptree x))).
  pose proof (dot_precise (ptree x) sh).
  destruct H0.
  rewrite (dot_plus _ (H0 (ptree_precise x)) _ _ _ H).
  trivial.
Qed.

End Examples_ProofTheory.

