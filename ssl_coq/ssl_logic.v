Require Import VST.msl.msl_direct.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.

Require Import neg_logic.
Require Import modal_logic.
Require Import ssl_shares.

Definition Emp {A} {ND : NatDed A} {SL : @SepLog A ND} := @VST.msl.seplog.emp A ND SL.

Open Local Scope logic.

Definition sprop {A} `{SL : SepLog A} (P : Prop) : A :=
  Emp && !!P.
Notation "'!!!' e" := (sprop e) (at level 25) : logic.

Lemma sprop_FF {A} `{SL : SepLog A}:
  !!! False = FF.
Proof.
  apply pred_ext.
  apply andp_left2.
  apply prop_left.
  contradiction.
  apply FF_left.
Qed.

(* LOGIC AXIOMS *)

Class PreciseSepLog (A : Type) {ND : NatDed A} {SL : @SepLog A ND} : Type := mkPreciseSepLog {
  precise : A -> Prop;
  precisely : A -> A;

  precisely_derives: forall P Q R,
    precisely P |-- (P * Q) && (P * R) --> P * (Q && R);
  derives_precisely: forall G P,
    (forall Q R, G |-- (P * Q) && (P * R) --> P * (Q && R)) ->
    G |-- precisely P;
  precise_precisely: forall P,
    precise P <-> TT |-- precisely P;

(*
  FF_precisely : forall G,
    G |-- precisely FF;
*)
(* On pen-and-paper these are probably axioms, but in the Coq development
   we can prove them from the rules for allp and exp.
  andp_precisely1 : forall G P Q,
    G |-- precisely P ->
    G |-- precisely (P && Q);
  orp_precisely1: forall G P Q,
    G |-- precisely P ->
    G |-- precisely Q ->
    (P * TT) && (Q * TT) |-- FF ->
    G |-- precisely (P || Q); *)
  allp_precisely : forall G T P,
    (exists x : T, G |-- precisely (P x)) ->
    G |-- precisely (ALL x : T, P x);
  exp_precisely : forall G T P,
    (forall x : T, G |-- precisely (P x)) ->
    (forall x y : T, G && (P x * TT) && (P y * TT) |-- !!(x = y)) ->
    G |--  precisely (EX x : T, (P x));
(*
  emp_precisely : forall G,
    G |-- precisely Emp;
*)
  star_precisely : forall G P Q,
    G |-- precisely P ->
    G |-- precisely Q -> 
    G |-- precisely (P * Q);
}.

Class ScaledSepLog (A RT : Type)
  {ND : NatDed A} {SL : @SepLog A ND} {PSL : @PreciseSepLog A ND SL}
  {ML : @ModLog RT A ND} {MLS : @ModLogSeq RT A ND ML} : Type := mkSSL {
  uniform : pshare -> A;
  factorR : pshare -> RT;
  dot : pshare -> A -> A := fun sh => diamond (factorR sh);

(* not true since Emp |-- uniform pi...
  uniform_inj: forall pi1 pi2, (uniform pi1 |-- uniform pi2) -> pi1 = pi2; *)
  uniform_emp: forall pi, Emp |-- (uniform pi);
  (* Right to left is easy, given uniform_emp.  Left to right
     requires disjointness. IFF? *)
  star_uniform: forall pi,
    (uniform pi) * (uniform pi) = uniform pi; 
  uniform_dot: forall pi pi' P,
        (P      |-- uniform pi)    <->
    (dot pi' P  |-- uniform (pbow pi pi'));

  factorR_CD : forall sh, Modal_CD (factorR sh);

  factorR1_T : Modal_T (factorR pfullshare);

  factorR_seqR : forall sh1 sh2, seqR (factorR sh1) (factorR sh2) = factorR (pbow sh2 sh1);

  dot_precise: forall P sh,
    precise P <-> precise (dot sh P);

  dot_prop: forall sh (P : Prop),
    dot sh (!!! P) = !!!P; (* We use the stronger version of !!! here *)

  dot_plus1 : forall P sh1 sh2 sh3, join sh1 sh2 sh3 ->
                dot sh3 P |-- (dot sh1 P) * (dot sh2 P);
  dot_plus2 : forall P, precise P -> forall sh1 sh2 sh3, join sh1 sh2 sh3 ->
                (dot sh1 P) * (dot sh2 P) |-- dot sh3 P;

  dot_star : forall P Q pi pi',
    P |-- uniform pi -> 
    Q |-- uniform pi ->
      dot pi' (P * Q) = (dot pi' P) * (dot pi' Q);
(* wand? ewand? *)
}.

Existing Instance factorR_CD.
Existing Instance factorR1_T.

Class ScaledMapsLog (A B RT : Type) 
  {ND : NatDed A} {SL : @SepLog A ND} {PSL : @PreciseSepLog A ND SL}
  {ML : @ModLog RT A ND} {MLS : @ModLogSeq RT A ND ML} 
  {SSL : @ScaledSepLog A RT ND SL PSL ML MLS} : Type := mkScaledMapsLog {

  maps_to' : pshare -> B -> A;
  maps_to'_nonempty : forall pi b,
    maps_to' pi b |-- !Emp;
  maps_to'_uniform : forall pi b,
    maps_to' pi b |-- uniform pi;
  maps_to'_precise : forall pi b,
    precise (maps_to' pi b);
  dot_maps_to' : forall pi1 pi2 b, dot pi1 (maps_to' pi2 b) = maps_to' (pbow pi2 pi1) b;
}.

Class FracIndLog (A RT : Type) {ND : NatDed A} {SL : @SepLog A ND} 
  {PSL: @PreciseSepLog A ND SL} {ML : @ModLog RT A ND} {MLS : @ModLogSeq RT A ND ML} 
  {SSL : @ScaledSepLog A RT ND SL PSL ML MLS} : Type := mkFracIndLog {

  withinR : RT;
  shrinkingR : pshare -> RT;

  within := [withinR];
  within_T : Modal_T withinR;
  within_4 : Modal_4 withinR;

  shrinking (pi : pshare) := [shrinkingR pi];
  shrinking_4 : forall pi, Modal_4 (shrinkingR pi); (* Supposedly this may follow from W *)
  shrinking_W : forall pi, Modal_W (shrinkingR pi);

  shrinkingR_withinR : forall pi, seqR (shrinkingR pi) withinR = shrinkingR pi;
  withinR_shrinkingR : forall pi, seqR withinR (shrinkingR pi) = shrinkingR pi;

  conj_within_star: forall P Q R,
    (P * Q) && (within R) |-- (P && within R) * (Q && within R);

  conj_shrinking_star1: forall P Q R sh,
    P |-- (uniform sh && !Emp)%logic ->
    (P * Q) && (shrinking sh R) |-- (P && shrinking sh R) * (Q && R)
}.

Existing Instance within_T.
Existing Instance within_4.
Existing Instance shrinking_W.
Existing Instance shrinking_4.

Definition covariant {A} {ND : NatDed A} {B} (F : (B -> A) -> (B -> A)) : Prop :=
  forall P Q, P |-- Q -> F P |-- F Q.

Class CorecLog (RT A : Type) {ND : NatDed A} {SL : @SepLog A ND} 
  {ML : @ModLog RT A ND} {MLS : @ModLogSeq RT A ND ML} : Type := mkCorecLog {

  corec {B} : ((B -> A) -> (B -> A)) -> (B -> A);
  corec_fold_unfold {B}: forall F : ((B -> A) -> (B -> A)),
    covariant F ->
    corec F = F (corec F);
}.

(* PROOF THEORY *)

Section PSL_ProofTheory.

Context {A RT : Type}.
Context {ND : NatDed A}.
Context {CND : @ClassicNatDed A ND}.
Context {SL : @SepLog A ND}.
Context {CS : @ClassicalSep A ND SL}.
Context {PSL : @PreciseSepLog A ND SL}.

Lemma sepcon_andp_distrib: forall P Q R,
  (P * (Q && R)) |-- (P * Q) && (P * R).
Proof.
  intros. apply andp_right; apply sepcon_derives; auto.
  apply andp_left1. trivial.
  apply andp_left2. trivial.
Qed.

Lemma precise_distrib: forall P, precise P <-> (forall Q R, 
  (P * Q) && (P * R) |-- (P * (Q && R))).
Proof.
  split; intros.
  + rewrite precise_precisely in H.
    rewrite <- (TT_andp (P * Q && _)).
    eapply derives_trans. apply andp_derives. eapply derives_trans. apply H. apply precisely_derives.
    apply derives_refl.
    rewrite andp_comm.
    apply modus_ponens.
  + rewrite precise_precisely.
    apply derives_precisely. intros R S.
    rewrite <- imp_andp_adjoint.
    rewrite TT_andp.
    apply H.
Qed.

Lemma precisely_strengthen: forall P,
    P * TT --> precisely P |-- precisely P.
Proof.
  intros.
  apply derives_precisely. intros R S.
  rewrite <- imp_andp_adjoint.
  rewrite <- (andp_dup ((P * R) && (P * S))).
  rewrite <- (andp_assoc _ ((P * R) && (P * S)) ((P * R) && (P * S))).
  rewrite imp_andp_adjoint.
  rewrite andp_comm.
  eapply derives_trans. 
  apply andp_derives. apply andp_left1. apply sepcon_derives. apply derives_refl. apply TT_right.
  apply derives_refl.
  eapply derives_trans. apply modus_ponens.
  apply precisely_derives.
Qed.

Lemma FF_precisely : forall G,
  G |-- precisely FF.
Proof.
  intros. apply derives_precisely. intros.
  rewrite <- imp_andp_adjoint.
  apply andp_left2. apply andp_left2.
  rewrite wand_sepcon_adjoint.
  apply FF_left.
Qed.

Lemma emp_precisely : forall G,
  G |-- precisely Emp.
Proof.
  intro. apply derives_precisely. intros R S.
  repeat (rewrite sepcon_comm, sepcon_emp).
  rewrite <- imp_andp_adjoint.
  apply andp_left2. apply derives_refl.
Qed.

(*
Lemma andp_precisely1: forall G P Q,
  G |-- precisely P ->
  G |-- precisely (P && Q).
Proof.
  intros.
  apply derives_precisely. intros R S.
  eapply derives_trans. eapply derives_trans. apply H.
  apply (precisely_derives P R S).
  rewrite <- imp_andp_adjoint.
  rewrite <- (andp_dup (P && Q * R && (P && Q * S))).
  rewrite <- (andp_assoc (P * R && (P * S) --> P * (R && S)) _ _).
  rewrite imp_andp_adjoint.
  eapply derives_trans.
  apply andp_derives. apply derives_refl.
  apply andp_derives; apply sepcon_derives.
  apply andp_left1. apply derives_refl. apply derives_refl.
  apply andp_left1. apply derives_refl. apply derives_refl.
  rewrite andp_comm.
  eapply derives_trans. apply modus_ponens.
  rewrite <- imp_andp_adjoint.

Check modus_ponens.
a
  rewrite andp_comm.


Lemma allp_precisely' : forall G T P,
  (exists x : T, G |-- precisely (P x)) ->
  G |-- precisely (ALL x : T, P x).
Proof.
  intros.
  apply derives_precisely. intros R S.
  destruct H.
  eapply derives_trans. apply H.
  rewrite <- imp_andp_adjoint.
  rewrite andp_comm.

apply derives_trans with (ALL x : T, (P x * (R && S))).
2: apply allp_left.
SearchAbout allp.


Check exp_sepcon1.
Check allp_sepcon.

rewrite sepcon_allp.
  apply  
  rewrite imp_andp_adjoint.
  eapply derives_trans. apply andp_derives; apply sepcon_derives.
  apply allp_left with x. apply derives_refl. apply derives_refl.
  apply allp_left with x. apply derives_refl. apply derives_refl.

  eapply derives_trans. apply precisely_derives.

  precisely_derives: forall P Q R,
    precisely P |-- (P * Q) && (P * R) --> P * (Q && R);
  derives_precisely: forall G P,
    (forall Q R, G |-- (P * Q) && (P * R) --> P * (Q && R)) ->
    G |-- precisely P;
  precise_precisely: forall P,
    precise P <-> TT |-- precisely P;
*)

Lemma precise_eq:
  precise = fun P => forall Q R, (P * (Q && R)) = (P * Q) && (P * R).
Proof.
  extensionality P. apply prop_ext. split; intros.
  apply pred_ext. apply sepcon_andp_distrib.
  apply precise_distrib. apply H.
  rewrite precise_distrib. intros.
  rewrite <- H. apply derives_refl.
Qed.

Lemma precisely_weaken: forall P,
  precisely P |-- P * TT --> precisely P.
Proof.
  intro. rewrite <- imp_andp_adjoint.
  apply andp_left1. apply derives_refl.
Qed.

Lemma precisely_equiv: forall P,
  precisely P = P * TT --> precisely P.
Proof. intro. apply pred_ext. apply precisely_weaken. apply precisely_strengthen. Qed.

Lemma precise_precisely': forall P,
  precise P <-> P * TT |-- precisely P.
Proof.
  split; intros.
  eapply derives_trans. apply TT_right.
  rewrite <- precise_precisely. trivial.
  rewrite precise_precisely. rewrite precisely_equiv.
  rewrite <- imp_andp_adjoint.
  apply andp_left2. trivial.
Qed.

Lemma andp_precisely1: forall G P Q,
  G |-- precisely P ->
  G |-- precisely (P && Q).
Proof.
  intros. rewrite andp_is_allp.
  apply allp_precisely.
  exists true. trivial.
Qed.

Lemma orp_precisely1: forall G P Q,
  G |-- precisely P ->
  G |-- precisely Q ->
  G && (P * TT) && (Q * TT) |-- FF ->
  G |-- precisely (P || Q).
Proof.
  intros. rewrite orp_is_exp.
  apply exp_precisely; intros.
  destruct x; trivial.
  destruct x, y; try (apply prop_right; trivial; fail); apply FF_right; auto.
  rewrite andp_assoc. rewrite (andp_comm (Q * TT)). rewrite <- andp_assoc. trivial.
Qed.

Lemma orp_precisely2: forall R S P Q,
  R |-- precisely P ->
  S |-- precisely Q ->
  (R * TT) && (Q * TT) |-- FF ->
  (S * TT) && (P * TT) |-- FF ->
  R || S |-- precisely (P || Q).
Proof.
  intros.
  apply orp_left; apply orp_precisely1; auto.
  + rewrite precisely_equiv. rewrite <- imp_andp_adjoint.
    apply FF_right.
    eapply derives_trans. 2: apply H1.
    apply andp_derives.
    apply sepcon_TT.
    apply derives_refl.
  + rewrite andp_comm. rewrite <- andp_assoc.
    apply andp_left1.
    eapply derives_trans. 2: apply H1.
    rewrite andp_comm.
    apply andp_derives.
    apply sepcon_TT.
    apply derives_refl.
  + rewrite precisely_equiv. rewrite <- imp_andp_adjoint.
    apply FF_right.
    eapply derives_trans. 2: apply H2.
    apply andp_derives.
    apply sepcon_TT.
    apply derives_refl.
  + apply andp_left1.
    eapply derives_trans. 2: apply H2.
    apply andp_derives.
    apply sepcon_TT.
    apply derives_refl.
Qed.

Lemma exp_precisely2 : forall T G P,
    (forall x : T, G x |-- precisely (P x)) ->
    (forall x y, G x && (P y * TT) |-- !!(x = y)) ->
    EX x : T, G x |--  precisely (EX x : T, (P x)).
Proof.
  intros.
  apply exp_left. intro x.
  apply exp_precisely.
  intro.
  spec H0 x x0.
  rewrite <- (andp_dup (G x)).
  rewrite precisely_equiv. rewrite <- imp_andp_adjoint.
  rewrite andp_assoc.
  eapply derives_trans.
  apply andp_derives. apply derives_refl. apply H0.
  rewrite andp_comm.
  rewrite imp_andp_adjoint.
  apply prop_left. intro. subst x0.
  rewrite <- imp_andp_adjoint. apply andp_left2.
  apply H.
  intros a b.
  rewrite imp_andp_adjoint.
  rewrite <- (andp_dup (G x)).
  rewrite andp_assoc.
  rewrite andp_comm.
  rewrite imp_andp_adjoint.
  eapply derives_trans. apply H0.
  apply prop_left. intro. subst x.
  rewrite <- imp_andp_adjoint. apply andp_left2.
  rewrite <- imp_andp_adjoint. apply H0.
Qed.

Lemma exp_induct: forall T (Q : A) (P : T -> A),
  (forall x : T, Q && (P x * TT) |-- precisely (P x)) ->
  (forall x y, (P x * TT) && (P y * TT) |-- !!(x = y)) -> 
  Q && ((EX x : T, P x) * TT) |-- precisely (EX x : T, P x).
Proof.
  intros.
  rewrite exp_sepcon1.
  rewrite exp_andp2.
  apply exp_precisely2; trivial.
  intros.
  spec H0 x y.
  eapply derives_trans. 2: apply H0.
  apply andp_derives. 2: apply derives_refl.
  apply andp_left2.
  apply derives_refl.
Qed.

Lemma orp_induct: forall Q R S,
  Q && (R * TT) |-- precisely R ->
  Q && (S * TT) |-- precisely S ->
  (R * TT) && (S * TT) |-- FF ->
  Q && ((R || S) * TT) |-- precisely (R || S).
Proof.
  intros. rewrite orp_is_exp.
  apply exp_induct.
  intro x. destruct x; trivial.
  intros x y. destruct x,y.
  apply prop_right; trivial.
  apply FF_right. trivial.
  apply FF_right. rewrite andp_comm. trivial.
  apply prop_right; trivial.
Qed.

Lemma TT_derives_precisely: forall P,
  TT |-- precisely P ->
  precise P.
Proof.
  intros.
  rewrite precise_precisely.
  eapply derives_trans.
  apply TT_right. trivial.
Qed.

Lemma FF_precise:
  precise FF.
Proof.
  rewrite precise_precisely'.
  rewrite wand_sepcon_adjoint.
  apply FF_left.
Qed.

Lemma andp_precise1: forall P Q,
  precise P ->
  precise (P && Q).
Proof.
  do 2 intro.
  do 2 rewrite precise_precisely'.
  intro.
  rewrite wand_sepcon_adjoint.
  apply andp_left1.
  rewrite <- wand_sepcon_adjoint.
  apply andp_precisely1. trivial.
Qed.

Lemma andp_precisely2: forall G P Q,
  G |-- precisely Q ->
  G |-- precisely (P && Q).
Proof.
  do 3 intro. rewrite andp_comm.
  apply andp_precisely1.
Qed.

Lemma andp_precise2: forall P Q,
  precise Q ->
  precise (P && Q).
Proof.
  do 2 intro. rewrite andp_comm.
  apply andp_precise1.
Qed.

Lemma orp_precise: forall P Q,
  precise P ->
  precise Q ->
  (P * TT) && (Q * TT) |-- FF ->
  precise (P || Q).
Proof.
  do 2 intro. do 3 rewrite precise_precisely'.
  intros.
  rewrite <- (TT_andp (_ * TT)).
  apply orp_induct.
  apply andp_left2. trivial.
  apply andp_left2. trivial.
  trivial.
Qed.

Lemma emp_precise:
  precise Emp.
Proof.
  rewrite precise_precisely'. apply emp_precisely.
Qed.

Lemma prop_precise: forall P,
  precise (!!! P).
Proof.
  intro. apply andp_precise1. apply emp_precise.
Qed.

Lemma star_precise: forall P Q,
  precise P ->
  precise Q ->
  precise (P * Q).
Proof.
  do 2 intro. do 3 rewrite precise_precisely'.
  intros. apply star_precisely.
  apply derives_trans with (P * TT); trivial.
  rewrite sepcon_assoc. apply sepcon_derives. apply derives_refl. apply TT_right.
  apply derives_trans with (Q * TT); trivial.
  rewrite (sepcon_comm P), sepcon_assoc. apply sepcon_derives. apply derives_refl. apply TT_right.
Qed.

Lemma precise_derives_precisely: forall P Q,
  precise P -> Q |-- precisely P.
Proof.
  intros. eapply derives_trans.
  apply TT_right.
  rewrite precise_precisely in H. trivial.
Qed.

Lemma star_precisely2 : forall P Q,
  precise P ->
  P * (precisely Q) |-- precisely (P * Q).
Proof.
  intros.
  apply derives_precisely. intros R S.
  rewrite <- imp_andp_adjoint.
  rewrite precise_eq in H.
  pose proof (H (Q * R) (Q * S)).
  do 2 rewrite <- sepcon_assoc in H0. rewrite <- H0. clear H0.
  spec H (precisely Q) (Q * R && (Q * S)).
  rewrite <- H. clear H.
  rewrite sepcon_assoc.
  apply sepcon_derives. trivial.
  rewrite imp_andp_adjoint.
  apply precisely_derives.
Qed.

End PSL_ProofTheory.

Section SSL_ProofTheory.

Context {A RT : Type}.
Context {ND : NatDed A}.
Context {CND : @ClassicNatDed A ND}.
Context {SL : @SepLog A ND}.
Context {PSL : @PreciseSepLog A ND SL}.
Context {ML : @ModLog RT A ND}.
Context {MLS : @ModLogSeq RT A ND ML}.
Context {SSL : @ScaledSepLog A RT ND SL PSL ML MLS}.

Lemma dot_FF: forall sh,
  dot sh FF = FF.
Proof. intro. apply diamond_FF. Qed.

Lemma dot_positive: forall sh P Q,
  P |-- Q ->
  dot sh P |-- dot sh Q.
Proof. intros. apply diamond_positive. trivial. Qed.

Lemma dot_andp: forall sh (P Q : A),
  dot sh (P && Q) = dot sh P && dot sh Q.
Proof. intros. apply diamond_andp. Qed.

Lemma dot_orp: forall sh (P Q : A),
  dot sh (P || Q) = dot sh P || dot sh Q.
Proof. intros. apply diamond_orp. Qed.

Lemma dot_allp1 {C}: forall sh (P : C -> A),
  dot sh (ALL c : C, P c) |-- ALL c : C, dot sh (P c).
Proof. intros. apply diamond_allp1. Qed.

Lemma dot_allp {C}: forall sh (P : C -> A), inhabited C ->
  dot sh (ALL c : C, P c) = ALL c : C, dot sh (P c).
Proof. intros. apply diamond_allp. trivial. Qed.

Lemma dot_exp {C}: forall sh (P : C -> A),
  dot sh (EX c : C, P c) = EX c : C, dot sh (P c).
Proof. intros. apply diamond_exp. Qed.

Definition factor (sh : pshare) : A := dot sh TT.
Lemma dot_WN: forall sh P, 
  TT |-- P -> factor sh |-- dot sh P.
Proof. intros. apply diamond_WN. trivial. Qed.

Lemma dot_K: forall sh (P Q : A),
  dot sh (P --> Q) |-- dot sh P --> dot sh Q.
Proof. intros. apply diamond_K. Qed.

Lemma dot_notp: forall sh (P : A),
  dot sh (!P) |-- ! (dot sh P).
Proof. intros. apply diamond_notp1. Qed.

Lemma dot_top: forall P,
  dot pfullshare P = P.
Proof. intro. apply diamond_T_eq. Qed.

Lemma dot_emp: forall sh,
  dot sh Emp = Emp.
Proof. intros. rewrite <- (andp_TT Emp). apply dot_prop. Qed.

Lemma dot_dot : forall sh1 sh2 P, 
  dot sh1 (dot sh2 P) = dot (pbow sh2 sh1) P.
Proof. intros. etransitivity. symmetry. apply seqR_diamond. rewrite factorR_seqR. trivial. Qed.

Lemma dot_plus: forall P, precise P -> forall sh1 sh2 sh3, join sh1 sh2 sh3 ->
                dot sh3 P = (dot sh1 P) * (dot sh2 P).
Proof. intros. apply pred_ext. apply dot_plus1; trivial. apply dot_plus2; trivial. Qed.

Lemma uniform_prop: forall pi P,
  !!! P |-- (uniform pi).
Proof.
  intros.
  apply andp_left1.
  apply uniform_emp.
Qed.

Lemma uniform_star: forall pi P Q, 
      P    |-- uniform pi ->
      Q    |-- uniform pi ->
    P * Q  |-- uniform pi. (* note, we only have one way here *)
Proof.
  intros. rewrite <- star_uniform.
  apply sepcon_derives; trivial.
Qed.

End SSL_ProofTheory.

Section FIL_ProofTheory.

Context {A RT : Type}.
Context {ND : NatDed A}.
Context {CND : @ClassicNatDed A ND}.
Context {SL : @SepLog A ND}.
Context {CSL : @ClassicalSep A ND SL}.
Context {PSL : @PreciseSepLog A ND SL}.
Context {ML : @ModLog RT A ND}.
Context {MLS : @ModLogSeq RT A ND ML}.
Context {SSL : @ScaledSepLog A RT ND SL PSL ML MLS}.
Context {FIL : @FracIndLog A RT ND SL PSL ML MLS SSL}.

Lemma shrinking_within: forall P sh,
  shrinking sh (within P) = shrinking sh P.
Proof.
  intros.
  unfold shrinking, within.
  rewrite <- seqR_box.
  rewrite shrinkingR_withinR. trivial.
Qed.

Lemma within_shrinking: forall P sh,
  within (shrinking sh P) = shrinking sh P.
Proof.
  intros.
  unfold shrinking, within.
  rewrite <- seqR_box.
  rewrite withinR_shrinkingR. trivial.
Qed.

Lemma within_star: forall P,
  within P |-- (within P) * (within P).
Proof.
  intros.
  rewrite <- (TT_andp (within P)) at 1.
  rewrite <- TT_sepcon_TT.
  eapply derives_trans.
  apply conj_within_star.
  apply sepcon_derives; apply andp_left2; trivial.
Qed.

Lemma shrinking_star: forall sh P,
  shrinking sh P |-- (shrinking sh P) * (shrinking sh P).
Proof.
  intros.
  rewrite <- within_shrinking.
  apply within_star.
Qed.

Lemma conj_shrinking_star2:forall P Q R sh,
  Q |-- uniform sh && !Emp ->
  (P * Q) && (shrinking sh R) |-- (P && R) * (Q && shrinking sh R).
Proof.
  intros.
  rewrite sepcon_comm. rewrite (sepcon_comm (P && R)).
  apply conj_shrinking_star1. trivial.
Qed.

Lemma conj_shrinking_entailswithin: forall P Q R S T sh,
  P |-- uniform sh && !Emp ->
  P && shrinking sh R |-- S ->
  Q && within R |-- T ->
  (P * Q) && shrinking sh R |-- S * T.
Proof.
  intros.
  rewrite <- shrinking_within.
  eapply derives_trans.
  apply conj_shrinking_star1. trivial.
  apply sepcon_derives; trivial.
  rewrite shrinking_within. trivial.
Qed.

Lemma conj_shrinking_entailswithin_uniform: forall P Q R sh,
  P |-- uniform sh && !Emp ->
  Q && within R |-- uniform sh ->
  (P * Q) && shrinking sh R |-- uniform sh.
Proof.
  intros.
  rewrite <- star_uniform.
  apply conj_shrinking_entailswithin; trivial.
  apply andp_left1. eapply derives_trans. apply H. apply andp_left1. trivial.
Qed.

End FIL_ProofTheory.

Section CSL_ProofTheory.

Context {A : Type}.
Context {ND : NatDed A}.
Context {CND : @ClassicNatDed A ND}.
Context {SL : @SepLog A ND}.

Lemma covariant_orp {B} : forall (P Q : (B -> A) -> (B -> A)),
  covariant P ->
  covariant Q ->
  covariant (fun F b => P F b || Q F b).
Proof.
  unfold covariant. intros.
  simpl. intro b.
  apply orp_left.
  apply orp_right1, H; trivial.
  apply orp_right2, H0; trivial.
Qed.

Lemma covariant_const {B} : forall P : (B -> A),
  covariant (fun _ b => P b).
Proof.
  unfold covariant. intros.
  simpl. intro b.
  apply derives_refl.
Qed.

Lemma covariant_exp {B} {C} : forall F : C -> (B -> A) -> (B -> A),
  (forall c, covariant (F c)) ->
  covariant (fun P b => EX c : C, F c P b).
Proof.
  repeat intro.
  apply exp_left. intro c.
  apply exp_right with c.
  apply H.
  apply H0.
Qed.

Lemma covariant_sepcon {B} : forall P Q : (B -> A) -> (B -> A),
  covariant P ->
  covariant Q ->
  covariant (fun F b => P F b * Q F b).
Proof.
  repeat intro.
  apply sepcon_derives.
  apply H. trivial.
  apply H0. trivial.
Qed.

Lemma covariant_const' {B} : forall b : B,
  covariant (fun P _ => P b).
Proof.
  repeat intro.
  apply H.
Qed.

End CSL_ProofTheory.

