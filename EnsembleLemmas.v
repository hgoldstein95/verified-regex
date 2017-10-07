Require Import Str CpdtTactics.
Require Import Arith List Ascii MSets Ensembles Equality.
Import ListNotations.

Inductive SetConcat (Y Z : Ensemble Str.t) : Ensemble Str.t :=
| SetConcat_intro : forall x y z,
    In Str.t Y y ->
    In Str.t Z z ->
    x = y ++ z ->
    In Str.t (SetConcat Y Z) x.

Fixpoint SetToN (X : Ensemble Str.t) (n : nat) : Ensemble Str.t :=
  match n with
  | 0 => Singleton Str.t []
  | S n' => SetConcat X (SetToN X n')
  end.

Inductive SetStar (X : Ensemble Str.t) : Ensemble Str.t :=
| SetStar_intro : forall x n,
    In Str.t (SetToN X n) x ->
    In Str.t (SetStar X) x.

Ltac union_crush :=
  intros ;
  apply Extensionality_Ensembles ;
  unfold Same_set ;
  unfold Included ;
  split ; intros x H ;
  repeat destruct H ; crush.

Lemma set_concat_assoc :
  forall a b c, SetConcat a (SetConcat b c) = SetConcat (SetConcat a b) c.
Proof.
  Ltac dest_set_concat :=
    repeat
      match goal with
      | [ H : In _ (SetConcat _ _) _ |- _ ] => destruct H ; subst
      end.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set.
  unfold Included.
  split ;
    intros ;
    dest_set_concat ;
    [ rewrite app_assoc | rewrite <- app_assoc ] ;
    eapply SetConcat_intro ; eauto ;
    eapply SetConcat_intro ; eauto.
Qed.

Lemma set_concat_neut_l :
  forall l, SetConcat (SetStar (Empty_set Str.t)) l = l.
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set.
  unfold Included.
  split ; intros.
  - destruct H.
    destruct H.
    subst.
    induction n ; destruct H ; simpl ; auto.
    contradict H.
  - eapply SetConcat_intro ; eauto.
    + eexists 0. simpl. constructor.
    + auto.
Qed.

Lemma set_concat_neut_r :
  forall l, SetConcat l (SetStar (Empty_set Str.t)) = l.
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set.
  unfold Included.
  split ; intros.
  - destruct H.
    destruct H0.
    subst.
    induction n ; destruct H0 ; simpl ; try rewrite app_nil_r ; auto.
    contradict H0.
  - eapply SetConcat_intro ; eauto.
    + eexists 0. simpl. constructor.
    + rewrite app_nil_r. auto.
Qed.
