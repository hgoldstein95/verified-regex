Require Import DecEq.
Require Import CpdtTactics.
Require Import Arith List Ascii MSets Ensembles Equality.
Import ListNotations.

Section EnsembleLemmas.
  Context {T : Type}.
  Context {dec_eq_ : DecEq T}.

  Definition str := list T.

  Inductive SetConcat (Y Z : Ensemble str) : Ensemble str :=
  | SetConcat_intro : forall x y z,
      In str Y y ->
      In str Z z ->
      x = y ++ z ->
      In str (SetConcat Y Z) x.

  Fixpoint SetToN (X : Ensemble str) (n : nat) : Ensemble str :=
    match n with
    | 0 => Singleton str []
    | S n' => SetConcat X (SetToN X n')
    end.

  Inductive SetStar (X : Ensemble str) : Ensemble str :=
  | SetStar_intro : forall x n,
      In str (SetToN X n) x ->
      In str (SetStar X) x.

  Ltac union_crush :=
    intros ;
    apply Extensionality_Ensembles ;
    unfold Same_set ;
    unfold Included ;
    split ; intros x H ;
    repeat destruct H ; crush.

  Lemma union_com :
    forall l m, Union str l m = Union str m l.
  Proof.
    union_crush.
  Qed.

  Lemma union_empty_neut :
    forall l, Union str (Empty_set str) l = l.
  Proof.
    union_crush.
  Qed.

  Lemma union_idem :
    forall l, Union str l l = l.
  Proof.
    union_crush.
  Qed.

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
    forall l, SetConcat (Singleton str []) l = l.
  Proof.
    intros.
    apply Extensionality_Ensembles.
    unfold Same_set.
    unfold Included.
    split ; intros.
    - destruct H.
      destruct H.
      subst.
      simpl.
      auto.
    - apply SetConcat_intro with (y := []) (z := x) ; auto.
      constructor.
  Qed.

  Lemma set_concat_neut_r :
    forall l, SetConcat l (Singleton str []) = l.
  Proof.
    intros.
    apply Extensionality_Ensembles.
    unfold Same_set.
    unfold Included.
    split ; intros.
    - destruct H.
      destruct H0.
      subst.
      rewrite app_nil_r.
      auto.
    - apply SetConcat_intro with (y := x) (z := []) ; auto.
      + constructor.
      + rewrite app_nil_r.
        auto.
  Qed.

  Lemma set_concat_zero_l :
    forall l, SetConcat (Empty_set str) l = Empty_set str.
  Proof.
    intros.
    apply Extensionality_Ensembles.
    unfold Same_set.
    unfold Included.
    split ; intros.
    - destruct H.
      subst.
      contradict H.
    - contradict H.
  Qed.

  Lemma set_concat_zero_r :
    forall l, SetConcat l (Empty_set str) = Empty_set str.
  Proof.
    intros.
    apply Extensionality_Ensembles.
    unfold Same_set.
    unfold Included.
    split ; intros.
    - destruct H.
      subst.
      contradict H0.
    - contradict H.
  Qed.

  Lemma star_empty_eq_sing :
    SetStar (Empty_set str) = Singleton str [].
  Proof.
    intros.
    apply Extensionality_Ensembles.
    unfold Same_set.
    unfold Included.
    split ; intros.
    - inversion H. subst.
      induction n.
      + simpl in *. auto.
      + simpl in *. rewrite set_concat_zero_l in H0.
        contradict H0.
    - apply SetStar_intro with (n := 0).
      simpl.
      auto.
  Qed.
End EnsembleLemmas.