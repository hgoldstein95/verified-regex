Require Import DecEq.
Require Import CpdtTactics.
Require Import List Equality NPeano Arith Bool MSets.
Require Import FunctionalExtensionality.
Import ListNotations.

Section Regex.
  Context {T : Type}.
  Context {dec_eq_ : DecEq T}.

  Definition str := list T.

  (** Definitions *)
  Inductive re : Type :=
  | Void : re
  | Ept : re
  | Char : T -> re
  | Alt : re -> re -> re
  | Cat : re -> re -> re
  | Star : re -> re.

  Definition syn_eq_re (r1 r2 : re) : {r1 = r2} + {r1 <> r2}.
    decide equality.
    apply dec_eq_.
  Defined.

  Reserved Notation "[[ r ]]" (at level 0).
  Inductive in_re : re -> str -> Prop :=
  | In_Ept : [[ Ept ]] []
  | In_Char : forall c, [[ Char c ]] [c]
  | In_Alt_left : forall r1 r2 s, [[ r1 ]] s -> [[ Alt r1 r2 ]] s
  | In_Alt_right : forall r1 r2 s, [[ r2 ]] s -> [[ Alt r1 r2 ]] s
  | In_Cat : forall r1 r2 s1 s2, [[ r1 ]] s1 -> [[ r2 ]] s2 -> [[ Cat r1 r2 ]] (s1 ++ s2)
  | In_Star_empty : forall r, [[ Star r ]] []
  | In_Star_cat : forall r s1 s2, [[ r ]] s1 -> [[ Star r ]] s2 -> [[ Star r ]] (s1 ++ s2)
  where "[[ r ]]" := (in_re r).

  Hint Constructors in_re.

  Definition reg_eq r1 r2 := forall s, [[ r1 ]] s <-> [[ r2 ]] s.
  Infix "[=]" := reg_eq (right associativity, at level 85).

  Ltac invert H := inversion H ; subst ; clear H.
  Ltac dest_eq := unfold reg_eq ; intros ; split ; intros.
  Ltac in_inv :=
    match goal with
    | [ H : in_re (Char _) _ |- _ ] => inversion H ; clear H ; subst
    | [ H : in_re Ept _ |- _] => inversion H ; clear H
    | [ H : in_re Void _ |- _] => inversion H
    | [ H : in_re (Cat _ _) _ |- _] => inversion H ; clear H
    | [ H : in_re (Alt _ _) _ |- _] => inversion H ; clear H
    end ; subst.

  Ltac crush_re :=
    match goal with
    | [ H : in_re ?r ?s |- in_re (Alt ?r _) ?s ] => apply In_Alt_left ; auto
    | [ H : in_re ?r ?s |- in_re (Alt _ ?r) ?s ] => apply In_Alt_right ; auto
    end.

  (** Properties of Equality *)
  Lemma reg_eq_refl : forall r, r [=] r.
  Proof.
    dest_eq ; auto.
  Qed.

  Lemma reg_eq_sym : forall r1 r2, r1 [=] r2 -> r2 [=] r1.
  Proof.
    dest_eq ; apply H ; auto.
  Qed.

  Lemma reg_eq_trans : forall r1 r2 r3, r1 [=] r2 -> r2 [=] r3 -> r1 [=] r3.
  Proof.
    dest_eq.
    - apply H0 ; apply H ; auto.
    - apply H ; apply H0 ; auto.
  Qed.

  Add Parametric Relation : re reg_eq
      reflexivity proved by reg_eq_refl
      symmetry proved by reg_eq_sym
      transitivity proved by reg_eq_trans
        as reg_eq_relation.

  Add Parametric Morphism : Alt with signature
      reg_eq ++> reg_eq ++> reg_eq as Alt_reg_eq_mor.
  Proof.
    dest_eq ; in_inv.
    - apply H in H5.
      crush_re.
    - apply H0 in H5.
      crush_re.
    - apply H in H5.
      crush_re.
    - apply H0 in H5.
      crush_re.
  Qed.

  Add Parametric Morphism : Cat with signature
      reg_eq ++> reg_eq ++> reg_eq as Cat_reg_eq_mor.
  Proof.
    dest_eq ; in_inv ; constructor.
    - apply H ; auto.
    - apply H0 ; auto.
    - apply H ; auto.
    - apply H0 ; auto.
  Qed.

  Lemma alt_comm : forall r1 r2, Alt r1 r2 [=] Alt r2 r1.
  Proof.
    dest_eq ; in_inv ; crush_re.
  Qed.

  Lemma alt_assoc : forall r1 r2 r3, Alt r1 (Alt r2 r3) [=] Alt (Alt r1 r2) r3.
  Proof.
    dest_eq ; in_inv ; try in_inv.
    - apply In_Alt_left.
      apply In_Alt_left.
      auto.
    - apply In_Alt_left.
      apply In_Alt_right.
      auto.
    - apply In_Alt_right.
      auto.
    - apply In_Alt_left.
      auto.
    - apply In_Alt_right.
      apply In_Alt_left.
      auto.
    - apply In_Alt_right.
      apply In_Alt_right.
      auto.
  Qed.

  Lemma alt_idem : forall r, Alt r r [=] r.
  Proof.
    dest_eq ; try in_inv ; auto ; crush_re.
  Qed.

  Lemma void_alt_unit : forall r, Alt Void r [=] r.
  Proof.
    dest_eq ; try in_inv ; auto ; try in_inv ; crush_re.
  Qed.

  Lemma void_cat_zero_left : forall r, Cat Void r [=] Void.
  Proof.
    dest_eq ; in_inv ; in_inv.
  Qed.

  Lemma void_cat_zero_right : forall r, Cat r Void [=] Void.
  Proof.
    dest_eq ; in_inv ; in_inv.
  Qed.

  Lemma ept_cat_unit_left : forall r, Cat Ept r [=] r.
  Proof.
    dest_eq ; try in_inv.
    - in_inv.
      compute.
      auto.
    - rewrite <- app_nil_l.
      auto.
  Qed.

  Lemma ept_cat_unit_right : forall r, Cat r Ept [=] r.
  Proof.
    dest_eq ; try in_inv.
    - in_inv.
      rewrite app_nil_r.
      auto.
    - rewrite <- app_nil_r ; auto.
  Qed.

  Hint Resolve alt_idem void_alt_unit void_cat_zero_left void_cat_zero_right
       ept_cat_unit_left ept_cat_unit_right.

  (** Optimized Constructors for null *)
  Definition alt (r1 r2 : re) : re :=
    match r1, r2 with
    | Void, r => r
    | r, Void => r
    | r1, r2 => if syn_eq_re r1 r2 then r1 else Alt r1 r2
    end.
  Notation "r1 <+> r2" := (alt r1 r2) (at level 50).

  Definition cat (r1 r2 : re) : re :=
    match r1, r2 with
    | Void, _ => Void
    | _, Void => Void
    | Ept, r => r
    | r, Ept => r
    | r1, r2 => Cat r1 r2
    end.
  Notation "r1 $ r2" := (cat r1 r2) (at level 50).

  Lemma opt_alt_correct : forall r1 r2, Alt r1 r2 [=] r1 <+> r2.
  Proof.
    destruct r1 ; auto ; destruct r2 ; auto ; crush ;
      rewrite alt_comm ; auto ;
        match goal with
        | [ _ : _ |- reg_eq _ (if ?e then _ else _) ] => destruct e
        end ; crush ;
          rewrite alt_comm ; crush.
  Qed.

  Lemma opt_cat_correct : forall r1 r2, Cat r1 r2 [=] r1 $ r2.
    destruct r1 ; auto ; destruct r2 ; auto ; crush.
  Qed.

  (** Null and Some Properties *)
  Fixpoint null (r : re) : re :=
    match r with
    | Void => Void
    | Ept => Ept
    | Char _ => Void
    | Alt r1 r2 => (null r1) <+> (null r2)
    | Cat r1 r2 => (null r1) $ (null r2)
    | Star _ => Ept
    end.

  Lemma null_void_or_ept : forall r, {null r = Void} + {null r = Ept}.
  Proof.
    induction r ; crush.
  Qed.

  Lemma null_correct : forall r, [[ r ]] [] <-> null r = Ept.
  Proof.
    intros.
    split ; intros.
    - induction r ; crush ; in_inv.
      + destruct (null_void_or_ept r2) ;
          apply IHr1 in H3 ; crush.
      + destruct (null_void_or_ept r1) ;
          apply IHr2 in H3 ; crush.
      + apply app_eq_nil in H2 ; crush.
    - induction r ; crush.
      + destruct (null_void_or_ept r1) ;
          destruct (null_void_or_ept r2) ;
          rewrite e in H ;
          rewrite e0 in H ;
          crush ; crush_re.
      + destruct (null_void_or_ept r1) ;
          destruct (null_void_or_ept r2) ;
          rewrite e in H ;
          rewrite e0 in H ;
          crush.
        assert (([] : list T) ++ [] = []) by auto.
        rewrite <- H2.
        constructor ; auto.
  Qed.

  Lemma null_correct_corr : forall r s, [[ null r ]] s -> s = [].
  Proof.
    intros.
    destruct (null_void_or_ept r) ; rewrite e in H ; in_inv.
    auto.
  Qed.

  (** Derivatives *)
  Fixpoint deriv (r : re) (c : T) : re :=
    match r with
    | Void => Void
    | Ept => Void
    | Char c' => if dec_eq c c' then Ept else Void
    | Alt r1 r2 => (deriv r1 c) <+> (deriv r2 c)
    | Cat r1 r2 => ((deriv r1 c) $ r2) <+> ((null r1) $ (deriv r2 c))
    | Star r => (deriv r c) $ (Star r)
    end.

  Lemma deriv_correct :
    forall r a s, [[ deriv r a ]] s <-> [[ r ]] (a :: s).
  Proof.
    Hint Rewrite null_correct null_correct_corr.
    split ; intros.
    - dependent induction r ; crush ; try in_inv.
      + destruct (dec_eq a t) ; in_inv ; crush.
      + apply opt_alt_correct in H.
        specialize (IHr1 a s).
        specialize (IHr2 a s).
        in_inv ; crush ; crush_re.
      + apply opt_alt_correct in H.
        in_inv ; crush ; apply opt_cat_correct in H3 ;
          in_inv ; rewrite app_comm_cons.
        * constructor ; auto ; apply IHr1 ; auto.
        * pose proof H1.
          apply null_correct_corr in H1.
          subst.
          simpl.
          rewrite <- app_nil_l.
          constructor ; auto.
          destruct (null_void_or_ept r1) ; crush.
          rewrite e in H.
          discriminate.
      + apply opt_cat_correct in H.
        induction s ; intros.
        * in_inv.
          apply app_eq_nil in H2.
          destruct H2.
          subst.
          simpl.
          rewrite <- app_nil_r.
          constructor ; auto.
        * in_inv.
          destruct H2.
          rewrite app_comm_cons.
          constructor ; auto.
    - dependent induction r ; crush ; try in_inv.
      + destruct (dec_eq a a) ; crush.
      + apply opt_alt_correct.
        constructor ; crush.
      + apply opt_alt_correct.
        apply In_Alt_right.
        crush.
      + apply opt_alt_correct.
        induction s1.
        * simpl in *.
          subst.
          apply In_Alt_right.
          apply opt_cat_correct.
          rewrite <- app_nil_l.
          constructor ; auto.
          apply null_correct in H3.
          rewrite H3.
          constructor.
        * constructor.
          apply opt_cat_correct.
          rewrite <- app_comm_cons in H2.
          invert H2.
          constructor ; crush.
      + apply opt_cat_correct.
        remember (Star r) as r'.
        remember (a :: s) as s'.
        generalize Heqr'.
        generalize Heqs'.
        clear Heqr'.
        clear Heqs'.
        induction H ; crush.
        destruct  s1 ; crush.
  Qed.

  Fixpoint derivs (r : re) (s : str) : re :=
    match s with
    | [] => r
    | c :: s' => derivs (deriv r c) s'
    end.

  Lemma derivs_correct :
    forall s r, [[ derivs r s ]] [] <-> [[ r ]] s.
  Proof.
    induction s ; crush.
    - apply deriv_correct ; apply IHs ; crush.
    - apply deriv_correct in H.
      apply IHs in H ; crush.
  Qed.

  Definition match_re (r : re) (s : str) :=
    let res := null (derivs r s) in
    if syn_eq_re res Ept then true else false.

  Lemma match_re_unfold :
    forall r a s, match_re r (a :: s) = match_re (deriv r a) s.
  Proof.
    crush.
  Qed.

  Lemma match_re_ltr : forall r s, [[ r ]] s -> match_re r s = true.
  Proof.
    intros.
    unfold match_re.
    apply derivs_correct in H.
    crush.
  Qed.

  Lemma match_re_rtl : forall s r, match_re r s = true -> [[ r ]] s.
  Proof.
    intros.
    unfold match_re in H.
    apply derivs_correct.
    destruct (syn_eq_re (null (derivs r s)) Ept) ; crush.
  Qed.

  Theorem match_re_correct : forall r s, [[ r ]] s <-> match_re r s = true.
  Proof.
    split.
    - apply match_re_ltr.
    - apply match_re_rtl.
  Qed.

  (** Nonnull and Standardization *)
  Fixpoint nonnull (r : re) : re :=
    match r with
    | Void => Void
    | Ept => Void
    | Char c => Char c
    | Alt r1 r2 => Alt (nonnull r1) (nonnull r2)
    | Cat r1 r2 => Alt (Alt (Cat (null r1) (nonnull r2))
                            (Cat (nonnull r1) (null r2)))
                       (Cat (nonnull r1) (nonnull r2))
    | Star r => Cat (nonnull r) (Star (nonnull r))
    end.

  Lemma nonnull_no_empty : forall r, ~ [[ nonnull r ]] [].
  Proof.
    induction r ; simpl ; auto ; intro H ; invert H ; auto.
    - destruct (null_void_or_ept r1) ;
        destruct (null_void_or_ept r2) ;
        auto ;
        rewrite e in * ;
        rewrite e0 in * ;
        invert H3 ; invert H2 ;
          try match goal with
          | [ H : [[ Void ]] _ |- _ ] => invert H
          end ;
          apply app_eq_nil in H1 ;
          crush.
    - invert H3 ; invert H2;
        apply app_eq_nil in H1 ;
        destruct H1 ; subst ;
          auto.
    - apply app_eq_nil in H2.
      destruct H2.
      subst.
      auto.
  Qed.

  Lemma app_neq_nil :
    forall T s1 s2, s1 ++ s2 <> ([]:list T) <-> s1 <> [] \/ s2 <> [].
  Proof.
    split ; intros.
    - destruct s1 ; destruct s2 ; auto ; left ;
        discriminate.
    - intro H1.
      apply app_eq_nil in H1 ; crush.
  Qed.

  Lemma star_roll : forall r s, [[ Cat r (Star r) ]] s -> [[ Star r ]] s.
  Proof.
    induction r ; crush ; invert H ; auto.
  Qed.

  Lemma star_unroll : forall r, Star r [=] Alt Ept (Cat r (Star r)).
  Proof.
    dest_eq.
    - remember (Star r) as r'.
      generalize Heqr'.
      clear Heqr'.
      induction H ; crush.
    - invert H ; invert H3 ; auto.
  Qed.

  Fixpoint iterate_re (r : re) (n : nat) :=
    match n with
    | 0 => Ept
    | S n' => Cat r (iterate_re r n')
    end.

  Lemma star_fixpoint : forall r s,
      [[ Star r ]] s <-> exists n, [[ iterate_re r n ]] s.
  Proof.
    split ; intros.
    - remember (Star r) as r'.
      generalize Heqr'.
      clear Heqr'.
      induction H ; crush.
      + exists 0 ; auto.
      + exists (S x).
        simpl in *.
        constructor ; auto.
    - destruct H.
      generalize dependent s.
      induction x ; crush ; invert H ; crush.
  Qed.

  Lemma iterate_nonnull : forall n r s,
      (forall s : list T, s <> [] -> [[r]] s <-> [[nonnull r]] s) ->
      [[ iterate_re (nonnull r) n ]] s ->
      [[ Star r ]] s.
  Proof.
    induction n ; crush ; invert H0 ; auto.
    constructor ; auto.
    apply H ; auto.
    intro.
    subst.
    apply (nonnull_no_empty r) ; auto.
  Qed.

  Lemma nonnull_preserves_meaning :
    forall r s, s <> [] -> [[ r ]] s <-> [[ nonnull r ]] s.
  Proof.
    induction r ; intros ; split ; intros ; auto.
    - invert H0. contradict H ; auto.
    - invert H0.
    - simpl. invert H0.
      + apply In_Alt_left.
        apply IHr1 ; auto.
      + apply In_Alt_right.
        apply IHr2 ; auto.
    - simpl in H0.
      invert H0.
      + apply In_Alt_left.
        apply IHr1 ; auto.
      + apply In_Alt_right.
        apply IHr2 ; auto.
    - simpl.
      invert H0.
      apply app_neq_nil in H.
      destruct H.
      + destruct s2.
        * apply In_Alt_left.
          apply In_Alt_right.
          constructor ; crush.
          apply IHr1 ; auto.
        * apply In_Alt_right.
          constructor ; [ apply IHr1 | apply IHr2 ] ; auto.
          crush.
      + destruct s1.
        * apply In_Alt_left.
          apply In_Alt_left.
          constructor ; crush.
          apply IHr2 ; auto.
        * apply In_Alt_right.
          constructor ; [ apply IHr1 | apply IHr2 ] ; auto.
          crush.
    - invert H0.
      + invert H4.
        * destruct (null_void_or_ept r1) ; rewrite e in *.
          -- invert H3 ; invert H2.
          -- invert H3 ; constructor ; crush.
             ++ invert H2 ; apply null_correct ; auto.
             ++ apply IHr2 ; crush.
                apply H.
                invert H2 ; crush.
        * destruct (null_void_or_ept r2) ; rewrite e in *.
          -- invert H3 ; invert H5.
          -- invert H3 ; constructor ; crush.
             ++ apply IHr1 ; crush.
                apply H.
                invert H5 ; crush.
             ++ invert H5 ; apply null_correct ; auto.
      + invert H4.
        apply app_neq_nil in H.
        destruct H.
        * constructor.
          -- apply IHr1 ; auto.
          -- apply IHr2 ; auto.
             intro H1.
             subst.
             apply (nonnull_no_empty r2) ; auto.
        * constructor.
          -- apply IHr1 ; auto.
             intro H1.
             subst.
             apply (nonnull_no_empty r1) ; auto.
          -- apply IHr2 ; auto.
    - remember (Star r) as r'.
      generalize Heqr'.
      clear Heqr'.
      induction H0 ; crush.
      clear IHin_re1.
      apply app_neq_nil in H.
      destruct H.
      + apply IHr in H0_ ; auto.
        constructor ; auto.
        destruct s2 ; auto.
        assert ([[Cat (nonnull r) (Star (nonnull r))]] (t :: s2))
          by (apply IHin_re2 ; crush).
        apply star_roll in H0.
        auto.
      + destruct s1 ; auto.
        apply IHr in H0_ ; crush.
        rewrite app_comm_cons.
        constructor ; auto.
        apply star_roll in H1.
        auto.
    - simpl in *.
      apply star_roll in H0.
      apply star_fixpoint in H0.
      destruct H0.
      eapply iterate_nonnull ; eauto.
  Qed.

  Definition standardize (r : re) : re :=
    Alt (null r) (nonnull r).

  Theorem standardize_correct : forall r, standardize r [=] r.
  Proof.
    unfold standardize.
    intros.
    dest_eq ; destruct s.
    - invert H.
      + destruct (null_void_or_ept r) ; crush.
        rewrite e in H3.
        simpl in H3.
        apply H3.
      + exfalso ; apply (nonnull_no_empty r) ; auto.
    - invert H.
      + destruct (null_void_or_ept r) ;
          rewrite e in H3 ; invert H3.
      + apply nonnull_preserves_meaning ; crush.
    - constructor.
      apply null_correct in H.
      rewrite H.
      auto.
    - apply In_Alt_right.
      apply nonnull_preserves_meaning in H ; crush.
  Qed.

  (** acc and Properties *)
  Fixpoint acc (r : re) (s : str) (k : str -> bool) (n : nat) :=
    match n with
    | 0 => false
    | S n =>
      match r with
      | Void => false
      | Ept => k s
      | Char c =>
        match s with
        | [] => false
        | d :: s' => if dec_eq c d then k s' else false
        end
      | Alt r1 r2 => acc r1 s k n || acc r2 s k n
      | Cat r1 r2 => acc r1 s (fun s' => acc r2 s' k n) n
      | Star r' => k s || acc (Cat r' r) s k n
      end
    end.

  Ltac dest_null r :=
    destruct (null_void_or_ept r) as [e | e] ;
    rewrite e in * ;
    clear e.

  Ltac acc_inv :=
    match goal with
    | [ H : acc _ _ _ ?n = true |- _ ] => destruct n ; crush
    end.

  Definition is_nil (l : str) := match l with [] => true | _ => false end.

  Ltac acc_simp :=
    intros ; simpl in * ;
    try match goal with
        | [ H : _ || _ = true |- _ ] => apply orb_true_elim in H ; destruct H
        | [ H : exists _, _ |- _ ] => destruct H
        | [ H : [[ Void ]] _ |- _ ] => invert H
        | [ H : [[ Ept ]] _ |- _ ] => invert H ; simpl
        | [ H : [[ Char _ ]] _ |- _ ] => invert H ; simpl
        | [ H : [[ Alt _ _ ]] _ |- _ ] => invert H ; simpl
        | [ H : [[ Cat _ _ ]] _ |- _ ] => invert H ; simpl
        | [ H : _ |- _ || _ = true ] => apply orb_true_intro ; auto
        | [ H : is_nil ?s = true |- _ ] => destruct s ; crush
        | [ H : _ /\ _ |- _ ] => destruct H
        | [ H : ?x <> ?x |- _ ] => contradict H ; auto
        | [ H : [[ standardize _ ]] _ |- _ ] => invert H
        | [ H : [[ null ?r ]] _ |- _ ] => dest_null r
        | [ H : _ |- false = true \/ _ ] => right
        | [ H : (fun _ : _ => _) _ = _ |- _ ] => simpl in H
        | [ H : _ |- (if ?t then _ else _) = true ] => destruct t
        end ;
    auto.

  Ltac smash := repeat acc_simp.

  Ltac dst x :=
    destruct x ; simpl in * ; try discriminate.

  Lemma continuation_swap : forall r s k1 k2 n,
      acc r s k1 n = true ->
      (forall x, k1 x = true -> k2 x = true) ->
      acc r s k2 n = true.
  Proof.
    refine (fix IH r s k1 k2 n H1 H2 {struct n} :
              acc r s k2 n = true := _).
    destruct r ; dst n ; repeat acc_simp.
    - destruct s ; try discriminate.
      destruct (dec_eq t t0) ; auto.
    - left ; auto ; eapply IH ; eauto.
    - right ; auto ; eapply IH ; eauto.
    - eapply IH ; eauto.
      intros.
      eapply IH ; eauto.
      simpl in *.
      auto.
    - eapply IH in e ; eauto.
  Qed.

  Lemma acc_n_greater : forall r s k n m,
      acc r s k n = true ->
      acc r s k (n + m) = true.
  Proof.
    refine (fix IH r s k n m H {struct n} :
              acc r s k (n + m) = true := _).
    destruct r ; dst n ; repeat acc_simp ; apply IH ;
      eapply continuation_swap ; eauto.
  Qed.

  Lemma ept_or_not : forall s : str, {s = []} + {s <> []}.
  Proof.
    destruct s ; auto.
    right.
    intro H.
    discriminate.
  Qed.

  Lemma null_nonnull_void : forall r, null (nonnull r) = Void.
  Proof.
    intros.
    induction r ; crush.
    dest_null r1 ; auto.
  Qed.

  Lemma null_idem : forall r, null (null r) = null r.
  Proof.
    intros.
    induction r ; crush ;
      dest_null r1 ;
      dest_null r2 ; auto.
  Qed.

  Lemma acc_sound : forall r s k n,
      acc r s k n = true ->
      exists s1 s2,
        s = s1 ++ s2 /\
        [[ r ]] s1 /\
        k s2 = true.
  Proof with smash.
    refine (fix IH r s k n H {struct n} :
              exists s1 s2,
                s = s1 ++ s2 /\
                [[ r ]] s1 /\
                k s2 = true := _).
    destruct r ; destruct n ; crush.
    - exists []. exists s. auto.
    - destruct s ; try discriminate.
      destruct (dec_eq t t0) ; try discriminate.
      subst. exists [t0]. exists s. auto.
    - acc_simp ; apply IH in e ; smash ;
        exists x ; exists x0 ;
        crush.
    - apply IH in H...
      apply IH in H1...
      exists (x ++ x1). exists x2.
      crush.
    - smash.
      + exists []. exists s. auto.
      + apply IH in e...
        eexists ; eexists ; eauto.
  Qed.

  Lemma acc_complete' : forall r s s1 s2 k,
      s = s1 ++ s2 ->
      k s2 = true ->
      [[ nonnull r ]] s1 ->
      exists n, acc (nonnull r) s k n = true.
  Proof with smash.
    induction r...
    - exists 1...
    - edestruct IHr1 ; eauto...
      exists (S x)...
    - edestruct IHr2 ; eauto...
      exists (S x)...
    - edestruct (IHr2) ; eauto.
      exists (S (S (S x)))...
      left... left... dst x...
    - edestruct (IHr1) ; eauto.
      exists (S (S (S x)))...
      rewrite app_nil_r.
      left... right... dst x...
    - edestruct (IHr2 (s3 ++ s2)) ; eauto.
      edestruct (IHr1 (s0 ++ (s3 ++ s2))) ; eauto.
      + instantiate (1 := fun s' => acc (nonnull r2) s' k x)...
      + exists (S (S (x + x0)))...
        rewrite <- app_assoc.
        right...
        rewrite plus_comm.
        apply acc_n_greater.
        eapply continuation_swap ; eauto.
        intros.
        simpl in H3.
        rewrite plus_comm.
        apply acc_n_greater...
    - edestruct IHr ; eauto...
      apply star_fixpoint in H6.
      destruct H6.
      (* I know that there is a way to do this... ☹ *)
  Admitted.

  Lemma acc_complete : forall r s s1 s2 k,
      s = s1 ++ s2 ->
      k s2 = true ->
      [[ standardize r ]] s1 ->
      exists n, acc (standardize r) s k n = true.
  Proof with smash.
    intros.
    unfold standardize in *.
    dest_null r...
    - edestruct (acc_complete' r) ; eauto.
      exists (S x)...
    - exists 2...
    - edestruct (acc_complete' r) ; eauto.
      exists (S x)...
  Qed.

  Definition match_simple (r : re) (s : str) (n : nat) : bool :=
    acc (standardize r) s is_nil n.

  Lemma match_simple_ltr :
    forall r s, [[ r ]] s -> exists n, match_simple r s n = true.
  Proof.
    intros.
    unfold match_simple.
    eapply acc_complete ; crush.
    apply standardize_correct.
    auto.
  Qed.

  Lemma match_simple_rtl :
    forall r s, (exists n, match_simple r s n = true) -> [[ r ]] s.
  Proof.
    unfold match_simple.
    intros.
    destruct H.
    apply standardize_correct.
    pose proof (acc_sound (standardize r) s is_nil x) ; crush.
    unfold is_nil in H3.
    destruct x1 ; try discriminate.
    rewrite app_nil_r.
    auto.
  Qed.

  Lemma match_simple_correct :
    forall r s, [[ r ]] s <-> exists n, match_simple r s n = true.
  Proof.
    split.
    - apply match_simple_ltr.
    - apply match_simple_rtl.
  Qed.
End Regex.