
Require Export Coq.Lists.List.
Import ListNotations.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.  
  intros X P H H0.
  - unfold not. 
    + destruct H0. apply H0. apply H.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  - split.
    + intros H. destruct H. inversion H.
      left. exists x. apply H0.
      right. exists x.  apply H0.
    + intros H. destruct H. inversion H.
      exists x. left. apply H0.
      inversion H. exists x. right. apply H0.
Qed.

Theorem dist_exists_and : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
Proof.
  intros X P Q x. inversion x. split.
  - exists x0. inversion H. apply H0.
  - exists x0. inversion H. apply H1.
Qed.


Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [| h t h1].
  - simpl. intros [].
  - simpl. intros [h2 | h3].
    + left. rewrite h2. reflexivity.
    + right. apply h1. apply h3.
Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  induction l as [| h t].
    - simpl. intros [].
    - simpl. intros [h1 | h2].
      + exists h. split.
          apply h1.
          left. reflexivity.
      + apply IHt in h2. destruct h2 as [w [F I]].
        exists w. split. apply F. 
        right. apply I.
    - intros [w [F I]]. rewrite <- F. apply In_map. apply I.
Qed.

Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l l' a. split.
  induction l as [| h t HL].
  - simpl. intros h. right. apply h.
  - simpl. intros [h1 | h2].
    + left. left. apply h1.
    + apply or_assoc. right. apply HL. apply h2.
  - induction l as [| h t].
    + simpl. intros [H1 | H2]. destruct H1.
    apply H2.
    + simpl. intros [[H1|H2] | H3].
      left. apply H1.
      right. apply IHt. left. apply H2.
      right. apply IHt.
      right. apply H3. 
Qed. 

Theorem excluded_middle_irrefutable:  forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  intros P.
  unfold not. 
  intros.
  apply H. right. intros HP. 
  apply H. left. apply HP.
Qed.

Theorem disj_impl : forall (P Q: Prop),
 (~P \/ Q) -> P -> Q.
Proof.
  intros P Q H1 H2.
  destruct H1 as [H3 | H4].
  - contradiction.
  - apply H4.
Qed.


Theorem Peirce_double_negation: forall (P : Prop), (forall P Q : Prop,
  (((P->Q)->P)->P)) -> (~~ P -> P).
Proof.
  intros P. intros H I.
  unfold not in I. apply H with (Q := False). intros J. apply I in J. contradiction.
Qed.

Theorem double_negation_excluded_middle : forall (P:Prop),
  (forall (P:Prop), (~~ P -> P)) -> (P \/ ~P). 
Proof.
  intros P. intros H.
  apply H. intros I. apply I. left. apply H. intros J. apply I. right. assumption.
Qed.
   








