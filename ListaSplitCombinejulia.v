(*Aluna: Julia Llorente*)

Require Export Coq.Lists.List.
Import ListNotations.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Lemma eq_cons : forall (X:Type) (l1 l2: list X) (x: X),
  l1 = l2 -> x :: l1 = x :: l2.
  intros X l1 l2 x.
  intro H.
  rewrite H.
  reflexivity.
Qed.

(* para usar no combine_split *)
Theorem tail_eq: forall (X: Type) (h: X) (l1 l2: list X),
l1 = l2 -> h :: l1 = h :: l2.
Proof.
  intros. apply f_equal. apply H.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [|h t IH1].
  - intros l1 l2 H. simpl in H. injection H as H1 H2. inversion H1. inversion H2. reflexivity.
  - intros. inversion H. destruct h. destruct (split t). simpl in H1. inversion H1. simpl.
    apply tail_eq. apply IH1. reflexivity. Qed.




Definition split_combine : Prop :=
  forall (X Y:Type) (l1:list X) (l2:list Y), 
  length l1 = length l2 -> split (combine l1 l2) = (l1,l2).
  
Theorem split_combine' : split_combine.
Proof.
  intros X Y l1. induction l1 as [| h1 t1 IH1].
  - intros. simpl. destruct l2 as [| h2 t2 _]. 
    + reflexivity.
    + inversion H. 
  - intros. inversion H. destruct l2 as [| h2 t2].
    + inversion H1. 
    + inversion H1. apply IH1 in H2. simpl. rewrite -> H2. reflexivity. Qed.
