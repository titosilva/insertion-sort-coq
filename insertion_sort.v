(** * Formalização da correção do algoritmo de ordenação por inserção em Coq *)

(* begin hide *)
 Require Import Arith List Lia.
(* end hide *)
 
(** A seguir definimos a função [insere] que tem um comportamento especial. A ideia é que se a lista [l] estiver ordenada então [insere x l] estará também ordenada. *)
Fixpoint insere x l :=
  match l with
  | nil => x::nil
  | h::tl => if (x <=? h) then x::l else h::(insere x tl) 
  end.

(** Aqui, implementamos o algoritmo de insertion sort a partir da função [insere] *)
Fixpoint ord_insercao l :=
  match l with
  | nil => l
  | h::tl => insere h (ord_insercao tl)
  end.

  
(** ** Formalização da Correção do Insertion Sort (10 pontos) *)

(** A definição [sorted] serve para decidir se uma lista é ou não é ordenada.*)
Inductive sorted : list nat -> Prop :=
| sorted_nil: sorted nil
| sorted_one: forall x, sorted (x :: nil)
| sorted_all: forall x y l, x <= y -> sorted (y :: l) -> sorted (x :: y :: l).                        

(** Queremos chegar ao teorema [ord_insercao_sorted], que afirma que se aplicarmos
o insertion sort a uma lista, o resultado será uma lista ordenada. No entanto, para
auxiliar na prova desse teorema, precisamos antes provar o lema [insertion_sorted] **)

(** Lemas auxiliares para a prova de [insertion_sorted] **)
(** le_all é um valor que é menor que igual 
    que todos os elementos de uma lista **)
Definition le_all x l := forall y, In y l -> x <= y.

(** O lema [le_all_sorted] afirma que se nós tivermos um elemento que é menor que todos os 
elementos de uma lista ordenada e criarmos uma nova lista que é composta por esse elemento 
mais a lista ordenada original, a nova lista também estará ordenada. Intuitivamente, facilmente
somos convencidos. No entanto, a prova formal é necessária. **)
Lemma le_all_sorted: forall l a, le_all a l -> sorted l -> sorted (a::l).
  intros l a H_a_le_all Hl_sorted.
  (** Analisamos os casos para a lista l*)
  case l eqn:Hl.
  - apply sorted_one.
  - apply sorted_all.
    * unfold le_all in H_a_le_all.
      apply H_a_le_all. 
      apply in_eq.
    * assumption.
Qed.

(** O lema [le_le_all] ajuda a analisar um caso específico de listas, 
quando um elemento x, maior que um [le_all] da lista l, é inserido na 
cabeça da lista. Nesse caso, o [le_all] em questão continua sendo [le_all].
Este lema é usado na prova de [le_all_insere] **)
Lemma le_le_all: forall l x y, y <= x -> le_all y l -> le_all y (x::l).
Proof.
  intros l x y H_y_le_x H_y_le_all.
  unfold le_all. intros z Hz.
  inversion Hz; subst.
  - assumption.
  - unfold le_all in H_y_le_all.
    apply H_y_le_all. assumption.
Qed.

(** O lema [le_all_insere] afirma que um [le_all] é preservado mediante um [insere] de um 
novo elemento na lista, desde que o elemento inserido seja menor que o [le_all] em questão **)
Lemma le_all_insere: forall l x y, y <= x -> le_all y l -> le_all y (insere x l).
Proof.
  intros l x y H_y_le_x H_y_le_all.
  induction l as [|h tl].
  - simpl. unfold le_all. intros z H.
    inversion H.
    + lia.
    + inversion H0.
  - simpl. destruct (x <=? h) eqn:Hxh.
    + apply le_le_all. all: assumption.
    + apply le_le_all.
      * unfold le_all in H_y_le_all.
        apply H_y_le_all. apply in_eq.
      * apply IHtl.
        unfold le_all in H_y_le_all.
        simpl in H_y_le_all.
        unfold le_all.
        rewrite Nat.leb_gt in Hxh.
        intros z H.
        apply H_y_le_all.
        auto.
Qed.

(** O lema [sublist_sorted] analise o comportamento de um caso específico de listas com relação à 
ordenação **)
Lemma sublist_sorted: 
  forall l x y, sorted (x::y::l) -> sorted (x::l).
Proof.
  intros l x y H.
  induction l as [|h tl].
  - apply sorted_one.
  - inversion H; subst.
    inversion H4; subst.
    apply sorted_all.
    * lia.
    * assumption.
Qed.
  
(** O lema [sorted_le_all]  afirma que se a lista (a::l) está ordenada, então a é [le_all] de l*)
Lemma sorted_le_all: forall l a, sorted (a::l) -> le_all a l.
Proof.
  induction l as [|h tl].
  - intros a H. unfold le_all.
    intros y Hnil. inversion Hnil.
  - intros a H. apply le_le_all.
    + inversion H; subst. assumption.
    + apply IHtl. inversion H; subst.
      apply sublist_sorted in H. assumption.
Qed.

Lemma sorted_sublist: forall l a, sorted (a::l) -> sorted l.
Proof.
  intros l x H.
  induction l as [|h tl].
  - apply sorted_nil.
  - inversion H; subst.
    assumption.
Qed.

(** O lema [insere_sorted] será necessário para a prova do teorema final 
    [ord_insercao_sorted], que finaliza a prova de correção do insertion sort.
**)
(** Os sub-lemas desse lema foram sendo provados à medida que eram 
necessários. Primeiro eram tomados como Admitted, para testar resul-
tados, e depois eram realmente provados. **)
Lemma insere_sorted: forall l x, sorted l -> sorted (insere x l).
Proof.
  induction l as [| h tl].
  - intros x H.
    unfold insere.
    apply sorted_one.
  - intros x H.
    simpl. destruct (x <=? h) eqn:Hineq.
    + apply sorted_all. rewrite Nat.leb_le in *. all: assumption.
    + apply le_all_sorted.
      * apply le_all_insere.
        ** rewrite Nat.leb_gt in *.
           apply Nat.lt_le_incl. assumption.
        ** apply sorted_le_all. assumption.
      * apply IHtl. apply sorted_sublist in H. assumption.
Qed.

(** Finalmente chegamos ao nosso objetivo final *)
Theorem ord_insercao_sorted: forall l, sorted (ord_insercao l).
Proof.
  (** De começo já tentamos por indução, mas sempre chegávamos
      na necessidade do lema insere_sorted, sem saber que era
      necessário prová-lo por indução. As notas de aula deram
      um norte **)
  induction l as [|h tl].
  - unfold ord_insercao. apply sorted_nil.
    (** Aqui, tomamos o lema [insertion_sorted] como Admitted
        inicialmente, e depois de verificar que resolveria a prova
        partimos para a sua formalização. **)
  - simpl. apply insere_sorted. assumption.
Qed.
  
(** ** Insertion Sort gera permutações de listas (10 pontos) *)
Require Import Permutation.

(** Decidimos provar o outro teorema ao invés deste *)
Theorem ord_insercao_perm: forall l, Permutation l (ord_insercao l).
Proof.
Admitted.

(* ou *)

(** Queremos provar o teorema [ord_insercao_equiv], mas para isto
provamos vários lemas auxiliares antes *)

Fixpoint num_oc x l :=
  match l with
  | nil => 0
  | h::tl => if (x =? h) then S (num_oc x tl) else num_oc x tl
  end.

Definition equiv l l' := forall x, num_oc x l = num_oc x l'.

(** O lema [num_oc_insere] afirma que realizar um [insere] em uma lista aumenta o número
de ocorrências do elemento inserido em um, por meio do operador "S", de sucessão nos naturais
Este lema é utilizado na prova do teorema [ord_insercao_equiv] *)
Lemma num_oc_insere: forall l x, num_oc x (insere x l) = S (num_oc x l).
Proof.
  induction l as [|h tl].
  - intros x. simpl. replace (x =? x) with true.
    + reflexivity.
    + apply beq_nat_refl.
  - intros x. simpl. destruct (x <=? h) eqn:Hx_le_h.
    + destruct (x =? h) eqn:Hx_eq_h.
      * simpl. 
        (** Aqui, não conseguimos encontrar uma forma
            melhor de continuar a prova do que essa forma
            abaixo, que é obviamente verdadeira.
        **)
        replace (x =? x) with true.
        replace (x =? h) with true.
        reflexivity. apply beq_nat_refl.
     * simpl. 
       replace (x =? x) with true.
       replace (x =? h) with false.
       reflexivity. apply beq_nat_refl.
  + destruct (x =? h) eqn:Hx_eq_h.
    * simpl.
      replace (x =? x) with true.
      replace (x =? h) with true.
      rewrite IHtl. reflexivity.
      apply beq_nat_refl.
    * simpl.
      replace (x =? x) with true.
      replace (x =? h) with false.
      rewrite IHtl. reflexivity.
      apply beq_nat_refl.
Qed.

(** O lema [num_oc_insere_diff] afirma que se for inserido um elemento qualquer em uma lista, apenas a 
quantidade de ocorrências desse elemento na lista é alterada, enquanto a quantidade de ocorrências de 
outros elementos é preservada. Este lema é utilizado na demonstração do teorema [ord_insercao_equiv]*)
Lemma num_oc_insere_diff: 
  forall l x y, (x =? y) = false -> num_oc x (insere y l) = num_oc x l.
Proof.
  intros l x y Hx_ne_y.
  induction l as [|h tl].
  - simpl. replace (x =? y) with false. reflexivity.
  - simpl. destruct (y <=? h) eqn:Hyh.
    + destruct (x =? h) eqn:Hxh.
      * simpl. destruct (x =? y). inversion Hx_ne_y.
        ** replace (x =? h) with true. reflexivity.
      * simpl. destruct (x =? y). inversion Hx_ne_y.
        ** replace (x =? h) with false. reflexivity.
   + destruct (x =? h) eqn:Hxh.
     * simpl. 
       replace (x =? h) with true.
       rewrite IHtl. reflexivity.
     * simpl. replace (x =? h) with false. assumption.
Qed.

(** O teorema [ord_insercao_equiv] consiste de uma afirmação equivalente a afirmar que a lista
gerada pelo insertion sort sobre uma lista l é uma permutação da lista l. A afirmação é de que 
o [ord_insercao] preserva a quantidade de ocorrência de cada um dos elementos na lista sendo 
ordenada **)
Theorem ord_insercao_equiv: forall l, equiv l (ord_insercao l).
Proof.
  induction l as [|h tl].
  - simpl. unfold equiv. reflexivity.
  - simpl. unfold equiv in *. intro n.
    simpl. destruct (n =? h) eqn:Hnh.
    + apply Nat.eqb_eq in Hnh. subst.
      rewrite num_oc_insere.
      rewrite IHtl.
      reflexivity.
    + rewrite num_oc_insere_diff.
      apply IHtl. assumption.
Qed.

(** ** Formalização da Complexidade do Insertion Sort (10 pontos) *)

(** A função [T_insere] computa o número de comparações necessárias para inserir o elemento [x] na lista [l]: *)
Fixpoint T_insere x l :nat :=
  match l with
  | nil => 0
  | h::tl => if x <=? h then 1 else S (T_insere x tl)
  end.

(** A função [T_insere_w] computa o número máximo de comparacões necessárias para inserir um elemento em uma lista de tamanho [n]:  *)

Fixpoint T_insere_w (n:nat) : nat :=
  match n with
  | 0 => 0
  | S k => S (T_insere_w k)
  end.

(** Alguns lemas auxiliares:*)
(** O lema [T_insere_w_comp] consiste de decidir valores para o [T_insere_w] pelo tamanho da lista*)
Lemma T_insere_w_comp: forall n, T_insere_w n = n.
Proof.
  intros n.
  induction n.
  - simpl. reflexivity.
  - simpl. auto.
Qed.

Lemma T_insere_comp: forall l x, T_insere x l <= T_insere_w (length l).
Proof.
  intros l x.
  induction l as [|h tl].
  - simpl. auto.
  - simpl. destruct (x <=? h) eqn:Hxa.
    + lia.
    + lia.
Qed.
  
(* big-O notation *)
Definition big_o (g:nat->nat) (f:nat->nat) : Prop :=
exists (c n0:nat), c > 0
                /\ n0 > 0
                /\ forall (n:nat), n >= n0 -> 0 <= (f n) <= (c * (g n)).


(* special growths *)
Definition linear_growth    := big_o (fun (n:nat) => n).
Definition quadratic_growth := big_o (fun (n:nat) => n * n).

(** 5 pontos: Provar que a função [insere] é linear no pior caso. *)
Theorem T_insere_linear: linear_growth T_insere_w.
Proof.
  unfold linear_growth.
  unfold big_o.
  (** Para provas de existência, é útil usar exemplos/casos **)
  (** Para c = 1 e n0 = 1, vou provar que é verdade **)
  exists 1.
  exists 1.
  repeat split; auto.
  - rewrite T_insere_w_comp. lia.
  - rewrite T_insere_w_comp. lia.
Qed.

Lemma T_insere_linear': forall l x, T_insere x l <= length l.
Proof.
  intros l x.
  induction l as [|h tl].
  - simpl. auto.
  - simpl. destruct (x <=? h) eqn:Hxh.
    + lia.
    + lia.
Qed.

Fixpoint T_ord_insercao l :=
  match l with
  | nil => 0
  | h::tl => T_ord_insercao tl + T_insere h (ord_insercao tl)
  end.

Fixpoint T_ord_insercao_w (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => T_ord_insercao_w k + T_insere_w k
  end.

(** Falso: considere inserir 3 em 4::1::2::nil 

Lemma T_insere_ord_insercao: forall l a, T_insere a (ord_insercao l) <= T_insere a l.
Proof.  
*)

Lemma ord_insercao_length: forall l, length (ord_insercao l) = length l.
Proof.
Admitted.
  
Lemma T_ord_insercao_comp: forall l, T_ord_insercao l <= T_ord_insercao_w (length l).
Proof.
  induction l.
  - simpl. auto.
  - simpl.
    apply plus_le_compat.
    + apply IHl.
    + rewrite T_insere_w_comp.
      pose proof ord_insercao_length.
      specialize (H l).
      rewrite <- H.
      apply T_insere_linear'.
Qed.

(** 5 pontos: Provar que a função [ord_insercao] é quadrático no pior caso. *)
Theorem T_ord_insercao_quad: quadratic_growth T_ord_insercao_w.
Proof.
  unfold quadratic_growth.
  unfold big_o.
  exists 1.
  exists 1.
  repeat split; try lia.
  simpl. rewrite Nat.add_0_r.
  induction n.
  - inversion H.
  - inversion H. subst.
    + unfold T_ord_insercao_w. unfold T_insere_w. lia.
    (** Simplifica a expressão fazendo um unfold e depois 
        resumindo o resultado com um fold **)
    + unfold T_ord_insercao_w. fold T_ord_insercao_w.
      rewrite T_insere_w_comp. lia.
Qed.