(*
  Autor: Cenobio Moisés Vázquez Reyes

  This module is part of my thesis degree work named:

  «Mónadas en la programación funcional: una prueba formal de su equivalencia
   con las ternas de Kleisli»
  (Monads in functional programming: a formalized proof of their equivalence
  with Kleisli triples)

  This code is inspired by Matthieu Sozeau's work:
  https://www.irif.fr/~sozeau//repos/coq/cat/
*)


Require Coq.Program.Tactics.

Section Category_Theory.

Generalizable All Variables.

(* Category Definition.

    A category consist of:
      •) An objects class 'obj'.
      •) ∀ a, b ∊ 'obj', an arrows class 'hom(a, b)'. *)
Class Category (obj:Type) (hom:obj->obj->Type) := {
(* •) ∀ a ∊ 'obj', an arrow 'id(a)' ∊ 'hom(a, a)'. *)
  id : forall a:obj, hom a a;
(* •) ∀ a, b, c ∊ 'obj', the arrows composition operator
                            'comp': 'hom(b, c)' → 'hom(a, b)' → 'hom(a, c)' *)
  comp : forall {a b c : obj}, hom b c -> hom a b -> hom a c;
(* That fulfill the following:
  ⋆) 'comp' operator is associative. *)
  asoc : forall {a b c d : obj} (f:hom a b) (g:hom b c) (h:hom c d),
                                         comp h (comp g f) = comp (comp h g) f;
(* ⋆) 'id' is neutral, on the left and on the right, for the 'comp' operator. *)
  id_left  : forall {a b : obj} (f:hom a b), comp (id b) f = f;
  id_right : forall {a b : obj} (f:hom a b), comp f (id a) = f
}.

Infix "°" := comp (at level 40).


  (* CATEGORY EXAMPLES *)

(*
  The Coq Category.

  Objects are Coq types and arrows are λ-functions. Proofing this is trivial.
*)
Program Instance Coq_Category : Category Type (fun (a b:Type) => a->b) := {
  id a       := fun x:a => x;
  comp a b c := fun (g:b->c) (f:a->b) => fun x:a => g (f x)
}.


(*
  A monoid is a triple (M, •, e) where •:MxM→M is an associative operator
  and 'e' is neutral for •.
*)
Class Monoid (M:Type) (dot:M->M->M) (e:M) := {
  asocc   : forall x y z : M, dot x (dot y z) = dot (dot x y) z;
  e_left  : forall x, dot e x = x;
  e_right : forall x, dot x e = x
}.

(* Singleton type 'P' *)
Inductive P:Type := Point.

(*
  Monoid as a one-object category.

  This category has only one object (the type 'P'). An arrow in this
  category is a monoid element. Neutral element in the monoid is the
  identity arrow on this category. To compose arrows is to compose elements
  by using the monoid operation. The proof is completed by the monoid axioms.
*)
Program Instance Monoid_Category `{Mon:Monoid M dot e}:
  Category P (fun _ _ => M) := {
  id   := fun _ => e;
  comp := fun _ _ _ => dot
}.
Next Obligation.
apply asocc.
Qed.

Next Obligation.
apply e_left.
Qed.

Next Obligation.
apply e_right.
Qed.


(*
  Functor Definition.
  Intuitively, given two categorys C and D, a functor from C to D is an arrow
  that maps C-objects to D-objects, and C-arrows to D-arrows. In a formal way,
  a functor from C to D consist of:
   i) A function of classes Fobj:objC → objD.
   ii) ∀ a, b ∊ objC, a function of classes F:Hom(a,b) → Hom(Fobj(a), Fobj(b)).
*)
Class Functor `{C:Category objC homC,
                D:Category objD homD}
(Fobj:objC->objD) (F:forall {a b : objC}, homC a b->homD (Fobj a) (Fobj b)) := {
(* That fulfill the following:
   •) F preserves identities. *)
  preserv_id   : forall a:objC, F (id a) = id (Fobj a);
(* •) F preserves arrows composition. *)
  preserv_comp : forall {a b c : objC} (f:homC a b) (g:homC b c),
                                                          F (g°f) = (F g)°(F f)
}.


(* Identity Functor. *)
Definition functId `(C:Category obj hom):
  Functor (fun x:obj => x) (fun {a b : obj} (f:hom a b) => f).
Proof.
split; trivial.
Qed.


(* Functors Composition. *)
Definition FunctComp
  `{C:Category objC homC,
    D:Category objD homD,
    E:Category objE homE}
  `(Gfunct: ! Functor (Gobj:objD->objE) G,
    Ffunct: ! Functor (Fobj:objC->objD) F):
  Functor (fun x:objC => Gobj (Fobj x))
          (fun {a b : objC} (f:homC a b) => G (Fobj a) (Fobj b) (F a b f)).
Proof.
split; intros.
rewrite preserv_id; apply preserv_id.
rewrite preserv_comp; apply preserv_comp.
Qed.

Infix "●" := FunctComp (at level 40).

(*
  Natural Transformation Definition.
  While functors are arrows between categories, natural transformations are
  arrows between functors.
  Given two functors F₁, F₂ : C → D, a natural transformation F₁⇒F₂ is, for each
  x ∊ Obj(C), to give an arrow η(x) : Fobj(x) → Gobj(x).
*)
Class NatTransf `{C:Category objC homC, D:Category objD homD}
                `(F1: ! Functor (Fobj:objC->objD) F,
                  F2: ! Functor (Gobj:objC->objD) G)
                 (η:forall x:objC, homD (Fobj x) (Gobj x)) := {
(* That fulfill the following:, for each f:a → b,

             F(f)
    F(a) ------------> F(b)
     |                  |
     |                  |
     |η(a)              |η(b)
     |                  |
     |                  |
     v       G(f)       v
    G(a) ------------> G(b)
*)
  η_law : forall {a b : objC} (f : homC a b), (G a b f)°(η a) = (η b)°(F a b f)
}.


(*
  Monad Definition.
 “A monad is just a monoid in the category of endofunctors, what’s the problem?”
  ̣─James Iry

  The term 'monad' was introduced by Mac Lane on 1971. Eugenio Moggi used monads
  to give semantics to functional programming languages. After, Phillip Wadler
  introduced monads on the functional programming following the Moggi's work.

  A monad (T, η, μ) over a category C consist of:
  •) A functor T:C → C.
  •) A natural transformation η: IdC ⇒ T.
  •) A natural transformation μ: T² ⇒ T.
*)
Class Monad `{C:Category obj hom}
            `(TFunct: ! Functor (Tobj:obj->obj) T,
              η_NT: ! NatTransf (functId C) TFunct η,
              μ_NT: ! NatTransf (TFunct●TFunct) TFunct μ) := {
(* That fulfill the following:
   μ is 'asociative':

           T(μ)
    T³ -----------> T²
    |               |
    |               |
    |μ(T)           |μ
    |               |
    |               |
    v       μ       v
    T² -----------> T
*)
  μ_asoc : forall x:obj,
                  (μ x)°(T (Tobj (Tobj x)) (Tobj x) (μ x)) = (μ x)°(μ (Tobj x));
(* η is 'unit' for μ

       η(T)          T(η)
   T --------> T² <-------- T
   |           |            |
   |           |            |
   |Id(T)      |μ           |Id(T)
   |           |            |
   |           |            |
   v           v            v
   T ========= T ========== T
*)
  η_left  : forall x:obj, (μ x)°(η (Tobj x)) = id (Tobj x);
  η_right : forall x:obj, (μ x)°(T x (Tobj x) (η x)) = id (Tobj x)
}.


(*
 “Kleisli triples are just an alternative description for monads.”
  ─Eugenio Moggi

  A Kleisli triple (T, η, _★) over a category C consist of:
  •) A classes function T:ObjC → ObjC.
  •) For each a ∊ Obj(C), an arrow η(a): a → T(a).
  •) For each f:a → T(b), an arrow f★:T(a) → T(b).
*)
Class KleisliTriple `{C:Category obj hom}
                     (Tobj:obj->obj)
                     (η:forall a:obj, hom a (Tobj a)) := {
  ext  : forall {a b : obj}, hom a (Tobj b) -> hom (Tobj a) (Tobj b);
(* That fulfill the following:
   •) η(a)★ = id(T(a)) *)
  ki   : forall a:obj, ext (η a) = id (Tobj a);
(* •) f★ ° η(a) = f *)
  kii  : forall {a b : obj} (f:hom a (Tobj b)), (ext f)°(η a) = f;
(* g★ ° f★ = (g★ ° f)★ *)
  kiii : forall {a b c : obj} (f:hom a (Tobj b)) (g:hom b (Tobj c)),
                                              (ext g)°(ext f) = ext ((ext g)°f)
}.

Notation "f ★" := (ext f) (at level 40).


(*
  Lemma: A Kleisli triple (T, η, _★) is a functor, where T(f) = (η(b)°f)★.
*)
Lemma KleisliTriple_is_Functor `{C:Category obj hom}
                               `(KT: ! KleisliTriple Tobj η):
                     Functor Tobj (fun a b (f:hom a b) => (η b)°f ★).
Proof.
split; intros.
(* T preserves identities. *)
rewrite id_right.
rewrite ki; trivial.
(* T preserves compositions. *)
rewrite asoc.
pattern ((η c)°g) at 1;
         rewrite <- (kii ((η c)°g)).
rewrite <- asoc.
rewrite <- kiii; trivial.
Qed.

(*
  Lemma: A Kleisli triple (T, η, _★) is a natural transformation η: IdC ⇒ T,
         where T is the previous functor.
*)
Lemma KleisliTriple_is_η_NT `{C:Category obj hom}
                            `(KT: ! KleisliTriple Tobj η):
    NatTransf (functId C) (KleisliTriple_is_Functor KT) η.
Proof.
split; intros.
(* For each f:a → b,

             f
     a -------------> b
     |                |
     |                |
     |η(a)            |η(b)
     |                |
     |                |
     v       T(f)     v
    T(a) ----------> T(b)
*)
rewrite kii; trivial.
Qed.

(*
  Lemma: A Kleisli triple (T, η, _★) is a natural transformation μ: T² ⇒ T,
         where T is the same previous functor and μ(x) = id(T(x))★.
*)
Lemma KleisliTriple_es_μ_NT `{C:Category obj hom}
                            `(KT: ! KleisliTriple Tobj η):
  NatTransf ((KleisliTriple_is_Functor KT)●(KleisliTriple_is_Functor KT))
            (KleisliTriple_is_Functor KT)
            (fun x:obj => id (Tobj x) ★).
Proof.
split; intros.
(*
  For each f:a → b,

            T²(f)
   T²(a) ----------> T²(b)
    |                 |
    |                 |
    |μ(a)             |μ(b)
    |                 |
    |                 |
    v       T(f)      v
   T(a) -----------> T(b)
*)
rewrite kiii.
rewrite id_right.
pattern (((η b)°f)★) at 1; rewrite <- id_left.
pattern (id (Tobj b)) at 1; rewrite <- kii.
rewrite <- asoc.
rewrite <- kiii; trivial.
Qed.


(*
  Theorem: Any Kleisli triple is a monad.
  The proof is directly obtained from the previous lemmas.
*)
Theorem KleisliTriple_is_Monad `{C:Category obj hom}
                               `(KT: ! KleisliTriple Tobj η):
  Monad (KleisliTriple_is_Functor KT)
        (KleisliTriple_is_η_NT KT)
        (KleisliTriple_es_μ_NT KT).
Proof.
split; intros.
(* μ is asociative. *)
rewrite kiii.
rewrite asoc; rewrite (kii (id (Tobj x))).
rewrite id_left.
pattern ((id (Tobj x))★) at 1;
       rewrite <- (id_right ((id (Tobj x))★)).
rewrite <- kiii; trivial.
(* η is left unit. *)
rewrite kii; trivial.
(* η is right unit. *)
rewrite kiii.
rewrite asoc; rewrite kii.
rewrite id_left.
rewrite <- ki; trivial.
Qed.

(*
  Theorem: Any monad is a Kleisli triple, where f★ = μ(b)°T(f).
  The proof only use the monad definition.
*)
Program Instance Monad_is_KleisliTriple
  `{C:Category obj hom,
    TFunct: ! Functor (Tobj:obj->obj) T,
    η_NT: ! NatTransf (functId C) TFunct η,
    μ_NT: ! NatTransf (TFunct●TFunct) TFunct μ}
  `(Mon: ! Monad TFunct η_NT μ_NT) : KleisliTriple Tobj η := {
    ext a b := fun (f:hom a (Tobj b)) => (μ b)°(T a (Tobj b) f)
}.
(* ki *)
Next Obligation.
Proof.
intros.
destruct Mon;
  rewrite η_right0;
  trivial.
Qed.
(* kii *)
Next Obligation.
Proof.
intros.
rewrite <- asoc;
  destruct η_NT;
  rewrite η_law0.
rewrite asoc;
  destruct Mon;
  rewrite η_left0.
rewrite id_left; trivial.
Qed.
(* kiii *)
Next Obligation.
Proof.
intros.
rewrite preserv_comp; rewrite preserv_comp.
rewrite (asoc (T a (Tobj b) f) (T (Tobj (Tobj c)) (Tobj c) (μ c)° T (Tobj b)
                                       (Tobj (Tobj c)) (T b (Tobj c) g)) (μ c));
        rewrite (asoc (T (Tobj b) (Tobj (Tobj c)) (T b (Tobj c) g))
                                      (T (Tobj (Tobj c)) (Tobj c) (μ c)) (μ c)).
destruct Mon;
  rewrite μ_asoc0;
  rewrite <- (asoc (T a (Tobj b) f) (T (Tobj b) (Tobj (Tobj c))
                                          (T b (Tobj c) g)) (μ c ° μ (Tobj c)));
  rewrite (asoc (T a (Tobj b) f) (T (Tobj b) (Tobj (Tobj c))
                                          (T b (Tobj c) g)) (μ c ° μ (Tobj c)));
  rewrite <- (asoc (T (Tobj b) (Tobj (Tobj c)) (T b (Tobj c) g))
                                                            (μ (Tobj c)) (μ c)).
destruct μ_NT;
  rewrite <- η_law0.
rewrite <- asoc;
  rewrite asoc;
  rewrite asoc;
  rewrite asoc;
  trivial.
Qed.

End Category_Theory.
