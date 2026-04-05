// ===================
// ----- DAFNY -------
// ===================

// ------------------------------------------------------------------------
// Dafny je imperativno, funkcijsko, objektno usmerjeni jezik.
// Namenjen je dokazovanju pravilnosti programov.
// Ustvaril ga je Rustan Leino iz Microsoft Research.
// Dafny se prevaja v C#, JS, Java, Go in Python.
// Podobni jeziki: Viper, Why3, SPARK.
// IronFleet: Proving Safety and Liveness of Practical Distributed Systems
// Dokumentacija: https://dafny.org/latest/DafnyRef/DafnyRef
// Plonk: https://dafny.org/latest/Dafny-cheat-sheet.pdf
// ------------------------------------------------------------------------

// ------------------------------------------------------------------------
//          UPORABNE BLIŽNJICE / POSTOPKI
// ----------------------------------------------------------------------------
// Dafny crkne:
//   1. ctrl-shift-p restart dafny server
//   2. skoči na drug zavihek pa nazaj ALI ctrl-shift-p reload window
//
// Večvrstično komentiranje/dekomentiranje:
//   1. izberi vrstice s kurzorjem
//      (ni treba označiti v celoti le da je kaj označeno na željenih vrstica)
//   2. ctrl-shift-7
// ----------------------------------------------------------------------------

// Primer: Fibbonacci
function Fib(a:nat) : nat {
  if a == 0 then
    1
  else if a == 1 then
    1
  else
    Fib(a-1) + Fib(a-2)
}

// Primer: tipi, spremenljivke, logični izrazi
function Test(x:nat, y:real) : bool {
  var z : int := -4;
  if (0 <= x <= 4 && y != 0.4) || (z >= 0 ==> x == z) then
    true
  else
    true
}

// Primer: Drevo in njegova velikost
datatype Tree<T> = Leaf(T) | Node(left: Tree<T>, right: Tree<T>)

function Size<T>(tree : Tree<T>) : nat {
  match tree
  case Leaf(_) => 1
  case Node(t1,t2) => 1 + Size(t1) + Size(t2)
}

// Primer: Mirror
function Mirror(tree : Tree) : Tree {
  if tree.Leaf? then
    tree
  else
    var mirr_x := Mirror(tree.left);
    var mirr_y := Mirror(tree.right);
    Node(mirr_y, mirr_x)
}

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

// Primer
function RisingFactorial(m:nat, n:nat) : nat
  decreases n
{
  if n == 0 then
    1
  else
    m * RisingFactorial(m+1,n-1)
}

lemma OKRisingFactorial() {
  assert RisingFactorial(1,4) == 1 * 2 * 3 * 4;
  assert RisingFactorial(3,2) == 3 * 4;
  assert RisingFactorial(2,3) == 2 * 3 * 4;
  assert RisingFactorial(3,3) == 3 * 4 * 5;
  assert RisingFactorial(0,3) == 0;
}

// Primer
function Fun(x:int) : int
  decreases x+5
{
  if x <= -5 then
    x
  else
    Fun(x-34)
}

// ------------------------------------------------------------------------
// Dobre urejenosti po tipih:
//  | tip X, y            | X ≻ y (“X se zmanjša na y”)                 |
//  +---------------------+---------------------------------------------+
//  | bool                | X && !y                                     |
//  | int                 | y < X && 0 <= X                             |
//  | real                | y <= X - 1.0 && 0.0 <= X                    |
//  | set<T>              | y je prava podmnožica X                     |
//  | seq<T>              | y je pravi prefix X                         |
//  | induktivni tipi     | y je strukturalno vsebovan v X              |
//
// Dafny poskuša sam dokazati ustavitev z leksikografsko urejenostjo.
// ------------------------------------------------------------------------

// ----------
//   Naloge
// ----------

// Naloga: dopolni funkcijo, da bo veljala spodnja lema
function Length(l : List) : nat

// lemma LengthOK() {
//   assert Length<int>(Nil) == 0;
//   assert Length(Cons(1,Nil)) == 1;
//   assert Length(Cons(1,Cons(2,Nil))) == 2;
// }

// Naloga: dopolni funkcijo, da bo veljala spodnja lema
function Append(l1 : List, l2 : List) : List

// lemma AppendOK() {
//   assert Append<int>(Nil,Nil) == Nil;
//   assert Append(Cons(2,Nil),Nil) == Cons(2,Nil);
//   assert Append(Nil,Cons(2,Nil)) == Cons(2,Nil);
//   assert Append(Cons(2,Nil),Cons(3,Nil)) == Cons(2,Cons(3,Nil));
// }

// Naloga: pravilno zapolni, da bo dokazana ustavitev
// function M(x: int, b: bool): int
// {
//   if b then x else M(x + 25, true)
// }

// Naloga: pravilno zapolni, da bo dokazana ustavitev
// function L(x: int): int
// {
//   if x < 100 then
//     L(x + 1) + 10
//   else
//     x
// }

// -------------- DODATNE NALOGE ----------------

// Naloga: dopolni funkcijo, da bo veljala spodnja lema
function OrderedList(xs: List<int>) : bool

// lemma OrderedListOK() {
//   assert OrderedList(Nil);
//   assert OrderedList(Cons(2,Nil));
//   assert OrderedList(Cons(1,Cons(2,Nil)));
//   assert OrderedList(Cons(1,Cons(2,Cons(2,Cons(4,Nil)))));
// }

// Naloga: dopolni funkcijo, da bo veljala spodnja lema
function ProjectElement(xs: List<int>, p: int): List<int> 

// lemma ProjectElementOK() {
//   var a := Cons(1,Cons(3,Cons(3,Cons(4,Cons(3,Cons(4,Nil))))));
//   assert ProjectElement(a,1) == Cons(1,Nil);
//   assert ProjectElement(a,2) == Nil;
//   assert ProjectElement(a,3) == Cons(3,Cons(3,Cons(3,Nil)));
//   assert ProjectElement(a,4) == Cons(4,Cons(4,Nil));
// }

// Naloga: pravilno zapolni, da bo dokazana ustavitev
// function RevAck(m: nat, n: nat): nat
// {
//   if n == 0 then
//     m + 1
//   else if m == 0 then
//     RevAck(1,n - 1)
//   else
//     RevAck(RevAck(m - 1,n),n - 1)
// }

// Naloga: pravilno zapolni, da bo dokazana ustavitev
// function Gcd(x:nat,y:nat) : nat
// {
//   if y == 0 then
//     x
//   else
//     Gcd(y, x%y)
// }

// Naloga: pravilno zapolni, da bo dokazana ustavitev
// function N(x: int, y: int, b: bool): int
// {
//   if x <= 0 || y <= 0 then
//     x + y
//   else if b then
//     N(x, y + 3, !b)
//   else
//     N(x - 1, y, true)
// }

// =============
//  Dokazovanje
// =============

// Primer: soda števila
function Even_long(x:int) : bool {
  x % 2 == 0
}

// lepši zapis
predicate Even(x:int) {
  x % 2 == 0
}

// še dva načina formalizacije
ghost predicate Even1(x:int) {
  exists xf:int :: 2 * xf == x
}

// -------------------------------------------
// Kvantifikatorji:
//   exists x:T :: P(X)
//   exists x1:T1, ..., xn:Tn :: P(x1,...,xn)
//
//   forall x:T :: P(X)
//   forall x1:T1, ..., xn:Tn :: P(x1,...,xn)
// -------------------------------------------

predicate Even2(x:nat) {
  x == 0 || (x>=2 && Even2(x-2))
}

ghost predicate IsReflexive<T(!new)>(p:(T,T)->bool) {
  forall x:T :: p(x,x)
}

// Primer: prvi dokaz
lemma Even1_plus_Even1_is_Even1(x:int, y:int)
  requires Even1(x) // exists xf:int :: 2 * xf == x
  requires Even1(y)
  ensures Even1(x+y)
{
  var xf : int :| 2 * xf == x;
  var yf : int :| 2 * yf == y;

  var z := xf + yf;
  assert 2 * z == x + y;
  assert exists z : int :: 2 * z == x + y;
}

lemma Even1_times_Even1_is_Even1(x:int, y:int)
  requires Even1(x)
  requires Even1(y)
  ensures Even1(x*y)
{
  var xf : int :| 2 * xf == x;
  var yf : int :| 2 * yf == y;
  calc {
    x*y;
    (2 * xf) * y;
    2 * (xf * y);
  }
}

lemma Even1_is_Even(x:int)
  requires Even1(x)
  ensures Even(x)
{}

// Primer:
lemma {:induction false} Mirror_mirror_is_id(tree : Tree)
  ensures Mirror(Mirror(tree)) == tree
{
  match tree
  case Leaf(a) => assert Mirror(Mirror(tree)) == tree;
  case Node (t1, t2) =>
    calc {
      Mirror(Mirror(Node (t1, t2)));
    ==
      Mirror(Node(Mirror(t2), Mirror(t1)));
    ==
      Node(Mirror(Mirror(t1)), Mirror(Mirror(t2)));
    == {Mirror_mirror_is_id(t1); Mirror_mirror_is_id(t2);}
      Node(t1, t2);
    }
}

// ----------
//   Naloge
// ----------

// Naloga: dokaži veljavnost spodnje leme
lemma Even1_pm_2_is_Even1(x:int)
  requires Even1(x)
  ensures Even1(x-2)
  ensures Even1(x+2)

// Naloga: dokaži veljavnost spodnje leme
lemma Even_is_Even1(x:int)
  requires Even(x)
  ensures Even1(x)

// Naloga: dokaži veljavnost spodnje leme
lemma {:induction false} Append_Nil_id(a:List)
  ensures Append(a,Nil) == a

// Naloga: dokaži veljavnost spodnje leme
lemma {:induction false} Size_mirror_is_Size(tree : Tree)
  ensures Size(Mirror(tree)) == Size(tree)

// --------------- DODATNE NALOGE ---------------------

// Naloga: dokaži veljavnost spodnje leme
lemma {:induction false} LengthAppend(l1:List, l2:List)
  ensures Length(l1) + Length(l2) == Length(Append(l1,l2))

// Naloga: dokaži veljavnost spodnje leme
lemma {:induction false} Append_associativity(l1:List, l2:List, l3:List)
  ensures Append(l1,Append(l2,l3)) == Append(Append(l1,l2),l3)

// Naloga: dokaži veljavnost spodnje leme
lemma {:induction false} ProjectElement_shorter(a:List<int>, e:int)
ensures Length(ProjectElement(a,e)) <= Length(a)

// Naloga: dokaži veljavnost spodnje leme (priporočena uporaba dodatnih lem in predikatov)
lemma ProjectElement_OrderedList(a:List<int>, e:int)
  ensures OrderedList(ProjectElement(a,e))

// ============
//  SORTIRANJE
// ============

// ----------------
//  Insertion sort
// ----------------

function Ordered(xs: List<int>) : bool {
  match xs
  case Nil => true
  case Cons(x, Nil) => true
  case Cons(x, Cons(y, _)) => x <= y && Ordered(xs.tail)
}

function InsertionSort(xs: List<int>): List<int> {
  match xs
  case Nil => Nil
  case Cons(x, tail) =>
    Insert(x, InsertionSort(tail))
}

function Insert(y: int, xs: List<int>): List<int> {
  match xs
  case Nil => Cons(y, Nil)
  case Cons(x, tail) =>
    if y < x then
      Cons(y, xs)
    else
      Cons(x, Insert(y, tail))
}

lemma InsertionSortOrdered(xs: List<int>)
  ensures Ordered(InsertionSort(xs))
{
  match xs
  case Nil =>
  case Cons(x, tail) =>
    InsertionSortOrdered(tail);
    InsertOrdered(x, InsertionSort(tail));
}

lemma InsertOrdered(y: int, xs: List<int>)
  requires Ordered(xs)
  ensures Ordered(Insert(y, xs))
{}

function Project(xs: List<int>, p: int): List<int> {
  match xs
  case Nil => Nil
  case Cons(x, tail) =>
    if x == p then
      Cons(x, Project(tail, p))
    else
      Project(tail, p)
}

lemma InsertionSortSameElements(xs: List<int>, p: int)
  ensures Project(xs, p) == Project(InsertionSort(xs), p)
{
  match xs
  case Nil =>
  case Cons(x, tail) =>
    InsertSameElements(x, InsertionSort(tail), p);
}

lemma InsertSameElements(y: int, xs: List<int>, p: int)
  ensures Project(Cons(y, xs), p) == Project(Insert(y, xs), p)
{}

// --------------------
// Naloge: Merge sort
// --------------------

function MergeSort(xs: List<int>): List<int> {
  MergeSortAux(xs, Length(xs))
}

// Naloga: dopolni funkcijo, da bo veljala spodnja lema
function MergeSortAux(xs: List<int>, len: nat): List<int>
  decreases len
  requires len == Length(xs)

// lemma MergeSortAuxOK() {
//   assert MergeSortAux(Nil,0) == Nil;
//   assert MergeSortAux(Cons(1,Nil),1) == Cons(1,Nil);
//   var a := Cons(3,Cons(1,Cons(5,Cons(2,Cons(4,Nil)))));
//   assert MergeSortAux(a,Length(a))
//          == Cons(1,Cons(2,Cons(3,Cons(4,Cons(5,Nil)))));
// }


// Naloga: dopolni funkcijo, da bo veljala spodnja lema
function Split(xs: List, n: nat): (List, List)
  requires n <= Length(xs)
  ensures var (left, right) := Split(xs, n);
          Length(left) == n &&
          Length(right) == Length(xs) - n &&
          Append(left, right) == xs

// lemma SplitOK() {
//   var a := Cons(1,Cons(2,Cons(3,Cons(4,Cons(5,Nil)))));
//   assert Split(a,0) == (Nil,a);
//   assert Split(a,1) == (Cons(1,Nil),a.tail);
//   assert Split(a,2) == (Cons(1,Cons(2,Nil)),Cons(3,Cons(4,Cons(5,Nil))));
//   assert Split(a,5) == (a,Nil);
// }


// Naloga: dopolni funkcijo, da bo veljala spodnja lema
function Merge(xs: List<int>, ys: List<int>): List<int>

// lemma MergeOK() {
//   var a := Cons(1,Cons(3,Nil));
//   var b := Cons(2,Cons(4,Nil));
//   assert Merge(Nil,Nil) == Nil;
//   assert Merge(Cons(1,Nil),Nil) == Cons(1,Nil);
//   assert Merge(Nil,Cons(1,Nil)) == Cons(1,Nil);
//   assert Merge(a,a) == Cons(1,Cons(1,Cons(3,Cons(3,Nil))));
//   assert Merge(a,b) == Cons(1,Cons(2,Cons(3,Cons(4,Nil))));
// }


lemma MergeSortOrdered(xs: List<int>)
  ensures Ordered(MergeSort(xs))
{
  MergeSortAuxOrdered(xs, Length(xs));
}


// Naloga: dopolni funkcijo, da bo veljala spodnja lema
lemma MergeOrdered(xs: List<int>, ys: List<int>)
  requires Ordered(xs) && Ordered(ys)
  ensures Ordered(Merge(xs, ys))

// Naloga: dopolni funkcijo, da bo veljala spodnja lema
lemma MergeSortAuxOrdered(xs: List<int>, len: nat)
  requires len == Length(xs)
  ensures Ordered(MergeSortAux(xs, len))
  decreases len

