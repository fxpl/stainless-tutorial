import stainless.lang.*
import stainless.collection.*
import stainless.annotation.*
 

// The definition of List and its operations can be found here:
// https://github.com/epfl-lara/stainless/blob/64a09dbc58d0a41e49e7dffbbd44b234c4d2da59/frontends/library/stainless/collection/List.scala
// You should not need them, but you can find some lemmas on List here:
// https://github.com/epfl-lara/stainless/blob/64a09dbc58d0a41e49e7dffbbd44b234c4d2da59/frontends/library/stainless/collection/ListSpecs.scala

/**
  * Determines whether `l1` is a sublist of `l2`.  
  * A list `l1` is a sublist of `l2` if and only if all elements of `l1` appear in `l2` in the same order, though not necessarily consecutively.  
  *  
  * For better intuition, try running the example below.  
  */
def sublist[T](l1: List[T], l2: List[T]): Boolean = {
  (l1, l2) match {
    case (Nil(), _)                 => true
    case (_, Nil())                 => false
    case (Cons(x, xs), Cons(y, ys)) => (x == y && sublist(xs, ys)) || sublist(l1, ys)
  }
}

@extern
@main
def main(): Unit = {

  // Nicely displays whether l1 is a sublist of l2
  def example(l1: List[Int], l2: List[Int]): Unit = {
    println(s"${l1.toScala.mkString("<", ",", ">")} ${if sublist(l1, l2) then '⊑' else '⋢'} ${l2.toScala.mkString("<", ",", ">")}")
  }

  example(List(0, 2), List(0, 1, 2))
  example(List(0, 0, 2), List(0, 2))
  example(List(1, 0), List(0, 0, 1))
  example(List(10, 5, 25), List(70, 10, 11, 8, 5, 25, 22))
  example(List(25, 11, 53, 38), List(15, 25, 11, 8, 53, 22, 38))
}

/**
  * Your task is to formally prove some properties of the sublist relation.
  * 
  * Tips:
  * - Try to understand how you would prove these properties using paper and pencil, and use examples to build intuition.
  * - Be prepared to use induction frequently in your proofs.
  * - While not strictly necessary, you may define new lemmas if they help (but you must prove them correct as well!).
  * - The last two theorems may appear similar, but their proofs differ significantly — can you see why?
  * 
  * Good luck!
  */
object SublistSpecs {
 
  def reflexivity[T](l: List[T]): Unit = {
    /* TODO: Prove me */
  }.ensuring(_ =>
    sublist(l, l)
  )
 
  def leftTail[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && sublist(l1, l2))

    /* TODO: Prove me */
  }.ensuring(_ =>
    sublist(l1.tail, l2)
  )
 
  def tails[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && !l2.isEmpty && l1.head == l2.head && sublist(l1, l2))
 
    /* TODO: Prove me */
  }.ensuring(_ =>
    sublist(l1.tail, l2.tail)
  )
 
  /* forall l1 l2 l3, sublist(l1, l2) /\ sublist(l2, l3) ==> sublist(l1, l3) */
  def transitivity[T](l1: List[T], l2: List[T], l3: List[T]): Unit = {
    require(sublist(l1, l2) && sublist(l2, l3))
 
    /* TODO: Prove me */
  }.ensuring(_ =>
    sublist(l1, l3)
  )
 
  def lengthHomomorphism[T](l1: List[T], l2: List[T]): Unit = {
    require(sublist(l1, l2))
 
    /* TODO: Prove me */
  }.ensuring(_ =>
    l1.length <= l2.length
  )
 
  def biggerSublist[T](l1: List[T], l2: List[T]): Unit = {
    require(sublist(l1, l2) && l1.length >= l2.length)
 
    /* TODO: Prove me */
  }.ensuring(_ =>
    l1 == l2
  )
 
  def antisymmetry[T](l1: List[T], l2: List[T]): Unit = {
    require(sublist(l1, l2) && sublist(l2, l1))
 
    /* TODO: Prove me */
  }.ensuring(_ =>
    l1 == l2
  )

  // ++ is the list concatenation operator.
  // It is defined here: 
  // https://github.com/epfl-lara/stainless/blob/64a09dbc58d0a41e49e7dffbbd44b234c4d2da59/frontends/library/stainless/collection/List.scala#L46

  def extendRight[T](l1: List[T], l2: List[T]): Unit = {
    /* TODO: Prove me */
  }.ensuring(_ => 
    sublist(l1, l1 ++ l2)  
  )

  def extendLeft[T](l1: List[T], l2: List[T]): Unit = {
    /* TODO: Prove me */
  }.ensuring(_ => 
    sublist(l2, l1 ++ l2)  
  )

  def prepend[T](l: List[T], l1: List[T], l2: List[T]): Unit = {
    require(sublist(l1, l2))

    /* TODO: Prove me */
  }.ensuring(_ =>
    sublist(l ++ l1, l ++ l2)  
  )

  def append[T](l1: List[T], l2: List[T], l: List[T]): Unit = {
    require(sublist(l1, l2))

    /* TODO: Prove me */
  }.ensuring(_ =>
    sublist(l1 ++ l, l2 ++ l)  
  )
}
