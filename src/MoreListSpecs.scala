package unionfind
package morelistspecs

import stainless.lang._
import stainless.proof._
import stainless.collection.{List, ListSpecs, Nil, Cons}
import stainless.annotation._

object MoreListSpecs {
  // =========================
  // ===== Append lemmas =====
  // =========================

  /** ```
    * empty == Nil() -> (empty :+ value).contains(value) && (empty :+ value).size == 1
    * ```
    */
  def appendToNil[T](empty: List[T], value: T): Unit = {
    require(empty == Nil[T]())
  }.ensuring(_ =>
    (empty :+ value).contains(value) && (empty :+ value).size == 1
  )

  /** ```
    * Nil() :+ value == Cons(value, Nil())
    * ```
    */
  def snocNil[T](value: T): Unit = {}.ensuring(_ =>
    Nil[T]() :+ value == Cons(value, Nil[T]())
  )

  /** ```
    * l.size == 1 -> l == Cons(value, Nil())
    * ```
    */
  def singletonList[T](l: List[T], value: T): Unit = {
    require(l.contains(value))
    require(l.size == 1)
  }.ensuring(_ => l == Cons(value, Nil[T]()))

  /** ```
    * (l :+ elem)(l.size) == elem
    * ```
    */
  def appendedElementIsAtIndexOldSize[T](l: List[T], elem: T): Unit = {
    decreases(l)
    l match {
      case Nil()      =>
      case Cons(h, t) => appendedElementIsAtIndexOldSize(t, elem)
    }
  }.ensuring { _ => (l :+ elem)(l.size) == elem }

  /** ```
    * l.forall(p) && p(elem) ==> (l :+ elem).forall(p)
    * ```
    */
  def snocForallAppend[T](l: List[T], elem: T, p: T => Boolean): Unit = {
    require(l.forall(p) && p(elem))
    decreases(l)
    (l :+ elem, l) match {
      case (Nil(), _)              => ()
      case (Cons(h, Nil()), Nil()) =>
        assert(h == elem)
        assert(p(elem))
      case (Cons(h1, t1), Cons(h2, t2)) =>
        assert(h1 == h2)
        assert(p(h1))
        assert(p(h2))
        snocForallAppend(t2, elem, p)
    }
  }.ensuring { _ => (l :+ elem).forall(p) }

  /** ```
    * 0 <= i < l.size ==> (l :+ n)(i) == l(i)
    * ```
    */
  def appendPreservesIndices[T](l: List[T], n: T, i: BigInt): Unit = {
    require(0 <= i && i < l.size)
    decreases(l)
    (l :+ n, l) match {
      case (Nil(), _)               => ()
      case (Cons(h1, Nil()), Nil()) =>
        assert(h1 == n)
        assert(i < 0)
      case (Cons(h1, t1), Cons(h2, t2)) =>
        assert(h1 == h2)
        if (i == 0) then ()
        else appendPreservesIndices(t2, n, i - 1)
    }
  }.ensuring { _ => (l :+ n)(i) == l(i) }

  /** ```
    * p(n) ==> (l :+ n).filter(p).size == l.filter(p).size + 1
    * ```
    */
  def appendFilterSizeDecreases[T](
      l: List[T],
      n: T,
      p: T => Boolean
  ): Unit = {
    require(p(n))

    l match {
      case Nil()      => ()
      case Cons(h, t) => appendFilterSizeDecreases(t, n, p)
    }
  }.ensuring { _ => (l :+ n).filter(p).size == l.filter(p).size + 1 }

  /** ```
    * !p(n) ==> (l :+ n).filter(p).size == l.filter(p).size
    * ```
    */
  def appendFilterSizePreserved[T](
      l: List[T],
      n: T,
      p: T => Boolean
  ): Unit = {
    require(!p(n))

    l match {
      case Nil()      => ()
      case Cons(h, t) => appendFilterSizePreserved(t, n, p)
    }
  }.ensuring { _ => (l :+ n).filter(p).size == l.filter(p).size }

  // =========================
  // ===== Update lemmas =====
  // =========================

  /** ```
    * l.forall(p) && p(elem) => (l.updated(addr, elem)).forall(p)
    * ```
    */
  def forallUpdate[T](
      l: List[T],
      addr: BigInt,
      elem: T,
      p: T => Boolean
  ): Unit = {
    require(0 <= addr && addr < l.size)
    require(l.forall(p))
    require(p(elem))

    if addr == 0 then ()
    else
      l match {
        case Nil()      => ()
        case Cons(h, t) => forallUpdate(t, addr - 1, elem, p)
      }
  }.ensuring(_ => (l.updated(addr, elem)).forall(p))

  /** ```
    * p(l(index)) && addr != index => p(l.updated(addr, elem)(index))
    * ```
    */
  def predicateIsPreservedOnNonUpdatedElements[T](
      l: List[T],
      addr: BigInt,
      elem: T,
      p: T => Boolean,
      index: BigInt
  ): Unit = {
    require(0 <= addr && addr < l.size)
    require(0 <= index && index < l.size)
    require(p(l(index)))
    require(addr != index)

    l match {
      case Nil()      => ()
      case Cons(h, t) =>
        if addr == 0 then ()
        else if index == 0 then ()
        else
          predicateIsPreservedOnNonUpdatedElements(
            t,
            addr - 1,
            elem,
            p,
            index - 1
          )
    }

  }.ensuring { _ => p(l.updated(addr, elem)(index)) }

  /** ```
    * p(l(i1), l(i2)) && addr != i1 && addr != i2 && i1 != i2
    * [=>] p(l.updated(addr, elem)(i1), l.updated(addr, elem)(i2))
    * ```
    */
  def predicatePreservedOnNonUpdatedPair[T](
      l: List[T],
      i1: BigInt,
      i2: BigInt,
      addr: BigInt,
      elem: T,
      p: (T, T) => Boolean
  ): Unit = {
    require(0 <= addr && addr < l.size)
    require(0 <= i1 && i1 < l.size)
    require(0 <= i2 && i2 < l.size)
    require(addr != i1 && addr != i2 && i1 != i2)
    require(p(l(i1), l(i2)))

    def p1 = (t1: T) => (t2: T) => p(t1, t2)
    def p2 = (t2: T) => (t1: T) => p(t1, t2)

    l match {
      case Nil()      => ()
      case Cons(h, t) =>
        if addr == 0 then ()
        else if i1 == 0 || i2 == 0 then
          if i1 < i2 then
            predicateIsPreservedOnNonUpdatedElements(l, addr, elem, p1(h), i2)
          else
            predicateIsPreservedOnNonUpdatedElements(l, addr, elem, p2(h), i1)
        else
          predicatePreservedOnNonUpdatedPair(
            t,
            i1 - 1,
            i2 - 1,
            addr - 1,
            elem,
            p
          )
    }
  }.ensuring { _ => p(l.updated(addr, elem)(i1), l.updated(addr, elem)(i2)) }

  /** ```
    * p(elem) || !p(l(addr)) ==> l.updated(addr, elem).filter(p).size >= l.filter(p).size
    * ```
    */
  def updatedFilterSizeIncreases[T](
      l: List[T],
      addr: BigInt,
      elem: T,
      p: T => Boolean
  ): Unit = {
    require(0 <= addr && addr < l.size)
    require(p(elem) || !p(l(addr)))

    l match {
      case Nil()      => ()
      case Cons(h, t) =>
        if addr == 0 then ()
        else updatedFilterSizeIncreases(t, addr - 1, elem, p)
    }
  }.ensuring(_ => l.updated(addr, elem).filter(p).size >= l.filter(p).size)

  /** ```
    * !p(l(addr)) && p(elem) ==> l.updated(addr, elem).filter(p).size == l.filter(p).size + 1
    * ```
    */
  def updatedFilterSizeIncreases2[T](
      l: List[T],
      addr: BigInt,
      elem: T,
      p: T => Boolean
  ): Unit = {
    require(0 <= addr && addr < l.size)
    require(!p(l(addr)))
    require(p(elem))

    l match {
      case Nil()      => ()
      case Cons(h, t) =>
        if addr == 0 then ()
        else updatedFilterSizeIncreases2(t, addr - 1, elem, p)
    }
  }.ensuring(_ => l.updated(addr, elem).filter(p).size == l.filter(p).size + 1)

  /** ```
    * 0 <= addr < l.size && 0 <= i < l.size && addr != i
    * [=>] l.updated(addr, elem)(i) == l(i)
    * ```
    */
  def updatePreservesIndices[T](
      l: List[T],
      addr: BigInt,
      elem: T,
      i: BigInt
  ): Unit = {
    require(0 <= addr && addr < l.size)
    require(0 <= i && i < l.size)
    require(addr != i)

    l match {
      case Nil()      => ()
      case Cons(h, t) =>
        if addr == 0 then ()
        else if i == 0 then ()
        else updatePreservesIndices(t, addr - 1, elem, i - 1)
    }
  }.ensuring { _ => l.updated(addr, elem)(i) == l(i) }

  /** ```
    * l.updated(i1, e1).updated(i2, e2) == l.updated(i2, e2).updated(i1, e1)
    * ```
    */
  def updateOrderDoesNotMatter[T](
      l: List[T],
      i1: BigInt,
      e1: T,
      i2: BigInt,
      e2: T
  ): Unit = {
    require(0 <= i1 && i1 < l.size)
    require(0 <= i2 && i2 < l.size)
    require(i1 != i2)

    l match {
      case Nil()      => ()
      case Cons(h, t) =>
        if i1 == 0 || i2 == 0 then ()
        else updateOrderDoesNotMatter(t, i1 - 1, e1, i2 - 1, e2)
    }
  }.ensuring { _ =>
    l.updated(i1, e1).updated(i2, e2) == l.updated(i2, e2).updated(i1, e1)
  }

  // ========================
  // ===== Slice lemmas =====
  // ========================

  /** ```
    * l.slice(from, until) == Cons(l(from), l.slice(from + 1, until))
    * ```
    */
  def sliceCons[T](l: List[T], from: BigInt, until: BigInt): Unit = {
    require(0 <= from && from < l.size && 0 <= until && until <= l.size)
    require(from < until)
    l match {
      case Nil()      => ()
      case Cons(h, t) =>
        if (from == 0) then ()
        else sliceCons(t, from - 1, until - 1)
    }
  }.ensuring(_ =>
    l.slice(from, until) == Cons(l(from), l.slice(from + 1, until))
  )

  /** ```
    * l1(index - from) == l2(index)
    * ```
    */
  def sliceAtIndex[T](
      l1: List[T],
      l2: List[T],
      from: BigInt,
      until: BigInt,
      index: BigInt
  ): Unit = {
    require(0 <= from && from < l2.size)
    require(0 <= until && until <= l2.size)
    require(from <= until)
    require(l1 == l2.slice(from, until))
    require(from <= index && index < until)

    decreases(until - from)

    if (index == from) then
      l1 match {
        case Cons(h, t) =>
          sliceCons(l2, from, until)
          assert(h == l2(from))
        case Nil() => ()
      }
    else
      l1 match {
        case Cons(h, t) =>
          sliceCons(l2, from, until)
          sliceAtIndex(t, l2, from + 1, until, index)
        case Nil() => ()
      }
  }.ensuring { _ => l1(index - from) == l2(index) }

  /** ```
    * l1 == l2.slice(from, until) => l1.tail == l2.slice(from + 1, until)
    * ```
    */
  def sliceTail[T](
      l1: List[T],
      l2: List[T],
      from: BigInt,
      until: BigInt
  ): Unit = {
    require(0 <= from && from < l2.size)
    require(0 <= until && until <= l2.size)
    require(from <= until)
    require(l1 == l2.slice(from, until))
    require(l1.size > 0)

    assert(from < until)
    l1 match {
      case Nil()        => ()
      case Cons(h1, t1) =>
        sliceCons(l2, from, until)
    }
  }.ensuring { _ =>
    l1 match {
      case Nil()        => true
      case Cons(h1, t1) => t1 == l2.slice(from + 1, until)
    }
  }

  /** ```
    * l == l.slice(0, l.size)
    * ```
    */
  def sliceZeroSize[T](l: List[T]): Unit = {
    decreases(l)
    l match {
      case Nil()      => ()
      case Cons(h, t) => sliceZeroSize(t)
    }
  }.ensuring { _ => l == l.slice(0, l.size) }

  // ======================
  // ===== Map lemmas =====
  // ======================

  /** ```
    * l.map(f) :+ f(elem) == (l :+ elem).map(f)
    * ```
    */
  def mapDistributesOverAppend[T, U](l: List[T], elem: T, f: T => U): Unit = {
    l match {
      case Nil()      => ()
      case Cons(h, t) => mapDistributesOverAppend(t, elem, f)
    }
  }.ensuring(_ => l.map(f) :+ f(elem) == (l :+ elem).map(f))

  /** ```
    * l.contains(value) ==> l.map(f).contains(f(value))
    * ```
    */
  def mapContains[T, U](l: List[T], f: T => U, value: T): Unit = {
    decreases(l)
    l match {
      case Nil()      => ()
      case Cons(h, t) => mapContains(t, f, value)
    }
  }.ensuring { _ =>
    l.contains(value) ==> l.map(f).contains(f(value))
  }

  /** ```
    * l.updated(addr, elem).map(f) == l.map(f).updated(addr, f(elem))
    * ```
    */
  def mapUpdate[T, U](l: List[T], addr: BigInt, elem: T, f: T => U): Unit = {
    require(0 <= addr && addr < l.size)
    require(f(l(addr)) == f(elem))

    if addr == 0 then ()
    else
      l match {
        case Nil()      => ()
        case Cons(h, t) => mapUpdate(t, addr - 1, elem, f)
      }
  }.ensuring(_ => l.updated(addr, elem).map(f) == l.map(f))

  /** ```
    * l.map(f)(index) == f(l(index))
    * ```
    */
  def mapAtIndex[T, U](l: List[T], index: BigInt, f: T => U): Unit = {
    require(0 <= index && index < l.size)

    if index == 0 then ()
    else
      l match {
        case Nil()      => ()
        case Cons(h, t) => mapAtIndex(t, index - 1, f)
      }
  }.ensuring { _ => l.map(f)(index) == f(l(index)) }

  // ========================
  // ===== Range lemmas =====
  // ========================

  /** ```
    * List.range(start, until) :+ until == List.range(start, until + 1)
    * ```
    */
  def rangeAppend(start: BigInt, until: BigInt): Unit = {
    require(start <= until)
    decreases(until - start)
    if (until == start) then ()
    else rangeAppend(start + 1, until)
  }.ensuring(_ =>
    List.range(start, until) :+ until == List.range(start, until + 1)
  )

  /** ```
    * List.range(start, until)(index) == start + index
    * ```
    */
  def rangeAtIndexPlusStartIsIndexPlusStart(
      start: BigInt,
      until: BigInt,
      index: BigInt
  ): Unit = {
    require(start <= index + start && start + index < until)

    if (index == 0) then ()
    else rangeAtIndexPlusStartIsIndexPlusStart(start + 1, until, index - 1)
  }.ensuring(_ => List.range(start, until)(index) == start + index)

  // =========================
  // ===== Filter lemmas =====
  // =========================

  /** ```
    * x <= l.filter(p).size ==> x <= l.size
    * ```
    */
  def weakenBoundOnListSize[T](
      l: List[T],
      p: T => Boolean,
      x: BigInt
  ): Unit = {
    require(x <= l.filter(p).size)
  }.ensuring { _ => x <= l.size }

}
