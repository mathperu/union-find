package ourlistspecs

import stainless.lang._
import stainless.proof._
import stainless.collection.{List, ListSpecs, Nil}
import stainless.annotation._
import stainless.collection.Cons

object OurListSpecs {

    // Append lemmas

    def appendedElementIsAtIndexOldSize[T](l: List[T], elem: T): Unit = {
        decreases(l)
        l match {
            case Nil() => 
            case Cons(h, t) => appendedElementIsAtIndexOldSize(t, elem)
        }
    }.ensuring{_ => (l :+ elem)(l.size) == elem}

    def forallAppend[T](l: List[T], elem: T, p: T => Boolean): Unit = {
        require(l.forall(p) && p(elem))
        decreases(l)
        (l :+ elem, l) match {
            case (Nil(), _) => ()
            case (Cons(h, Nil()), Nil()) => 
                assert(h == elem)
                assert(p(elem))
            case (Cons(h1, t1), Cons(h2, t2)) => 
                assert(h1 == h2)
                assert(p(h1))
                assert(p(h2))
                forallAppend(t2, elem, p)
        }
    }.ensuring{_ => (l :+ elem).forall(p)}

    def appendPreservesIndices[T](l: List[T], n: T, i: BigInt): Unit = {
        require(0 <= i && i < l.size)
        decreases(l)
        (l :+ n, l) match {
            case (Nil(), _) => ()
            case (Cons(h1, Nil()), Nil()) => 
                assert(h1 == n)
                assert(i < 0)
            case (Cons(h1, t1), Cons(h2, t2)) => 
                assert(h1 == h2)
                if (i == 0) then ()
                else appendPreservesIndices(t2, n, i-1)
        }
    }.ensuring{_ => (l :+ n)(i) == l(i)}

    // Update lemmas

    def forallUpdate[T](l: List[T], addr: BigInt, elem: T, p: T => Boolean): Unit = {
        require(0 <= addr && addr < l.size)
        require(l.forall(p) && p(elem))
        
        if addr == 0 then ()
        else l match {
            case Nil() => ()
            case Cons(h, t) => forallUpdate(t, addr - 1, elem, p)
        }
    }.ensuring(_ => (l.updated(addr, elem)).forall(p))

    // Slice lemmas

    def sliceCons[T](l: List[T], from: BigInt, until: BigInt): Unit = {
        require(0 <= from && from < l.size && 0 <= until && until <= l.size)
        require(from < until)
         l match {
            case Nil() => ()
            case Cons(h, t) =>
                if (from == 0) then ()
                else sliceCons(t, from - 1, until - 1)
        }
    }.ensuring(_ => l.slice(from, until) == Cons(l(from), l.slice(from + 1, until)))

    def sliceAtIndex[T](l1: List[T], l2: List[T], from: BigInt, until: BigInt, index: BigInt): Unit = {
        require(0 <= from && from < l2.size)
        require(0 <= until && until <= l2.size)
        require(from <= until)
        require(l1 == l2.slice(from, until))
        require(from <= index && index < until)

        decreases(until - from)

        if (index == from) then l1 match {
                case Cons(h, t) =>
                    sliceCons(l2, from, until)
                    assert(h == l2(from))
                case Nil() => ()
        }
        else l1 match {
                case Cons(h, t) =>
                    sliceCons(l2, from, until)
                    sliceAtIndex(t, l2, from + 1, until, index)
                case Nil() => ()
        }
    }.ensuring{_ => l1(index - from) == l2(index)}

    def sliceTail[T](l1: List[T], l2: List[T], from: BigInt, until: BigInt): Unit = {
        require(0 <= from && from < l2.size)
        require(0 <= until && until <= l2.size)
        require(from <= until)
        require(l1 == l2.slice(from, until))
        require(l1.size > 0)

        assert(from < until)
        l1 match {
            case Nil() => ()
            case Cons(h1, t1) => 
                sliceCons(l2, from, until)
        }
    }.ensuring{_ => l1 match {
        case Nil() => true
        case Cons(h1, t1) => t1 == l2.slice(from + 1, until)
    }}

    def sliceZeroSize[T](l: List[T]): Unit = {
        decreases(l)
        l match {
            case Nil() => ()
            case Cons(h, t) => sliceZeroSize(t)
        }
    }.ensuring{_ => l == l.slice(0, l.size)}

    // Map lemmas

    def mapDistributesOverAppend[T, U](l: List[T], elem: T, f: T => U): Unit = {
        l match {
            case Nil() => ()
            case Cons(h, t) => mapAppend(t, elem, f)
        }
    }.ensuring(_ => l.map(f) :+ f(elem) == (l :+ elem).map(f))

    def mapUpdate[T, U](l: List[T], addr: BigInt, elem: T, f: T => U): Unit = {
        require(0 <= addr && addr < l.size)
        require(f(l(addr)) == f(elem))
        
        if addr == 0 then ()
        else l match {
            case Nil() => ()
            case Cons(h, t) => mapUpdate(t, addr - 1, elem, f)
        }
    }.ensuring(_ => l.updated(addr, elem).map(f) == l.map(f))

    def mapAtIndex[T, U](l: List[T], index: BigInt, f: T => U): Unit = {
        require(0 <= index && index < l.size)
        
        if index == 0 then ()
        else l match {
            case Nil() => ()
            case Cons(h, t) => mapAtIndex(t, index - 1, f)
        }
    }.ensuring{_ => l.map(f)(index) == f(l(index))}

    // Range lemmas

    def rangeAppend(start: BigInt, until: BigInt): Unit = {
        require(start <= until)
        decreases(until - start)
        if (until == start) then ()
        else rangeAppend(start + 1, until)
    }.ensuring(_ => List.range(start, until) :+ until == List.range(start, until + 1))

    def rangeAtIndexPlusStartIsIndexPlusStart(start: BigInt, until: BigInt, index: BigInt): Unit = {
        require(start <= index + start && start + index < until)

        if (index == 0) then ()
        else rangeAtIndexPlusStartIsIndexPlusStart(start + 1, until, index - 1)
    }.ensuring(_ => List.range(start, until)(index) == start + index)
}
