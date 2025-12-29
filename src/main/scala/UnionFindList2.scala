import stainless.lang._
import stainless.proof._
import stainless.collection.{List, ListSpecs}
import stainless.annotation._
import stainless.collection.Cons
import org.w3c.dom.ls.LSInput

object UnionFindList2{

    sealed trait Node[T]{
        val addr: BigInt
        val value: T
    }
    
    case class Child[T](addr: BigInt, value: T, parentAddr: BigInt) extends Node[T]
    case class Root[T](addr: BigInt, value: T, rank: BigInt) extends Node[T]

    def parentIsInHeap[T](n: Node[T], heap: List[Node[T]]): Boolean = {
        if (0 <= n.addr && n.addr < heap.size) then
            n match {
                case Child(_, _, pA) => 0 <= pA && pA < heap.size
                case _           => true
            }
        else false
    }

    def addrAndHeapMatch[T](n: Node[T], heap: List[Node[T]]): Boolean = {
        if 0 <= n.addr && n.addr < heap.size then heap(n.addr) == n
        else false
    }

    // invariant idea A: traversal is bounded by the heap's size
    def traverseBounded[T](start: Node[T], heap: List[Node[T]]): Boolean = {
        def traverseBoundedRec(n: Node[T], fuel: BigInt): BigInt = {
            require(fuel >= 0)
            decreases(fuel)
            if (fuel == 0) BigInt(0)
            else n match
                case Child(addr, value, parentAddr) => 
                    if (parentAddr >= 0 && parentAddr < heap.size)
                        traverseBoundedRec(heap(parentAddr), fuel - 1) + 1
                    else BigInt(1)
                case Root(addr, value, rank) => BigInt(0)
        }

        traverseBoundedRec(start, heap.size) < heap.size
    }

    // invariant idea B: going up will always end up on a root
    def finishAtRoot[T](start: Node[T], heap: List[Node[T]]): Boolean = {
        def inner(n: Node[T], fuel: BigInt): Node[T] = {
            require(fuel >= 0)
            decreases(fuel)
            if (fuel == 0) n
            else n match
                case Child(addr, value, parentAddr) => 
                    if (parentAddr >= 0 && parentAddr < heap.size)
                        inner(heap(parentAddr), fuel - 1)
                    else n
                case r @ Root(addr, value, rank) => r
        }

        isRoot(inner(start, heap.size))
    }

    def isRoot[T](n: Node[T]): Boolean = {
        n match {
        case Root(a, v, r) => true
        case _             => false
        }
    }


    case class UF[T](heap: List[Node[T]]) {
        val parentFunc = (heap: List[Node[T]]) => n => parentIsInHeap[T](n, heap)
        val parentFuncOnHeap = parentFunc(heap)
        val parentInHeapInvariant = heap.forall(parentFuncOnHeap)
        require(parentInHeapInvariant)

        val addrFunc = (heap: List[Node[T]]) => n => addrAndHeapMatch[T](n, heap)
        val addrFuncOnHeap = addrFunc(heap)
        val addrInvariant = heap.forall(addrFuncOnHeap)
        require(addrInvariant)

        // invariant A
        require(heap.forall(finishAtRoot(_, heap)))

        // invariant B
        require(heap.forall(traverseBounded(_, heap)))




        def size: BigInt = heap.size
        def domain: List[T] = heap.map(n => n.value)

        def isValidAddr(addr: BigInt): Boolean =
            addr >= 0 && addr < size

        def nodeAt(addr: BigInt): Node[T] = 
            require(isValidAddr(addr))
            heap(addr)

        def getParentAddr(n: Node[T]): BigInt =
            n match {
                case Child(addr, value, parentAddr) => parentAddr
                case Root(addr, value, rank) => addr
            }

        def set(addr: BigInt, n: Node[T]): UF[T] =
            require(isValidAddr(addr))
            require(n.addr == addr)
            require(isValidAddr(getParentAddr(n)))

            UF(heap.updated(addr, n))

        def nodeAtIsRoot(addr: BigInt): Boolean = {
            if (isValidAddr(addr)) then isRoot(nodeAt(addr))
            else true
        }

        def rankIs(n: Node[T], x: BigInt): Boolean = {
            n match {
                case Child(addr, value, parentAddr) => false
                case Root(addr, value, rank) => rank == x
            }
            
        }

        // invariant timeout in stainless
        def make(value: T): (UF[T], Node[T]) = {
            require(!domain.contains(value))

            val addr = size
            val newNode = Root(addr, value, 0)
            val newHeap = heap :+ newNode
            (UF(newHeap), newNode)
        }

        // no path compression
        // provide address and finds parent's address

        def findRec(addr: BigInt, fuel: BigInt): BigInt = {
            require(fuel >= 0)
            decreases(fuel)
            if fuel == 0 then -1
            else 
                if isValidAddr(addr) then 
                    nodeAt(addr) match {
                        case Child(addr, value, parentAddr) => findRec(parentAddr, fuel - 1)
                        case Root(ad, value, rank) => addr
                    }
                else addr
        }

        def find(addr: BigInt): BigInt = {
            findRec(addr, size)
        }

        def equiv(a1: BigInt, a2: BigInt): Boolean = {
            find(a1) == find(a2)
        }

        def link(a1: BigInt, a2: BigInt): (UF[T], BigInt) = {
            require(isValidAddr(a1) && isValidAddr(a2) && nodeAtIsRoot(a1) && nodeAtIsRoot(a2))

            if a1 == a2 then (this, a1)
            else
                (nodeAt(a1), nodeAt(a2)) match {
                    case (Root(ad1, v1, r1), Root(ad2, v2, r2)) => 
                        if r1 < r2 then 
                            val newNode1 = Child(a1, v1, a2)
                            val newUF = this.set(a1, newNode1)
                            (newUF, a2)
                        else if r1 > r2 then 
                            val newNode2 = Child(a2, v2, a1)
                            val newUF = this.set(a2, newNode2)
                            (newUF, a1)
                        else 
                            val newNode1 = Child(a1, v1, a2)
                            val newUF1 = this.set(a1, newNode1)
                            val newNode2 = Root(a2, v2, r2 + 1)
                            val newUF2 = newUF1.set(a2, newNode2)
                            (newUF2, a2)

                    case (_, _) => 
                        assert(nodeAtIsRoot(a1) && nodeAtIsRoot(a2))
                        (this, BigInt(-1))
                }             
        }

        def union(a1: BigInt, a2: BigInt): (UF[T], BigInt) = {
            require(isValidAddr(a1) && isValidAddr(a2))
            val r1 = find(a1)
            val r2 = find(a2)
            findReturnsRoot(a1)
            findReturnsRoot(a2)
            assert(nodeAtIsRoot(r1) && nodeAtIsRoot(r2))
            findReturnsValidAddr(a1)
            findReturnsValidAddr(a2)
            assert(isValidAddr(r1) && isValidAddr(r2))

            link(find(a1), find(a2))
        }


        def findReturnsRoot(addr: BigInt): Unit = {
            def findReturnsRootRec(addr: BigInt, fuel: BigInt): Unit = {
                require(fuel >= 0)
                decreases(fuel)
                
                if fuel == 0 then ()
                else 
                    if isValidAddr(addr) then 
                        nodeAt(addr) match {
                            case nc @ Child(addr, value, parentAddr) => 
                                ListSpecs.forallContained(heap, parentFuncOnHeap, nc)
                            
                                findReturnsRootRec(parentAddr, fuel - 1)
                                
                            case Root(ad, value, rank) => 
                                ()
                        }
                    else ()
            }.ensuring(_ => 
                !isValidAddr(findRec(addr, fuel)) || 
                nodeAtIsRoot(findRec(addr, fuel))
            )

            findReturnsRootRec(addr, size)
        }.ensuring(_ => !isValidAddr(find(addr)) || nodeAtIsRoot(find(addr)))

        // invalid in stainless: measure missing
        def findReturnsValidAddr(addr: BigInt): Unit = {
            def findReturnsValidAddrRec(addr: BigInt, fuel: BigInt): Unit = {
                require(fuel >= 0)
                decreases(fuel)
                
                if fuel == 0 then ()
                else 
                    if isValidAddr(addr) then 
                        nodeAt(addr) match {
                            case nc @ Child(_, _, parentAddr) =>
                                assert(heap.contains(nc))
                                
                                ListSpecs.forallContained(heap, parentFuncOnHeap, nc)
                                
                                assert(parentIsInHeap(nc, heap))
                                
                                assert(isValidAddr(parentAddr))
                                
                                findReturnsValidAddrRec(parentAddr, fuel - 1)
                                
                            case Root(_, _, _) => 
                                ()
                        }
                    else ()
            }.ensuring(_ => 
                findRec(addr, fuel) == -1 || 
                (!isValidAddr(addr) || isValidAddr(findRec(addr, fuel)))
            )

            findReturnsValidAddrRec(addr, size)
        }.ensuring(_ => find(addr) == -1 || (!isValidAddr(addr) || isValidAddr(find(addr))))


        def makeAddsValueToDomain(value: T): Unit = {
            require(!domain.contains(value))
        }.ensuring(_ => make(value)._1.domain.contains(value))

        def makeReturnsASingletonSet(value: T): Unit = {
            require(!domain.contains(value))
        }.ensuring(_ => isRoot(make(value)._2) 
                        && (find(make(value)._2.addr) == BigInt(-1) || find(make(value)._2.addr) == make(value)._2.addr)
                        && rankIs(make(value)._2, BigInt(0))
        )


        def linkReturnsARootOfInput(a1: BigInt, a2: BigInt): Unit = {
            require(isValidAddr(a1) && isValidAddr(a2) && nodeAtIsRoot(a1) && nodeAtIsRoot(a2))
        }.ensuring(_ => link(a1, a2)._2 == a1 || link(a1, a2)._2 == a2)

        def unionReturnsARootOfInput(a1: BigInt, a2: BigInt): Unit = {
            require(isValidAddr(a1) && isValidAddr(a2))
        }.ensuring(_ => union(a1, a2)._2 == find(a1) || union(a1, a2)._2 == find(a2))

        def unionMergedTheSets(a1: BigInt, a2: BigInt, b: BigInt): Unit = {
            require(isValidAddr(a1) && isValidAddr(a2))
        }.ensuring(_ => (!(equiv(a1, b) || equiv(a2, b)) || find(b) == union(a1, a2)._2)
                        && ((equiv(a1, b) || equiv(a2, b)) || find(b) != union(a1, a2)._2)
        )

    }

}
