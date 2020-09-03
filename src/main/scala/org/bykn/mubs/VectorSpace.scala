package org.bykn.mubs

import scala.reflect.ClassTag
import shapeless.{Nat}
import shapeless.ops.nat.ToInt
import spire.math.{SafeLong, Real}
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.concurrent.duration.Duration.Inf

/**
 * We say a pair of vectors, of dimension d
 * is approximately orthogonal
 * if |<a, b>|^2 <= 4d sin^2(pi / n)
 *
 * we are approximately unbiased
 *
 * if ||<a, b>|^2 - d| <= 4d sin^2(pi / n)
 */
object VectorSpace {

  // realBits is how many real bits to compute
  class Space[N <: Nat, C: ClassTag](dim: Int, realBits: Int)(implicit val C: Cyclotomic[N, C]) {
    // the total possible set of hadamard vectors is
    // (2^N)^d
    // for (2^N = 8) and d = 6, this is 262144
    // for (2^N = 16) and d = 6, this is 16.7 x 10^6
    // for (2^N = 32) and d = 6, this is 1.07 x 10^9

    // array lookup is faster
    private val rootArray: Array[C] = C.roots.toArray

    val vectorCount: SafeLong = SafeLong(rootArray.length).pow(dim)

    require(vectorCount <= SafeLong(Int.MaxValue), s"we can't fit $vectorCount into an Int")

    val realD: Real = Real(dim)

    val eps: Real = {
      // theta = 2 pi / n
      // C.omega = e^(2 pi i / n)
      // C.omega ^(1/2) = e^(pi i /n)
      // sin^2(theta/2) = (1 - cos(theta))/2
      // 4d sin^2(theta/2) = 2d(1 - re(C.omega))

      Real(2 * dim) * (Real.one - C.reOmega)
    }

    def zeroVec(): Array[Int] = new Array[Int](dim)

    def vectorToInt(v: Array[Int]): Int = {
      // consider this as a number base rootArray.length
      var idx = v.length
      var acc = 0
      val size = rootArray.length
      while (idx > 0) {
        idx = idx - 1
        acc = acc * size + v(idx)
      }

      acc
    }

    def intToVector(i: Int, into: Array[Int]): Unit = {
      // consider this as a number base rootArray.length
      var idx = 0
      var value = i
      val size = rootArray.length
      while (idx < into.length) {
        into(idx) = value % size
        value = value / size
        idx = idx + 1
      }
    }

    // if there is a vector after the current
    // one, inc to that and return true
    def incInPlace(v: Array[Int]): Boolean = {
      var idx = 0
      while (idx < v.length) {
        val vi = v(idx)
        val next = vi + 1
        if (next < rootArray.length) {
          // this is valid
          v(idx) = next
          return true
        }
        else {
          // set this to zero and increment the next
          v(idx) = 0
          idx = idx + 1
        }
      }

      false
    }

    def trace(v: Array[Int]): Real = {
      var idx = 0
      var acc = C.zero
      while (idx < v.length) {
        val item = rootArray(v(idx))
        acc = C.plus(acc, item)
        idx = idx + 1
      }
      C.abs2(acc)
    }

    def conjProd(v1: Array[Int], v2: Array[Int], target: Array[Int]): Unit = {
      require(v1.length == v2.length)
      require(v1.length == target.length)

      var idx = 0
      while (idx < v1.length) {
        val left = rootArray.length - v1(idx)
        val right = v2(idx)
        target(idx) = (left + right) % rootArray.length
        idx = idx + 1
      }
    }

    // we do the conjugate on the left
    def dotAbs(v1: Array[Int], v2: Array[Int]): Real = {
      require(v1.length == v2.length)
      var idx = 0
      var acc = C.zero
      while (idx < v1.length) {
        val v1idx = v1(idx)
        val left = rootArray(if (v1idx == 0) 0 else (rootArray.length - v1idx))
        val right = rootArray(v2(idx))
        acc = C.plus(acc, C.times(left, right))
        idx = idx + 1
      }

      C.abs2(acc)
    }

    def isOrth(r: Real): Boolean = {
      val diff = r - eps

      // this is the closest rational x such that r = x/2^p
      diff(realBits).signum <= 0
    }

    def isUnbiased(r: Real): Boolean = {
      val diff = (r - realD).abs - eps
      // this is the closest rational x such that r = x/2^p
      diff(realBits).signum <= 0
    }

    def maybeOrth(v1: Array[Int], v2: Array[Int]): Boolean =
      // now, we want to see if
      // acc <= 4d sin^2(pi / n)
      isOrth(dotAbs(v1, v2))

    def maybeUnbiased(v1: Array[Int], v2: Array[Int]): Boolean =
      // now, we want to see if
      // |acc - d| <= 4d sin^2(pi / n)
      isUnbiased(dotAbs(v1, v2))

    // we represent each hadamard as a set of indices into the roots
    def isApproximatelyOrthogonal(vectors: List[Array[Int]]): Boolean = {
      vectors match {
        case Nil => true
        case h :: rest =>
          // the head has to be approximately orthogonal:
          rest.forall { r =>
            maybeOrth(h, r)
          } && isApproximatelyOrthogonal(rest)
      }
    }

    // we own from and can mutate it
    @annotation.tailrec
    final def augmentOrth(from: Array[Int], vs: List[Array[Int]]): Option[List[Array[Int]]] = {
      val canAdd = vs.forall(maybeOrth(from, _))
      if (canAdd) Some(from :: vs)
      else if (incInPlace(from)) {
        augmentOrth(from, vs)
      }
      else None
    }

    def tryComplete(init: Array[Int]): Option[List[Array[Int]]] = {
      val i0 = init.clone()
      augmentOrth(i0, Nil)
    }

    def orthToZero: Int = {
      val z = zeroVec()
      val v = zeroVec()
      var cont = true
      var count = 0
      while (cont) {
        val o = maybeOrth(z, v)
        val vint = vectorToInt(v)
        if ((vint & 0xFFF) == 0) {
          println(s"current count: $count, vector: ${vint}, orth: $o")
        }

        if (o) {
          count = count + 1
        }
        cont = incInPlace(v)
      }

      count
    }

    def ubToZero: Int = {
      val z = zeroVec()
      val v = zeroVec()
      var cont = true
      var count = 0
      while (cont) {
        val o = maybeUnbiased(z, v)
        if (o) {
          count = count + 1
        }
        cont = incInPlace(v)
      }

      count
    }

    private def buildCachedFn(fn: Real => Boolean): () => Int => Int => Boolean = {
      // first we compute all the traces that are orthogonal
      val tmp = new Array[Int](dim)
      val bitset = new scala.collection.mutable.BitSet(vectorCount.toInt)
      (0 until vectorCount.toInt)
        .foreach { v =>
          intToVector(v, tmp)
          if (fn(trace(tmp))) bitset.addOne(v)
        }

      // now we have the whole bitset,

      () => {
        val v1 = new Array[Int](dim)
        val v2 = new Array[Int](dim)
        val v3 = new Array[Int](dim)

        { n1: Int =>
          intToVector(n1, v1)

          { n2: Int =>
            intToVector(n2, v2)
            conjProd(v1, v2, v3)
            val n3 = vectorToInt(v3)
            bitset(n3)
          }
        }
      }
    }

    // there are all orthogonal basis
    def allBasesFuture()(implicit ec: ExecutionContext): Future[LazyList[List[Int]]] = {
      val vci = vectorCount.toInt

      Cliques.findAllFuture[Int](
        size = dim, // the number of items in a basis is the dimension
        initNode = 0,
        incNode = { i: Int => i + 1},
        isLastNode = { i: Int => vci <= i },
        buildCachedFn(isOrth))
    }

    def allBases(): LazyList[List[Int]] =
      Await.result(allBasesFuture()(ExecutionContext.global), Inf)

    def allMubsFuture(cnt: Int)(implicit ec: ExecutionContext): Future[LazyList[List[List[Int]]]] = {
      // we use the head of this list as the node
      type Node = LazyList[List[Int]]
      def nodeToList(n: Node): List[Int] = n.head

      def incNode(n: Node): Node = n.tail
      def isLastNode(n: Node): Boolean = n.isEmpty

      val ubFn = buildCachedFn(isUnbiased)

      val buildBasisFn = () => {
        val pairFn = ubFn()

        // two heads are unbiased, if they are pairwise unbiased
        { n1: Node =>
          val list1 = nodeToList(n1).map(pairFn)

          { n2: Node =>
            val list2 = nodeToList(n2)

            list1
              .iterator
              .forall { fn1 =>
                list2.forall(fn1)
              }
          }
        }
      }

      allBasesFuture()
        .flatMap { nodes =>
          Cliques.findAllFuture[Node](
          size = cnt, // the number of items in a basis is the dimension
          initNode = nodes,
          incNode = incNode,
          isLastNode = isLastNode,
          buildBasisFn)
        }
        .map { cliques =>
          cliques.map { members =>
            members.map(nodeToList)
          }
        }
    }

    def allMubs(cnt: Int): LazyList[List[List[Int]]] =
      Await.result(allMubsFuture(cnt)(ExecutionContext.global), Inf)
  }
}
