package org.bykn.mubs

import scala.reflect.ClassTag
import shapeless.{Nat}
import shapeless.ops.nat.ToInt
import spire.math.{SafeLong, Real}

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

    def dotAbs(v1: Array[Int], v2: Array[Int]): Real = {
      require(v1.length == v2.length)
      var idx = 0
      var acc = C.zero
      while (idx < v1.length) {
        val left = rootArray(v1(idx))
        val right = rootArray(v2(idx))
        acc = C.plus(acc, C.times(left, right))
        idx = idx + 1
      }

      C.abs2(acc)
    }

    def maybeOrth(v1: Array[Int], v2: Array[Int]): Boolean = {
      // now, we want to see if
      // acc <= 4d sin^2(pi / n)
      val diff = dotAbs(v1, v2) - eps

      // this is the closest rational x such that r = x/2^p
      diff(realBits).signum <= 0
    }

    def maybeUnbiased(v1: Array[Int], v2: Array[Int]): Boolean = {
      // now, we want to see if
      // |acc - d| <= 4d sin^2(pi / n)
      val diff = (dotAbs(v1, v2) - realD).abs - eps

      // this is the closest rational x such that r = x/2^p
      diff(realBits).signum <= 0
    }

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
  }
}
