package org.bykn.mubs

import com.monovore.decline.CommandApp
import java.util.concurrent.Executors
import scala.concurrent.duration.Duration.Inf
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.reflect.ClassTag
import shapeless.ops.nat.ToInt
import shapeless.{Nat}
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
  class Space[N <: Nat, C: ClassTag](val dim: Int, realBits: Int)(implicit val C: Cyclotomic[N, C]) {

    // the total possible set of hadamard vectors is
    // (2^N)^d
    // for (2^N = 8) and d = 6, this is 262144
    // for (2^N = 16) and d = 6, this is 16.7 x 10^6
    // for (2^N = 32) and d = 6, this is 1.07 x 10^9

    // array lookup is faster
    private val rootArray: Array[C] = C.roots.toArray

    override def toString: String = {
      s"Space(dim = $dim, roots = ${rootArray.length} realBits = $realBits)"
    }

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
      // the java bitset doesn't box on access
      val bitset = new java.util.BitSet(vectorCount.toInt)
      (0 until vectorCount.toInt)
        .foreach { v =>
          intToVector(v, tmp)
          if (fn(trace(tmp))) bitset.set(v)
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
            bitset.get(n3)
          }
        }
      }
    }

    // there are all orthogonal basis
    def allBasesFuture()(implicit ec: ExecutionContext): Future[List[Array[Int]]] = {
      val vci = vectorCount.toInt

      // we use an array for the ints because it is more space efficient
      // than lists
      Cliques.findAllFuture[Int,Array[Int]](
        size = dim, // the number of items in a basis is the dimension
        initNode = 0,
        incNode = { i: Int => i + 1},
        isLastNode = { i: Int => vci <= i },
        buildCachedFn(isOrth),
        { lst => lst.toArray })
    }

    def allBases(): List[Array[Int]] =
      Await.result(allBasesFuture()(ExecutionContext.global), Inf)

    def allMubsFuture(cnt: Int)(implicit ec: ExecutionContext): Future[List[List[Array[Int]]]] = {
      // we use the head of this list as the node
      type Node = List[Array[Int]]
      def nodeToList(n: Node): Array[Int] = n.head

      def incNode(n: Node): Node = n.tail
      def isLastNode(n: Node): Boolean = n.lengthCompare(1) == 0

      val ubFn = buildCachedFn(isUnbiased)

      val buildBasisFn = () => {
        val pairFn = ubFn()

        // two heads are unbiased, if they are pairwise unbiased
        { n1: Node =>
          val list1 = nodeToList(n1)

          { n2: Node =>
            val list2 = nodeToList(n2)

            list1
              .forall { l1 =>
                val fn1 = pairFn(l1)
                list2.forall(fn1)
              }
          }
        }
      }

      allBasesFuture()
        .flatMap { nodes =>
          Cliques.findAllFuture[Node, List[Node]](
            size = cnt, // the number of items in a basis is the dimension
            initNode = nodes,
            incNode = incNode,
            isLastNode = isLastNode,
            buildBasisFn,
            identity)
        }
        .map { cliques =>
          cliques.map { members =>
            members.map(nodeToList)
          }
        }
    }

    def allMubs(cnt: Int): List[List[Array[Int]]] =
      Await.result(allMubsFuture(cnt)(ExecutionContext.global), Inf)
  }
}

object SearchApp extends CommandApp(
  name = "mub-search",
  header = "search for approximate mutually unbiased bases",
  main = {
    import com.monovore.decline.Opts
    import cats.data.Validated
    import VectorSpace.Space

    import cats.implicits._

    val realBits = Opts.option[Int]("bits", "number of bits to use in computable reals, default = 30").withDefault(30)
    val dim = Opts.option[Int]("dim", "the dimension we are working in, should be small!").mapValidated { d =>
      if (d < 2) Validated.invalidNel(s"invalid dimension: $d, should be >= 2")
      else Validated.valid(d)
    }

    val goalMubs = Opts.option[Int]("mubs", "the number of mutually unbiased bases we try to find")
      .orNone

    val threads = Opts.option[Int]("threads", "number of threads to use, default = number of processors")
      .withDefault(Runtime.getRuntime().availableProcessors())

    val depth = Opts.option[Int]("depth", "we use 2^depth roots of unity")
      .mapValidated { d =>

        if ((0 <= d) && (d <= 4)) Validated.valid {
          d match {
            case 0 => { (d: Int, bits: Int) => new Space[Cyclotomic.N0, Cyclotomic.C0](d, bits) }
            case 1 => { (d: Int, bits: Int) => new Space[Cyclotomic.N1, Cyclotomic.L1](d, bits) }
            case 2 => { (d: Int, bits: Int) => new Space[Cyclotomic.N2, Cyclotomic.L2](d, bits) }
            case 3 => { (d: Int, bits: Int) => new Space[Cyclotomic.N3, Cyclotomic.L3](d, bits) }
            case 4 => { (d: Int, bits: Int) => new Space[Cyclotomic.N4, Cyclotomic.L4](d, bits) }
          }
        }
        else Validated.invalidNel(s"invalid depth: $d")
      }

    realBits
      .product(dim)
      .product(depth)
      .map { case ((b, d), fn) => fn(d, b) }
      .product(goalMubs)
      .product(threads)
      .map { case ((space, mubsOpt), threads) =>
        // dim is the most we can get
        val mubs = mubsOpt.getOrElse(space.dim)

        val eserv = Executors.newFixedThreadPool(threads)
        implicit val ec = ExecutionContext.fromExecutorService(eserv)
        println(s"# $space")
        val mubsVector = Await.result(space.allMubsFuture(mubs), Inf)
        println(s"# found: ${mubsVector.length}")
        var idx = 0
        val ary = new Array[Int](space.dim)

        mubsVector.foreach { clique =>
          def showBasis(v: List[Array[Int]]): String = {
            def showInt(i: Int): String = {
              space.intToVector(i, ary)
              ary.mkString("[", ", ", "]")
            }
            v.map { vs => vs.map(showInt).mkString("[[", ", ", "]]") }.mkString("[[[\n\t", ",\n\t", "\n]]")
          }

          val cliqueStr = showBasis(clique)
          println(s"$idx: $cliqueStr")
          idx = idx + 1
        }

        eserv.shutdown()
      }
  }
)
