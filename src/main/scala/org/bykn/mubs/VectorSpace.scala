package org.bykn.mubs

import cats.Eval
import com.monovore.decline.CommandApp
import java.util.concurrent.Executors
import java.util.BitSet
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
 *
 * TODO: we can standardize an MUB
 *
 * by Zi H_i W_i
 * such that the first row and column
 * are 1, further, we can set Z_0 = I, W_0 = I
 * next we can sort the columns so smaller
 * values appear first
 *
 * Using this equivalence, we can cut
 * the search space by a factor since
 * we can find all standardized bases H_i
 * and then multiply by all possible
 * left and right shifts.
 *
 * lastly, multiplying on the right doesn't
 * change unbiased-ness or orthogonality
 * we can by convention set to I
 *
 * finally, since overall phase doesn't matter
 * we can set the first element of Z_i to 1
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

    val conjProdInt: () => (Int, Int) => Int = {
      // TODO this could be optimized to not use an intermediate vector
      () => {
        val v1 = zeroVec()
        val v2 = zeroVec()
        val target = zeroVec()

        (i1: Int, i2: Int) => {
          intToVector(i1, v1)
          intToVector(i2, v2)
          conjProd(v1, v2, target)
          vectorToInt(target)
        }
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

    private[this] val vectorRange = (0 until vectorCount.toInt)

    private def buildCache(fn: Real => Boolean): BitSet = {
      // first we compute all the traces that are orthogonal
      val tmp = new Array[Int](dim)
      // the java bitset doesn't box on access
      val bitset = new BitSet(vectorCount.toInt)
      vectorRange
        .foreach { v =>
          intToVector(v, tmp)
          if (fn(trace(tmp))) bitset.set(v)
        }

      bitset
    }

    // this builds standardized bases:
    // to be orthogonal: you must also be orthogonal to 0
    // to be unbiased, you must be unbiased to 0
    //
    // return the first index in the set
    private def buildCachedFn(bitset: BitSet): (Int, () => Int => Int => Boolean) = {
      // first we compute all the traces that are orthogonal

      // there should be at least one
      val first = vectorRange.iterator.filter(bitset.get(_)).next()
      // now we have the whole bitset,

      val cp = conjProdInt

      val res = () => {
        val intCP = cp()

        { n1: Int =>
          if (bitset.get(n1)) {

            { n2: Int =>

              (bitset.get(n2)) && {
                val n3 = intCP(n1, n2)
                bitset.get(n3)
              }
            }
          }
          else Function.const(false)(_: Int)
        }
      }

      (first, res)
    }

    /**
     * These are all standardized Hadamards:
     * they have 0 in the last position (1)
     * and they all include the all 0 vector (which is omitted
     * in the response)
     */
    def allBasesFuture()(implicit ec: ExecutionContext): Future[List[Array[Int]]] = {
      val vci = vectorCount.toInt / rootArray.length

      val (first, fn) = buildCachedFn(buildCache(isOrth))
      // we use an array for the ints because it is more space efficient
      // than lists
      Cliques.findAllFuture[Int,Array[Int]](
        size = (dim - 1), // the number of items in a basis is the dimension, in addition to 0
        initNode = first,
        incNode = { i: Int => i + 1},
        isLastNode = { i: Int => vci <= i },
        fn,
        { lst => lst.toArray })
    }

    def allBases(): List[Array[Int]] =
      Await.result(allBasesFuture()(ExecutionContext.global), Inf)

    /**
     * These are sets of mutually unbiased vectors.
     * This is an upper bound on unbiased bases because
     * selecting a single item from unbiased bases is a
     * set of unbiased vectors
     *
     * These are *standardized*: they are all unbiased to 0
     * and all have 0 in the final position
     */
    private def allMubVectorsFutureWithFn(cliqueSize: Int)(implicit ec: ExecutionContext): (BitSet, Future[List[Array[Int]]]) = {
      val vci = vectorCount.toInt / rootArray.length

      val ubBitSet = buildCache(isUnbiased)
      val (first, fn) = buildCachedFn(ubBitSet)
      // we use an array for the ints because it is more space efficient
      // than lists
      (ubBitSet, Cliques.findAllFuture[Int,Array[Int]](
        size = (cliqueSize - 1), // the number of items in a basis is the dimension
        initNode = first,
        incNode = { i: Int => i + 1},
        isLastNode = { i: Int => vci <= i },
        fn,
        { lst => lst.toArray }))
    }

    /**
     * These are sets of mutually unbiased vectors.
     * This is an upper bound on unbiased bases because
     * selecting a single item from unbiased bases is a
     * set of unbiased vectors
     *
     * These are *standardized*: they are all unbiased to 0
     * and all have 0 in the final position
     */
    def allMubVectorsFuture(cliqueSize: Int)(implicit ec: ExecutionContext): Future[List[Array[Int]]] = {
      val (_, fut) = allMubVectorsFutureWithFn(cliqueSize)
      fut
    }

    def allMubVectors(cliqueSize: Int): List[Array[Int]] =
      Await.result(allMubVectorsFuture(cliqueSize)(ExecutionContext.global), Inf)

    // transform all but the first with a the corresponding mub
    // we add back the 0 vector to the front in the results
    private def transformStdBasis(hs: List[Array[Int]], mub: Array[Int], ubBitSet: BitSet): Option[List[Array[Int]]] =
      hs match {
        case Nil => None
        case h :: rest =>
          val cp = conjProdInt()
          // we use conjugate product to transform, but we could also not use conjugate (since
          // conjugate of H is another H
          require(rest.size == mub.length)
          val restz: List[Array[Int]] =
            mub.toList.zip(rest)
              .map { case (z, had) =>
                (cp(z, 0) :: had.toList.map(cp(z, _))).toArray
              }

          val h1 = 0 +: h

          val allBases = h1 :: restz

          val isUB =
            allDistinctPairs(allBases)
              .forall { case (h1, h2) =>
                h1
                  .forall { v1 =>
                    h2.forall { v2 =>
                      ubBitSet.get(cp(v1, v2))
                    }
                  }
              }

          if (isUB) Some(allBases)
          else None
      }

    /**
     * Generate all standard bases, then all sets of unbiased standard vectors.
     * Finally, try to assemble a set of MUBs from these:
     * H0, Z1 H1, Z2 H2, ...
     */
    def allMubsFuture(cnt: Int)(implicit ec: ExecutionContext): Future[List[List[Array[Int]]]] = {

      val (ubBitSet, mubs) = allMubVectorsFutureWithFn(cnt)
      // we can pick any cnt bases, and any (cnt - 1) unbiased vectors
      // to transform them. We have to include the phantom 0 vector
      def assemble(bases: List[Array[Int]], mubV: List[Array[Int]]): Future[List[List[Array[Int]]]] = {
        require(bases.forall(_.size == dim - 1), "invalid basis size")
        require(mubV.forall(_.size == (cnt - 1)), "invalid mub size")
        // these are all sets of cnt bases
        // in every possible order
        val allHs: List[List[Array[Int]]] =
          chooseN(cnt, bases)

        Future.traverse(mubV) { ubv =>
          Future {
            allHs.flatMap { hs =>
              transformStdBasis(hs, ubv, ubBitSet).toList
            }
          }
        }
        .map(_.flatten)
      }

      allBasesFuture().zip(mubs)
        .flatMap { case (bases, mubV) => assemble(bases, mubV) }
    }

    def allMubs(cnt: Int): List[List[Array[Int]]] =
      Await.result(allMubsFuture(cnt)(ExecutionContext.global), Inf)
  }

  // return lists of exactly n items where each item
  // comes from an index in items.
  // we do allow repeats, so we choose with replacement
  def chooseN[A](n: Int, items: List[A]): List[List[A]] = {

    def loop(n: Int): List[List[A]] =
      if (n <= 0) Nil :: Nil
      else {
        // we could pick any first item
        // followed by picking n-1 from any items
        items.flatMap { h =>
          loop(n - 1).map(h :: _)
        }
      }

    loop(n)
  }

  def allDistinctPairs[A](items: List[A]): List[(A, A)] = {
    @annotation.tailrec
    def loop(items: List[A], acc: List[(A, A)]): List[(A, A)] =
      items match {
        case Nil => acc.reverse
        case h :: rest =>
          val hpairs = rest.map((h, _))
          loop(rest, hpairs reverse_::: acc)
      }

    loop(items, Nil)
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
