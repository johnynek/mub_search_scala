package org.bykn.mubs

import algebra.ring.Ring
import cats.Eval
import cats.data.NonEmptyList
import com.monovore.decline.CommandApp
import java.io.{DataInputStream, DataOutputStream, FileInputStream, FileOutputStream, InputStream, OutputStream}
import java.util.concurrent.Executors
import java.util.concurrent.atomic.AtomicLong
import java.util.BitSet
import java.util.zip.{GZIPInputStream, GZIPOutputStream}
import java.nio.file.Path
import scala.concurrent.duration.Duration.Inf
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.reflect.ClassTag
import spire.math.{SafeLong, Complex, Real}

import cats.implicits._

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
  class Space[N <: BinNat, C: ClassTag](val dim: Int, realBits: Int)(implicit val C: Cyclotomic[N, C]) {

    // the total possible set of hadamard vectors is
    // (2^N)^d
    // for (2^N = 8) and d = 6, this is 262144
    // for (2^N = 16) and d = 6, this is 16.7 x 10^6
    // for (2^N = 32) and d = 6, this is 1.07 x 10^9

    // array lookup is faster
    private val rootArray: Array[C] = C.roots.toArray
    private val rootArrayComplex: Array[Complex[Real]] = C.roots.toArray.map(C.toComplex)

    private val nroots: Int = rootArray.length

    val vectorCount: SafeLong = SafeLong(nroots).pow(dim)


    // we always set the last vector element to exp(2 pi i * 0) = 1
    require(vectorCount/nroots <= SafeLong(Int.MaxValue), s"we can't fit ${vectorCount/nroots} into an Int")
    val standardCount: Int = (vectorCount / nroots).toInt

    val realD: Real = Real(dim)

    /**
     * This is 2d * sin(pi/n) when n>1, else 2d
     * we use d' = d - 1 because we can always
     * standardize the original vectors to have
     * 1 as the last element. 1 is a root of
     * unity, so there is no difference on that
     * axis
     */
    val eps: Real = {
      // theta = 2 pi / n
      // C.omega = e^(2 pi i / n)
      // C.omega ^(1/2) = e^(pi i /n)
      // sin(theta/2) = ((1 - cos(theta))/2).sqrt
      // 2d sin(theta/2) = 2d((1 - re(C.omega))/2).sqrt

      val dMinus1 = Real(dim - 1)

      if (nroots == 1) dMinus1
      else {
        Real.two * dMinus1 * (((Real.one - C.reOmega)/Real.two).sqrt)
      }
    }

    override def toString: String = {
      s"Space(dim = $dim, roots = ${nroots}, standardCount = $standardCount, realBits = $realBits, eps = $eps, ubEpsIsTrivial = $ubEpsIsTrivial, orthEpsIsTrivial = $orthEpsIsTrivial)"
    }

    // quantize a vector to the nearest root of unity
    // this is for exploring quantization bounds
    def quantize(vec: List[Complex[Real]]): List[Complex[Real]] = {
      implicit val ordReal: Ordering[Real] =
        new Ordering[Real] {
          def compare(r1: Real, r2: Real) = (r1 - r2)(realBits).signum.toInt
        }

      def nearest(c: Complex[Real]): Complex[Real] =
        rootArrayComplex
          .minBy { wc =>
            (c - wc).absSquare
          }

      vec.map(nearest)
    }

    def innerAbs2(left: List[Complex[Real]], right: List[Complex[Real]]): Real =
      Ring[Complex[Real]]
        .sum(
          left.zip(right)
            .map { case (u, v) =>
              u.conjugate * v
            })
        .absSquare

    //if we quantize to nearest root of unity, the inner product error is <= eps with eps = 2d sin(pi/n)
    def quantizationBoundGap(v1: List[Complex[Real]], v2: List[Complex[Real]]): Real = {
      require(v1.length == v2.length)
      require(v1.length == (dim - 1))

      val exact = innerAbs2(v1, v2).sqrt
      val quant = innerAbs2(quantize(v1), quantize(v2)).sqrt
      val left = (exact - quant).abs
      val right = eps

      val gap = right - left

      // we know that left <= right so gap >= 0
      // we want the minimum value to be close to 0 to prove
      // this bound is tight
      gap
    }

    def zeroVec(): Array[Int] = new Array[Int](dim)

    def vectorToInt(v: Array[Int]): Int = {
      // consider this as a number base nroots
      var idx = v.length
      var acc = 0
      val size = nroots
      while (idx > 0) {
        idx = idx - 1
        acc = acc * size + v(idx)
      }

      acc
    }

    def intToVector(i: Int, into: Array[Int]): Unit = {
      // consider this as a number base nroots
      var idx = 0
      var value = i
      val size = nroots
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
        if (next < nroots) {
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
        val left = nroots - v1(idx)
        val right = v2(idx)
        target(idx) = (left + right) % nroots
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
    def dotAbs2(v1: Array[Int], v2: Array[Int]): Real = {
      require(v1.length == v2.length)
      var idx = 0
      var acc = C.zero
      while (idx < v1.length) {
        val v1idx = v1(idx)
        val left = rootArray(if (v1idx == 0) 0 else (nroots - v1idx))
        val right = rootArray(v2(idx))
        acc = C.plus(acc, C.times(left, right))
        idx = idx + 1
      }

      C.abs2(acc)
    }

    // we know |a| <= d
    // so if orthEps >= d this is trivial
    // and everything is orthogonal
    val orthEpsIsTrivial: Boolean =
      (eps - realD).compare(0) >= 0

    /**
     * ||<u', v'>| - |<u, v>|| <= eps
     * but |<u, v>| = 0
     */
    def isOrth(r: Real): Boolean = {
      val diff = r.sqrt - eps
      // this is the closest rational x such that r = x/2^p
      diff(realBits).signum <= 0
    }

    // we know |a| <= d
    // so, ||a|- sqrt(d)| <= d + sqrt(d)
    //
    // so if ubEps >= d + sqrt(d) this is trivial
    // and everything is unbiased
    val ubEpsIsTrivial: Boolean =
      (eps - (realD + realD.sqrt)).compare(0) >= 0

    /**
     * ||<u', v'>| - |<u, v>|| <= eps
     * ||<u', v'>| - sqrt(d)| <= eps
     */
    def isUnbiased(r: Real): Boolean = {
      val diff = (r.sqrt - realD.sqrt).abs - eps
      // this is the closest rational x such that r = x/2^p
      diff(realBits).signum <= 0
    }

    def maybeOrth(v1: Array[Int], v2: Array[Int]): Boolean =
      // now, we want to see if
      // acc <= 4d sin^2(pi / n)
      isOrth(dotAbs2(v1, v2))

    def maybeUnbiased(v1: Array[Int], v2: Array[Int]): Boolean =
      // now, we want to see if
      // |acc - d| <= 4d sin^2(pi / n)
      isUnbiased(dotAbs2(v1, v2))

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

    // all permutations then convert back to int
    def perms(buffer: Array[Int], v0: Int): Iterator[Int] = {
      def loop(pos: Int): Iterator[Int] =
        // we always leave the last digit to be 0
        // so we can't swap the second to last position
        // with anything
        if (pos >= (buffer.length - 2)) Iterator.single(v0)
        else {
          // we can swap this position with any
          // position to the right
          (pos until (buffer.length - 1))
            .iterator
            .flatMap { swapIdx =>
              val inners = loop(pos + 1)
              // for each of the inners
              // we could swap in any position
              inners.map { v1 =>
                intToVector(v1, buffer)
                val tmp = buffer(swapIdx)
                buffer(swapIdx) = buffer(pos)
                buffer(pos) = tmp
                val v2 = vectorToInt(buffer)
                v2
              }
            }
        }

      loop(0)
    }

    def buildCacheFuture(fn: Real => Boolean)(implicit ec: ExecutionContext): Future[BitSet] = {
      // first we compute all the traces that are orthogonal
      // the java bitset doesn't box on access
      val bitset = new BitSet(standardCount)
      val fut = Future
        .traverse((0 until standardCount).grouped(2000).toList) { group =>
          Future {
            val tmp = new Array[Int](dim)
            group.foreach { v =>
              intToVector(v, tmp)
              // we always fix the last item to 0
              java.util.Arrays.sort(tmp, 0, dim - 1)
              val v1 = vectorToInt(tmp)
              if (v1 != v) {
                // this is not the "root" value
                ()
              }
              else {
                // this is the root value, compute the trace once and set all
                // the values
                val bitIsSet = fn(trace(tmp))

                if (bitIsSet) {
                  bitset.synchronized {
                    perms(tmp, v1).foreach { v =>
                      require(v < standardCount, s"error: $v >= $standardCount")
                      bitset.set(v)
                    }
                  }
                }
              }
            }
          }
        }

      fut.map(_ => bitset)
    }

    def buildCache(fn: Real => Boolean): BitSet =
      Await.result(buildCacheFuture(fn)(ExecutionContext.global), Inf)

    // this builds standardized bases:
    // to be orthogonal: you must also be orthogonal to 0
    // to be unbiased, you must be unbiased to 0
    //
    // return the first index in the set
    private def buildCachedFn(bitset: BitSet): () => Int => Int => Boolean = {
      // first we compute all the traces that are orthogonal

      val cp = conjProdInt

      () => {
        val intCP = cp()

        { n1: Int =>
          if (bitset.get(n1)) {

            { n2: Int =>

              bitset.get(n2) && {
                val n3 = intCP(n1, n2)
                bitset.get(n3)
              }
            }
          }
          else Function.const(false)(_: Int)
        }
      }

    }

    def nextFn(set: BitSet): Int => Int =
      { (i: Int) =>
        val res = i + 1
        if (res < standardCount) {
          val n = set.nextSetBit(res)
          if (n < 0) standardCount
          else n
        }
        else res
      }

    /**
     * These are all standardized Hadamards:
     * they have 0 in the last position (1)
     * and they all include the all 0 vector (which is omitted
     * in the response)
     */
    def allBasesFuture(orthSet: BitSet)(implicit ec: ExecutionContext): Future[List[Cliques.Family[Int]]] = {
      //if (orthEpsIsTrivial) throw new IllegalStateException(s"orthEps is trivial: $orthEps >= ${realD.pow(2)}")

      val fn = buildCachedFn(orthSet)
      val inc = nextFn(orthSet)
      // we use an array for the ints because it is more space efficient
      // than lists
      Cliques.async[Int](
        size = (dim - 1), // the number of items in a basis is the dimension, in addition to 0
        initNode = inc(0),
        incNode = inc,
        isLastNode = { i: Int => (standardCount - 1) <= inc(i) },
        fn)
    }

    private def cliqueSync(set: BitSet, size: Int): LazyList[Cliques.Family[Int]] = {
      val fn = buildCachedFn(set)
      val inc = nextFn(set)
      // we use an array for the ints because it is more space efficient
      // than lists
      Cliques.sync[Int](
        size = size, // the number of items in a basis is the dimension, in addition to 0
        initNode = inc(0),
        incNode = inc,
        isLastNode = { i: Int => (standardCount - 1) <= inc(i) },
        fn())
    }

    def allBasesSync(orthSet: BitSet): LazyList[Cliques.Family[Int]] =
      cliqueSync(orthSet, dim - 1)

    def allBases(orthSet: BitSet): List[Cliques.Family[Int]] =
      Await.result(allBasesFuture(orthSet)(ExecutionContext.global), Inf)

    /**
     * These are sets of mutually unbiased vectors.
     * This is an upper bound on unbiased bases because
     * selecting a single item from unbiased bases is a
     * set of unbiased vectors
     *
     * These are *standardized*: they are all unbiased to 0
     * and all have 0 in the final position
     */
    def allMubVectorsFuture(ubBitSet: BitSet, cliqueSize: Int)(implicit ec: ExecutionContext): Future[List[Cliques.Family[Int]]] = {
      val fn = buildCachedFn(ubBitSet)
      val inc = nextFn(ubBitSet)
      // we use an array for the ints because it is more space efficient
      // than lists

      Cliques.async[Int](
        size = (cliqueSize - 1), // the number of items in a basis is the dimension
        initNode = inc(0),
        incNode = inc,
        isLastNode = { i: Int => (standardCount - 1) <= inc(i) },
        fn)
    }

    // if there are cliqueSize, mubs, we are looking for cliqueSize - 1
    def allMubVectorsSync(ubBitSet: BitSet, cliqueSize: Int): LazyList[Cliques.Family[Int]] =
      cliqueSync(ubBitSet, cliqueSize - 1)

    def allMubVectors(ubBitSet: BitSet, cliqueSize: Int): List[Cliques.Family[Int]] =
      Await.result(allMubVectorsFuture(ubBitSet, cliqueSize)(ExecutionContext.global), Inf)

    type BasisF = Cliques.Family[Int]
    type Basis = List[Int]
    type Mubs = Cliques.Family[Basis]

    // transform all but the first with a the corresponding mub
    // we add back the 0 vector to the front in the results
    private def transformStdBasis(hs: Cliques.Family[BasisF], mubs: Cliques.Family.NonEmpty[Int], ubBitSet: BitSet): LazyList[Mubs] = {

      // TODO we are still using crossProduct
      // below which seems to be not leveraing the
      // fact that we can remove subtrees of bases that
      // are not fully unbiased to the mubs faster
      // e.g. any head basis that isn't unbiased
      // to all the mubs definitely won't work
      // so, we could filter first
      // or, if we can use cliqueMerge directly on hs and mubs
      // somehow we will save a massive amount of work
      // but we may need to generalize since hs
      // involves the cross-product somehow
      // maybe we need some kind of crossMerge function
      import Cliques.Family

      val cp = conjProdInt()

      val mub0 = mubs.head
      val hs1Opt =
          // The entire first basis has to be unbiased to the first mub
          // we can use that to trim down the search
          hs.collectHead { h0 =>
            h0.filter { h =>
              ubBitSet.get(cp(h, mub0))
            }
          }

      hs1Opt match {
        case None => LazyList.empty
        case Some(hs1) =>

          val mubWithZero = Family.NonEmpty(0, NonEmptyList(mubs, Nil))

          //
          Family
            .crossProduct(hs1)
            .flatMap { bases: Family[Basis] =>

              // the basis is a standard basis (missing the first all 0 vector)
              // the int is a MUB vector to be applied to this basis
              def areUnbiased(b0: (Basis, Int), b1: (Basis, Int)): Boolean = {
                // both bases are augmented with the 0 value
                // we switch the phase because we put it on the left
                val overall = cp(b1._2, b0._2)
                val v1s = (0 :: b1._1)
                (0 :: b0._1).forall { v0 =>
                  v1s.forall { v1 =>
                    ubBitSet.get(cp(overall, cp(v0, v1)))
                  }
                }
              }

              def toFull(b0: Basis, mub: Int): Basis = {
                // we have to do the conjugate twice
                val conjMub = cp(mub, 0)
                (0 :: b0).map { v =>
                  cp(conjMub, v)
                }
              }

              Cliques.Family.cliqueMerge(bases, mubWithZero)(areUnbiased(_, _))
                .map { mubF =>
                  mubF.map { case (b, i) => toFull(b, i) }
                }
            }
      }
    }

    /**
     * Generate all standard bases, then all sets of unbiased standard vectors.
     * Finally, try to assemble a set of MUBs from these:
     * H0, Z1 H1, Z2 H2, ...
     */
    def allMubsFuture(orthSet: BitSet, ubBitSet: BitSet, cnt: Int)(implicit ec: ExecutionContext): Future[List[List[List[Int]]]] = {

        def log[A](str: String, f: => Future[A]): Future[A] = {
          val start = System.currentTimeMillis()
          println(s"#starting: $str")
          val fut = f
          fut.flatMap { a =>
            Future {
              val end = System.currentTimeMillis()
              println(f"#done: $str (${(end - start)/1000.0}%.3f s)")
              a
            }
          }
        }
        val mubs = log("allMubVectorsFuture", allMubVectorsFuture(ubBitSet, cnt))
        // we can pick any cnt bases, and any (cnt - 1) unbiased vectors
        // to transform them. We have to include the phantom 0 vector
        def assemble(bases: List[Cliques.Family[Int]], mubV: List[Cliques.Family[Int]]): Future[List[List[List[Int]]]] = {
          require(bases.forall(_.cliqueSize == dim - 1), "invalid basis size")
          require(mubV.forall(_.cliqueSize == (cnt - 1)), "invalid mub size")

          val mubsCount = new AtomicLong(0L)
          val start = System.currentTimeMillis()
          val mubVLen = mubV.length

          def remaining(idx: Int, found: Long): Unit = {
            if ((idx < 10) || (idx % (mubVLen / 100) == 1)) {
              val end = System.currentTimeMillis()
              val idxD = idx.toDouble
              val currentRateMs = (idxD + 1)/(end - start)
              val remainingMs = (mubVLen - (idx + 1)) / currentRateMs
              val remainingSec = remainingMs / 1000

              println(f"#done: ${idxD/mubVLen}%2.2f, found: $found, ${remainingSec}%.1f sec remaining")
            }
          }
          Future.traverse(mubV.zipWithIndex) {
            case (ubv@Cliques.Family.NonEmpty(h, _), idx) =>
              Future {
                // these are all sets of cnt bases
                // in every possible order
                //
                // these are as cheap to compute as iterate so don't keep them
                // in memory
                val trans: Iterator[Mubs] =
                  Cliques.Family
                    .chooseN(cnt, bases)
                    .iterator
                    .flatMap { hs: Cliques.Family[Cliques.Family[Int]] =>
                      transformStdBasis(hs, ubv, ubBitSet).iterator
                    }

                val res: List[List[List[Int]]] =
                  trans
                    .flatMap(_.cliques)
                    .toList

                val thisCount = res.length
                val current = mubsCount.addAndGet(thisCount)
                if (current == thisCount) {
                  println(s"#found the first $current mubs")
                }

                remaining(idx, current)
                res
              }
            case (Cliques.Family.Empty, _) =>
              Future {
                val res: List[List[List[Int]]] =
                  bases.flatMap { fam =>
                    val withZero = Cliques.Family.NonEmpty(0, NonEmptyList(fam, Nil))
                    withZero.cliques.map(_ :: Nil).toList
                  }

                res
              }
          }
          .map(_.flatten)
        }

        log("allBasesFuture", allBasesFuture(orthSet)).zip(mubs)
          .flatMap {
            case (bases, mubV) =>
              println("#calling assemble")
              assemble(bases, mubV)
          }
      }

    def allMubs(orthSet: BitSet, ubBitSet: BitSet, cnt: Int): List[List[List[Int]]] =
      Await.result(allMubsFuture(orthSet, ubBitSet, cnt)(ExecutionContext.global), Inf)
  }

  // return lists of exactly n items where each item
  // comes from an index in items.
  // we do allow repeats, so we choose with replacement
  def chooseN[A](n: Int, items: Iterable[A]): Iterator[List[A]] = {

    def loop(n: Int): Iterator[List[A]] =
      if (n <= 0) Iterator.single(Nil)
      else {
        // we could pick any first item
        // followed by picking n-1 from any items
        items.iterator.flatMap { h =>
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

  final def runInfo[N <: BinNat, C](
    space: Space[N, C],
    bases: Option[BitSet],
    runSync: Boolean,
    mubsOpt: Option[(Int, BitSet)]
    )(implicit ec: ExecutionContext): Future[Unit] = {

    println(s"# $space")
    val f1 = bases match {
      case Some(orthBitSet) =>
        def showBases(bases0: Iterable[Cliques.Family[Int]]): Future[Unit] =
          Future {
            val basesLen = bases0.foldLeft(0L)(_ + _.cliqueCount)

            println(s"there are ${basesLen} bases")
            mubsOpt.foreach { case (mub, _) =>
              val sl = SafeLong(basesLen)
              val comb = sl.pow(mub)
              println(s"we need to try $comb combinations of these, doing a total of ${comb * (mub * (mub - 1)/2)} inner products")
            }
          }

        if (runSync) showBases(space.allBasesSync(orthBitSet))
        else space.allBasesFuture(orthBitSet).flatMap(showBases)
      case None =>
        Future.unit
    }

    val f2 = mubsOpt match {
      case Some((cliqueSize, ubBitSet)) =>
        def showMub(bases0: Iterable[Cliques.Family[Int]]): Future[Unit] =
          Future {
            println("showMub...")
            if (bases0.isEmpty) {
              println(s"there are 0 sets of mutually unbiased vectors of clique size = $cliqueSize")
            }
            else {
              println(s"nonEmpty... computing.")
              val basesLen = bases0.foldLeft(0L)(_ + _.cliqueCount)

              println(s"there are ${basesLen} sets of mutually unbiased vectors of clique size = $cliqueSize")
            }
          }


        if (runSync) showMub(space.allMubVectorsSync(ubBitSet, cliqueSize))
        else space.allMubVectorsFuture(ubBitSet, cliqueSize).flatMap(showMub)
      case None =>
        Future.unit
    }

    f1.zip(f2).map(_ => ())
  }

  def writeTable[N <: BinNat, C](
    space: Space[N, C],
    isOrthTable: Boolean,
    dos: DataOutputStream)(implicit ec: ExecutionContext): Future[Unit] = {
    val fn = if (isOrthTable) space.isOrth(_) else space.isUnbiased(_)

    space.buildCacheFuture(fn)
      .flatMap { bitset =>
        val sc = space.standardCount
        dos.writeInt(space.dim)
        dos.writeInt(sc)
        dos.writeBoolean(isOrthTable)
        dos.writeInt(bitset.cardinality)
        // we use a delta encoding, which will
        // compress better if we compress larger tables
        Future {
          var prev = 0
          var idx = bitset.nextSetBit(0)
          while ((idx < sc) && (idx >= 0)) {
            dos.writeInt(idx - prev)
            prev = idx
            idx = bitset.nextSetBit(idx + 1)
          }

          dos.flush()
        }
      }
  }

  def readTable[N <: BinNat, C](
    space: Space[N, C],
    isOrthTable: Boolean,
    ios: DataInputStream): BitSet = {
    val fileDim = ios.readInt()
    val fileSc = ios.readInt()
    val fileIsOrth = ios.readBoolean()
    val card = ios.readInt()

    if ((fileDim != space.dim) || (fileSc != space.standardCount) || (isOrthTable != fileIsOrth) || (card < 0)) {
      throw new IllegalArgumentException(
        s"expected (dim = ${space.dim}, standardCount = ${space.standardCount}, isOrth = $isOrthTable, card >= 0)\n\n" +
        s"but found (dim = $fileDim, standardCount = $fileSc, isOrth = $fileIsOrth, card = $card)")
    }

    // past here we know things match
    val bitset = new BitSet(fileSc)
    var idx = 0
    var prev = 0
    while (idx < card) {
      val next = ios.readInt()
      prev += next
      bitset.set(prev)
      idx = idx + 1
    }

    bitset
  }

  def readPath[N <: BinNat, C](space: Space[N, C], isOrth: Boolean, path: Path): BitSet = {
    val input = new FileInputStream(path.toFile)
    val gz = new GZIPInputStream(input)
    val data = new DataInputStream(gz)

    try VectorSpace.readTable(space, isOrth, data)
    finally data.close()
  }

  def search0[N <: BinNat, C](
    space: Space[N, C],
    orthSet: BitSet,
    mubSet: BitSet,
    mubs: Int,
    limit: Option[Int])(implicit ec: ExecutionContext): Future[Unit] = {

    println(s"# $space")
    space.allMubsFuture(orthSet, mubSet, mubs)
      .flatMap { mubsVector0 =>
        Future {
          println(s"# found: ${mubsVector0.length}")

          val mubsVector = limit.fold(mubsVector0)(mubsVector0.take(_))
          var idx = 0
          val ary = new Array[Int](space.dim)

          mubsVector.foreach { clique =>
            def showBasis(v: List[List[Int]]): String = {
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
        }
      }
  }

  def search[N <: BinNat, C](
    space: Space[N, C],
    orthSet: BitSet,
    mubSet: BitSet,
    mubs: Int,
    limit: Option[Int])(implicit ec: ExecutionContext): Future[Unit] = {

    val cp = space.conjProdInt

    val nextFn: Int => Option[Int] =
      { i0 =>
        val i1 = i0 + 1
        if (i1 < space.standardCount) Some(i1)
        else None
      }

    Future {
      println(s"# $space")
      val mubBuild = new MubBuild.Instance(
        space.dim,
        space.standardCount,
        mubs,
        cp,
        orthSet,
        mubSet,
        nextFn)

      println(s"found: ${mubBuild.firstCompleteExample}")
    }
  }


  def quantBoundSearch[N <: BinNat, C](
    space: Space[N, C],
    seed: Long,
    trials: Int)(implicit ec: ExecutionContext): Future[Unit] = {

      require(trials > 0)

      val rng = new java.util.Random(seed)

      // this is a root of unity
      def nextC(): Complex[Real] = {
        // return exp(2 * pi * i *phi)
        val theta = Real(2 * rng.nextDouble()) * Real.pi
        Complex(Real.cos(theta), Real.sin(theta))
      }

      def nextV(): List[Complex[Real]] =
        (0 until (space.dim - 1))
          .iterator
          .map { _ => nextC() }
          .toList

      // do this outside of the future since we mutate rng
      val pairs = (0 until trials).map { _ => (nextV(), nextV()) }

      // now compute the gaps
      Future.traverse(pairs) { case (v1, v2) =>
        Future(space.quantizationBoundGap(v1, v2).doubleValue())
      }
      .map { gaps =>

        val minGap = gaps.min
        val maxGap = gaps.max
        val totalGap = gaps.sum
        println(s"minGap = $minGap")
        println(s"maxGap = $maxGap")
        println(s"aveGap = ${totalGap / trials}")
      }
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

    val threads: Opts[(ExecutionContext => Unit) => Unit] =
      Opts.option[Int]("threads", "number of threads to use, default = number of processors")
        .withDefault(Runtime.getRuntime().availableProcessors())
        .map { t =>
          { (callback: ExecutionContext => Unit) =>
            val eserv = Executors.newFixedThreadPool(t)
            try {
              val ec = ExecutionContext.fromExecutorService(eserv)
              callback(ec)
            }
            finally {
              eserv.shutdown()
            }
          }
        }

    val root = Opts.option[Int]("root", "what root of unity")
      .mapValidated { d =>

        val validSizes: Set[Int] =
          Set(1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 24, 27, 32)

        if (validSizes(d)) Validated.valid {
          d match {
            case 1 => { (d: Int, bits: Int) => new Space[BinNat._1, Cyclotomic.L1](d, bits) }
            case 2 => { (d: Int, bits: Int) => new Space[BinNat._2, Cyclotomic.L2](d, bits) }
            case 3 => { (d: Int, bits: Int) => new Space[BinNat._3, Cyclotomic.L3](d, bits) }
            case 4 => { (d: Int, bits: Int) => new Space[BinNat._4, Cyclotomic.L4](d, bits) }
            case 6 => { (d: Int, bits: Int) => new Space[BinNat._6, Cyclotomic.L6](d, bits) }
            case 8 => { (d: Int, bits: Int) => new Space[BinNat._8, Cyclotomic.L8](d, bits) }
            case 9 => { (d: Int, bits: Int) => new Space[BinNat._9, Cyclotomic.L9](d, bits) }
            case 12 => { (d: Int, bits: Int) => new Space[BinNat._12, Cyclotomic.L12](d, bits) }
            case 16 => { (d: Int, bits: Int) => new Space[BinNat._16, Cyclotomic.L16](d, bits) }
            case 18 => { (d: Int, bits: Int) => new Space[BinNat._18, Cyclotomic.L18](d, bits) }
            case 24 => { (d: Int, bits: Int) => new Space[BinNat._24, Cyclotomic.L24](d, bits) }
            case 27 => { (d: Int, bits: Int) => new Space[BinNat._27, Cyclotomic.L27](d, bits) }
            case 32 => { (d: Int, bits: Int) => new Space[BinNat._32, Cyclotomic.L32](d, bits) }
          }
        }
        else Validated.invalidNel(s"invalid root: $d. valid values: ${validSizes.toList.sorted}")
      }

    val orthTab = Opts.option[Path]("orth_tab", "path to orthogonality table")
    val ubTab = Opts.option[Path]("ub_tab", "path to unbiasedness table")
    val tableOpts: Opts[(Path, Path)] = orthTab.product(ubTab)

    val spaceOpt =
      realBits
        .product(dim)
        .product(root)
        .map { case ((b, d), fn) => fn(d, b) }

    val search =
      (spaceOpt, goalMubs.orNone, threads, tableOpts, Opts.option[Int]("limit", "limit printing out to this many mubs").orNone)
        .mapN { case (space, mubsOpt, cont, (orthPath, ubPath), limit) =>
          // dim is the most we can get
          val mubs = mubsOpt.getOrElse(space.dim)

          cont { implicit ec =>
            val orthBS = VectorSpace.readPath(space, true, orthPath)
            val ubBS = VectorSpace.readPath(space, false, ubPath)
            Await.result(VectorSpace.search(space, orthBS, ubBS, mubs, limit), Inf)
          }
        }


    val info =
      (spaceOpt,
        threads,
        (Opts.flag("bases", "compute all the standard bases and give the size") *> orthTab).orNone,
        Opts.flag("sync", "run synchronous (less memory, but no concurrency)").orFalse,
        (goalMubs.product(ubTab)).orNone)
        .mapN { (space, cont, bases0, runSync, mubsOpt0) =>
          cont { implicit ec =>
            val bases = bases0.map { path =>
              VectorSpace.readPath(space, true, path)
            }
            val mubsOpt = mubsOpt0.map { case (n, path) =>
              (n, VectorSpace.readPath(space, false, path))
            }
            Await.result(VectorSpace.runInfo(space, bases, runSync, mubsOpt), Inf)
          }
        }

    val writeTable =
      (spaceOpt,
        threads,
        Opts.flag("orth", "build the orthTable").as(true)
          .orElse(Opts.flag("unbiased", "build the unbiasedness table").as(false)),
        Opts.option[Path]("output", "file to write to"))
        .mapN { (space, cont, isOrth, path) =>
          cont { implicit ec =>
            val output = new FileOutputStream(path.toFile)
            val gz = new GZIPOutputStream(output)
            val data = new DataOutputStream(gz)
            val fut = VectorSpace.writeTable(space, isOrth, data)
            try Await.result(fut, Inf)
            finally {
              data.close()
            }
          }
        }

    val quantSearch = {
      (spaceOpt,
        threads,
        Opts.option[Long]("seed", "the seed to use, or use nanoTime").orElse(Opts(System.nanoTime())),
        Opts.option[Int]("count", "the number of pairs to check, default = 1000").orElse(Opts(1000)))
        .mapN { (space, cont, seed, cnt) =>
          cont { implicit ec =>
            Await.result(VectorSpace.quantBoundSearch(space, seed, cnt), Inf)
          }
        }
    }

    Opts.subcommand("search", "run a search for mubs")(search)
      .orElse(
        Opts.subcommand("info", "show the count of bases and or mub vectors")(info))
      .orElse(
        Opts.subcommand("write_table", "compute an orthogonality/unbiasedness table and write to file")(writeTable))
      .orElse(
        Opts.subcommand("quant_search", "explore the tightness of the quantization bound")(quantSearch))
  }

)
