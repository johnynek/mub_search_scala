package org.bykn.mubs

import cats.data.OneAnd
import java.util.BitSet
import org.typelevel.paiges.Doc
import java.util.concurrent.atomic.AtomicLong
import scala.concurrent.{ExecutionContext, Future}

import cats.implicits._

/**
 * The approach of MUB build is to build a tree
 * of extensions to the empty set such that each
 * vector added to a basis maintains the MUB
 * property. The idea is to add in order of
 * removing the most expected possible extensions
 * (based on the expected probability of a random
 * edge being unbiased or orthogonal).
 */
object MubBuild {

  sealed abstract class Tree[F[_], A]
  object Tree {
    final case class Empty[F[_], A]() extends Tree[F, A]
    final case class NonEmpty[F[_], A](root: A, children: F[NonEmpty[F, A]]) extends Tree[F, A]
  }

  /*
   * For each basis (key) we have the current set of values
   * and all possible extensions
   */
  type Candidates = Array[Int]
  type Bases = Array[(List[Int], Candidates)]

  class Instance(
    val dim: Int,
    val standardCount: Int,
    val goalHads: Int,
    cpFn: (Int, Int) => Int,
    orthBitSet: BitSet,
    ubBitSet: BitSet,
    optPart: Option[Partitioned]) {

    import scala.math.pow

    val pOrth = orthBitSet.cardinality.toDouble / standardCount
    val pUb = ubBitSet.cardinality.toDouble / standardCount
    private val addVectorCount = new AtomicLong(0L)

    println(s"pOrth = $pOrth, pUb = $pUb")

    private val filterFn = optPart match {
      case Some(p) => { (i: List[Int]) => p.selectByHash(i) }
      case None => { (i: List[Int]) => true }
    }

    def orthFn(i: Int, j: Int): Boolean =
      orthBitSet.get(cpFn(i, j))

    def docBases(bases: Bases): Doc = {
      val parts = (0 until goalHads).map { idx =>
        val (basis, candidates) = bases(idx)
        Doc.text(s"$idx. ") + Doc.char('[') +
          (Doc.line + Doc.intercalate(Doc.line, basis.map(Doc.str(_))) + Doc.line).nested(4).grouped +
          Doc.char(']') + Doc.text(s" candidate_size=${candidates.length}")
      }
      Doc.intercalate(Doc.line, parts)
    }

    def unbiasedFn(i: Int, j: Int): Boolean =
      ubBitSet.get(cpFn(i, j))

    private[this] val EmptyCandidates: Candidates = Array.emptyIntArray

    private def bitSetToArray(bitset: BitSet): Candidates = {
      val res = new Array[Int](bitset.cardinality())
      var write = 0
      var idx = bitset.nextSetBit(0)
      while ((idx < standardCount) && (idx >= 0)) {
        res(write) = idx
        write = write + 1
        idx = bitset.nextSetBit(idx + 1)
      }
      if (write == res.length) res
      else java.util.Arrays.copyOf(res, write)
    }

    private def firstIndexGte(cands: Candidates, minVal: Int): Int = {
      val raw = java.util.Arrays.binarySearch(cands, minVal)
      if (raw >= 0) raw
      else -raw - 1
    }

    private def filterCandidates(
      cands: Candidates,
      startIdx: Int,
      vec: Int,
      useOrth: Boolean): Candidates = {

      val len = cands.length
      if (startIdx >= len) EmptyCandidates
      else {
        var out = new Array[Int](math.min(128, len - startIdx))
        var size = 0
        var idx = startIdx

        while (idx < len) {
          val cand = cands(idx)
          val accept =
            if (useOrth) orthFn(vec, cand)
            else unbiasedFn(vec, cand)

          if (accept) {
            if (size == out.length) {
              val nextLen =
                if (out.length < 8) 8
                else out.length * 2
              out = java.util.Arrays.copyOf(out, nextLen)
            }
            out(size) = cand
            size = size + 1
          }
          idx = idx + 1
        }

        if (size == 0) EmptyCandidates
        else if (size == out.length) out
        else java.util.Arrays.copyOf(out, size)
      }
    }

    private def filterOrthCandidates(cands: Candidates, vec: Int): Candidates = {
      val startIdx = firstIndexGte(cands, vec + 1)
      filterCandidates(cands, startIdx, vec, useOrth = true)
    }

    private def filterUnbiasedCandidates(cands: Candidates, vec: Int): Candidates =
      filterCandidates(cands, 0, vec, useOrth = false)

    private def candidatesFromPredicate(fn: Int => Boolean): Candidates = {
      var out = new Array[Int](1024)
      var size = 0
      var idx = 0
      while (idx < standardCount) {
        if (fn(idx)) {
          if (size == out.length) {
            out = java.util.Arrays.copyOf(out, out.length * 2)
          }
          out(size) = idx
          size = size + 1
        }
        idx = idx + 1
      }
      if (size == out.length) out
      else java.util.Arrays.copyOf(out, size)
    }

    val orthToZero: Candidates = bitSetToArray(orthBitSet)
    val ubToZero: Candidates = bitSetToArray(ubBitSet)

    def forBasis(bases: Bases, i: Int): List[Int] =
      bases(i)._1

    private def toBasisMap(b: Bases): Map[Int, List[Int]] =
      (0 until goalHads).iterator.map { i =>
        (i, b(i)._1)
      }
      .toMap

    def addVector(bases: Bases, i: Int, vec: Int): Option[Bases] = {
      val currentCount = addVectorCount.incrementAndGet()

      if (currentCount % 10000000L == 0L) {
        val debugMsg = docBases(bases) + Doc.line +
          Doc.text(s"addVectorCount=$currentCount") + Doc.line +
          Doc.text(s"instant=${java.time.Instant.now()}") 

        println(debugMsg.render(80))
        println("")
      }

      val basisi = bases(i)._1
      val mini = if (basisi.isEmpty) vec else basisi.last

      val next = new Array[(List[Int], Candidates)](goalHads)
      var basis = 0
      while (basis < goalHads) {
        val (vecs, s) = bases(basis)
        val sortBasis =
          if (0 < basis) {
            if (basis < i) {
              // the min value of this
              // basis has to be <= vec
              val bprev = bases(basis - 1)._1
              bprev.isEmpty || (bprev.last <= mini)
            }
            else if (basis > i) {
              val bprev = bases(basis - 1)._1
              bprev.isEmpty || (mini <= bprev.last)
            }
            else true
          }
          else true

        if (!sortBasis) return None
        else if (basis == i) {
          // we add in sorted order
          val nextLen = vecs.length + 1
          val v1 = vec :: vecs
          // Partition exactly once at a canonical point so workers are
          // disjoint/exhaustive over branches. Re-checking at deeper levels
          // can prune valid branches from every worker.
          if ((basis == 0) && (nextLen == 3) && !filterFn(v1)) return None

          if (nextLen >= dim) {
            next(basis) = (v1, EmptyCandidates)
          }
          else {
            val s1 = filterOrthCandidates(s, vec)
            if ((s1.length + nextLen) < dim) {
              // we can't reach a complete set
              return None
            }
            next(basis) = (v1, s1)
          }
        }
        else {
          val s1 = filterUnbiasedCandidates(s, vec)
          if ((s1.length + vecs.length) < dim) {
            // we can't reach a complete set
            return None
          }

          next(basis) = (vecs, s1)
        }
        basis = basis + 1
      }

      Some(next)
    }

    type TreeB = Tree[LazyList, Bases]

    def firstComplete(b: TreeB): Option[Bases] =
      b match {
        case Tree.Empty() => None
        case Tree.NonEmpty(root, children) =>
          if (children.isEmpty) Some(root)
          else children.flatMap(firstComplete).headOption
      }

    // this is true, we found a complete set, we might as well stop
    def isComplete(b: Bases): Boolean = {
      var basis = 0
      while (basis < goalHads) {
        if (forBasis(b, basis).length != dim) return false
        basis = basis + 1
      }
      true
    }

    def extensionSize(b: Bases, i: Int): Int =
      b(i)._2.length

    // fully extend an incomplete basis
    private def extendBasis(b: Bases, i: Int, depth: Int): Option[TreeB] = {
      val orthVectors: List[Int] = forBasis(b, i)

      if (orthVectors.length == dim) {
        // we know this isn't complete and can't be
        // completed in this direction
        None
      }
      else {
        val branchWidth = b(i)._2.length
        // make this a def so the head can be GCe'd below
        def choices = b(i)._2.iterator.to(LazyList)

        def extension(vec: Int): Option[Tree.NonEmpty[LazyList, Bases]] =
          addVector(b, i, vec).flatMap(extendFully(_, depth + 1))

        if (depth < 12) {
          //println(s"#depth = $depth, basis = $i, width = $branchWidth")
        }

        val start = System.nanoTime()
        val children = choices.flatMap(extension(_))
        val isEmpty = children.isEmpty
        val diff = System.nanoTime() - start

        if (depth < 12) {
          //println(s"#depth = $depth, basis = $i, width = $branchWidth, time = ${diff.toDouble / 1e6}ms")
        }

        if (isEmpty) None
        else Some(Tree.NonEmpty(b, children))
      }
    }

    def extendFully(b: Bases, depth: Int): Option[Tree.NonEmpty[LazyList, Bases]] = {
      if (isComplete(b)) Some(Tree.NonEmpty[LazyList, Bases](b, LazyList.empty))
      else {
        // we can choose the order in which we search. We don't have to search all of the bases
        // we can select which of the bases we search next

        var smallestBranch = -1
        var smallestSize = Int.MaxValue
        var i = 0
        while (i < goalHads) {
          val cnt = extensionSize(b, i)
          if ((cnt > 0) && (cnt < smallestSize)) {
            smallestBranch = i
            smallestSize = cnt
          }
          i = i + 1
        }

        if (smallestBranch < 0) None
        else {
          extendBasis(b, smallestBranch, depth).flatMap {
            case n @ Tree.NonEmpty(_, _) =>
              Some(Tree.NonEmpty(b, LazyList(n)))
            case _ => None
          }
        }

        /*
        val greatestToLeast =
          // we have to check all,
          // we might as well try to find the most probable
          // first, note we can't stop early on these
          hads.sortBy(extensionSize(b, _)).reverse

        val children = greatestToLeast
          .to(LazyList)
          .flatMap { basis =>
            extendBasis(b, basis, depth)
          }
          .collect { case n@Tree.NonEmpty(_, _) => n }

        if (children.nonEmpty) Some(Tree.NonEmpty(b, children))
        else None
        */
      }
    }

    val initBasis: Bases =
      Array.tabulate(goalHads) {
        case 0 => (0 :: Nil, orthToZero)
        case _ => (Nil, ubToZero)
      }


    /**
     * This allows you to manually construct a basis and then search for extensions to the bases
     */
    def fromVectBasis[L <: BinNat, N <: BinNat, C](bases: List[List[Vect[L, N, C]]])(implicit C: Cyclotomic[N, C], L: BinNat.FromType[L]): Bases = {
      val lenInt = L.value.toBigInt.toInt
      if (lenInt != dim)
        throw new IllegalArgumentException(s"expected vector length to be $dim found $lenInt")

      val nInt = C.roots.length
      val size = BigInt(nInt).pow(L.value.toBigInt.toInt - 1).toInt

      if (size != standardCount)
        throw new IllegalArgumentException(s"expected Int embedding space to be $standardCount found $size")

      @annotation.tailrec
      def toInt(c: C, idx: Int): Int =
        if (C.roots(idx) == c) idx
        else toInt(c, idx + 1)

      def vectToInt(v: Vect[L, N, C]): Int = {
        val last = toInt(v(lenInt - 1), 0)
        if (last != 0) throw new IllegalArgumentException(s"expected last index to be unity in $v")

        var idx = lenInt - 1
        var acc = 0
        while (idx > 0) {
          idx = idx - 1
          acc = acc * nInt + toInt(v(idx), 0)
        }
        return acc
      }

      makeBases(bases.map(_.map(vectToInt))) match {
        case Right(bases) => bases
        case Left(message) => throw new IllegalArgumentException(s"bases: $bases did not form a valid basis.\n\n$message")
      }
    }

    // each Int is a vector encoded as a single Int
    def makeBases(bases: List[List[Int]]): Either[String, Bases] = {
      bases.foreach { lst =>
        if (lst.length > dim) throw new IllegalArgumentException(s"expected basis size <= $dim: $lst")
        lst.foreach { v =>
          if ((v < 0) || (standardCount < v)) {
            throw new IllegalArgumentException(s"expected encoded vectors in [0, $standardCount), found: $v in $lst")
          }
        }
      }

      if (bases.length > goalHads) {
        throw new IllegalArgumentException(s"expected <= $goalHads bases, found: ${bases.length} in $bases")
      }
      // add some empty bases
      val empty = List.fill(goalHads - bases.length)(List.empty[Int])

      def sortFn(ls: List[Int]): Int =
        if (ls.isEmpty) Int.MaxValue
        else ls.min

      (bases ::: empty)
        .map(_.sorted)
        .sortBy(sortFn) match {
        case (Nil | (Nil :: _)) => Left("did not expect empty, or empty lists early")
        case (h :: tail) :: brest =>
          val orthToH = candidatesFromPredicate { left => orthBitSet.get(cpFn(left, h)) }
          val ubToH = candidatesFromPredicate { left => ubBitSet.get(cpFn(left, h)) }

          val b0: Bases =
            Array.tabulate(goalHads) {
              case 0 => (h :: Nil, orthToH)
              case _ => (Nil, ubToH)
            }

        (tail :: brest).zipWithIndex.foldM(b0) { case (bases, (vectors, basis)) =>
          vectors.foldM(bases) { (b, v) =>
            addVector(b, basis, v) match {
              case Some(b1) => Right(b1)
              case None => Left(s"could not do: addVector($b, $basis, $v)")
            }
          }
        }
      }
    }

    def findFirstCompleteExampleFrom(b: Bases): Option[Map[Int, List[Int]]] =
      extendFully(b, 0)
        .flatMap(firstComplete(_))
        .map(toBasisMap(_))

    case class Result(fullBases: List[Tree.NonEmpty[LazyList, Bases]]) {
      lazy val firstCompleteExample: Option[Map[Int, List[Int]]] =
        fullBases.flatMap(firstComplete(_))
          .map(toBasisMap(_))
          .headOption

      lazy val completeCount: Long = {
        def completeCountOf(n: Tree[LazyList, Bases]): Long =
          n match {
            case Tree.Empty() => 0L
            case Tree.NonEmpty(h, cs) =>
              val rest = cs.foldLeft(0L) { (acc, t) => acc + completeCountOf(t) }
              val hcount = if (isComplete(h)) 1L else 0L
              hcount + rest
          }

        fullBases.iterator.map { t =>
          completeCountOf(t)
        }
        .sum
      }
    }

    // Run this synchonously to get the result
    def syncResult: Result = Result(extendFully(initBasis, 0).toList)

    def asyncResult(threads: Int)(implicit ec: ExecutionContext): Future[Result] =
      if (threads == 1) Future(syncResult)
      else {
        require(threads > 0, s"require threads $threads > 0")

        // round up by adding 1
        val chunkSize = (orthToZero.length / threads) + 1
        require(chunkSize * threads >= orthToZero.length)

        val nextList = orthToZero

        Future.traverse((0 until threads).toVector) { part =>
          Future {
            val offset = chunkSize * part

            val end = math.min(offset + chunkSize, nextList.length)
            val bldr = List.newBuilder[Tree.NonEmpty[LazyList, Bases]]
            var idx = offset
            while (idx < end) {
              addVector(initBasis, 0, nextList(idx))
                .flatMap(extendFully(_, 1))
                .foreach { t =>
                  bldr += t
                }
              idx = idx + 1
            }

            bldr.result()
          }
        }
        .map(rs => Result(rs.toList.flatten))
    }
  }
}
