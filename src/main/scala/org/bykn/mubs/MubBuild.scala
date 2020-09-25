package org.bykn.mubs

import cats.data.OneAnd
import java.util.BitSet
import scala.collection.immutable.SortedSet

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
  type Bases = Map[Int, (List[Int], SortedSet[Int])]

  class Instance(
    val dim: Int,
    val standardCount: Int,
    val goalHads: Int,
    cpFn: (Int, Int) => Int,
    orthBitSet: BitSet,
    ubBitSet: BitSet) {

    import scala.math.pow

    val pOrth = orthBitSet.cardinality.toDouble / standardCount
    val pUb = ubBitSet.cardinality.toDouble / standardCount

    println(s"pOrth = $pOrth, pUb = $pUb")

    def orthFn(i: Int, j: Int): Boolean =
      orthBitSet.get(cpFn(i, j))

    def unbiasedFn(i: Int, j: Int): Boolean =
      ubBitSet.get(cpFn(i, j))

    def bitSetToSet(bitset: BitSet): SortedSet[Int] = {
      var idx = bitset.nextSetBit(0)
      val bldr = SortedSet.newBuilder[Int]
      while ((idx < standardCount) && (idx >= 0)) {
        bldr += idx
        idx = bitset.nextSetBit(idx + 1)
      }
      bldr.result()
    }

    val orthToZero: SortedSet[Int] = bitSetToSet(orthBitSet)
    val ubToZero: SortedSet[Int] = bitSetToSet(ubBitSet)

    def forBasis(bases: Bases, i: Int): List[Int] =
      bases(i)._1

    def addVector(bases: Bases, i: Int, vec: Int): Option[Bases] = {
      val basisi = bases(i)._1
      val mini = if (basisi.isEmpty) vec else basisi.last

      bases
        .toList
        .traverse {
          case (basis, (vecs, s)) =>
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

            if (!sortBasis) None
            else if (basis == i) {
              // we add in sorted order
              val s0 = s.rangeFrom(vec + 1)
              val s1 = s0.filter(orthFn(vec, _))

              if ((s1.size + vecs.length + 1) < dim) {
                // we can't reach a complete set
                None
              }
              else {
                val v1 = vec :: vecs
                Some((basis, (v1, s1)))
              }
            }
            else {
              val s1 = s.filter(unbiasedFn(vec, _))

              if ((s1.size + vecs.length) < dim) {
                // we can't reach a complete set
                None
              }
              else {
                Some((basis, (vecs, s1)))
              }
            }
        }
        .map(_.toMap)
    }

    private[this] val hads = (0 until goalHads).toList

    type TreeB = Tree[LazyList, Bases]

    def firstComplete(b: TreeB): Option[Bases] =
      b match {
        case Tree.Empty() => None
        case Tree.NonEmpty(root, children) =>
          if (children.isEmpty) Some(root)
          else children.flatMap(firstComplete).headOption
      }

    // this is true, we found a complete set, we might as well stop
    def isComplete(b: Bases): Boolean =
      hads.forall { basis =>
        forBasis(b, basis).length == dim
      }

    def extensionSize(b: Bases, i: Int): Int =
      b(i)._2.size

    // fully extend an incomplete basis
    private def extendBasis(b: Bases, i: Int, depth: Int): Option[TreeB] = {
      val orthVectors: List[Int] = forBasis(b, i)

      if (orthVectors.length == dim) {
        // we know this isn't complete and can't be
        // completed in this direction
        None
      }
      else {
        val branchWidth = b(i)._2.size
        // make this a def so the head can be GCe'd below
        def choices = b(i)._2.to(LazyList)

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
        // we have to check all,
        // we might as well try to find the most probable
        // first
        val greatestToLeast =
          hads.sortBy(extensionSize(b, _)).reverse

        val children = greatestToLeast
          .to(LazyList)
          .flatMap { basis =>
            extendBasis(b, basis, depth)
          }
          .collect { case n@Tree.NonEmpty(_, _) => n }

        if (children.nonEmpty) Some(Tree.NonEmpty(b, children))
        else None
      }
    }

    val initBasis: Bases =
      hads.map {
        case 0 => (0, (0 :: Nil, orthToZero))
        case i => (i, (Nil, ubToZero))
      }
      .toMap

    // each Int is a vector encoded as a single Int
    def makeBases(bases: List[List[Int]]): Option[Bases] = {
      bases.foreach { lst =>
        if (lst.length > dim) throw new IllegalArgumentException(s"expected basis size <= $dim: $lst")
        lst.foreach { v =>
          if ((v < 0) || (standardCount < v)) {
            throw new IllegalArgumentException(s"expected encoded vectors in [0, $standardCount), found: $v in $lst")
          }
        }
      }

      if (bases.length != goalHads) {
        throw new IllegalArgumentException(s"expected $goalHads bases, found: ${bases.length} in $bases")
      }

      bases.map(_.sorted) match {
        case (Nil | (Nil :: _)) => None
        case (h :: tail) :: brest =>
          def toSS(it: Iterator[Int]): SortedSet[Int] = {
            val ss = SortedSet.newBuilder[Int]
            ss ++= it
            ss.result()
          }

          val orthToH = toSS((0 until standardCount).iterator.filter { left => orthBitSet.get(cpFn(left, h)) })
          val ubToH = toSS((0 until standardCount).iterator.filter { left => ubBitSet.get(cpFn(left, h)) })

          val b0 = (0 until goalHads).foldLeft(Map.empty: Bases) { (m, basis) =>
            if (basis == 0) m.updated(0, (h :: Nil, orthToH))
            else m.updated(basis, (Nil, ubToH))
          }

        (tail :: brest).zipWithIndex.foldM(b0) { case (bases, (vectors, basis)) =>
          vectors.foldM(b0) { (b, v) =>
            addVector(b, basis, v)
          }
        }
      }
    }

    lazy val fullBases: Option[Tree.NonEmpty[LazyList, Bases]] = extendFully(initBasis, 0)

    lazy val firstCompleteExample: Option[Map[Int, List[Int]]] =
      fullBases.flatMap(firstComplete(_))
        .map(_.map { case (k, (v, _)) => (k, v) })

    lazy val completeCount: Long = {
      def completeCountOf(n: Tree[LazyList, Bases]): Long =
        n match {
          case Tree.Empty() => 0L
          case Tree.NonEmpty(h, cs) =>
            val rest = cs.foldLeft(0L) { (acc, t) => acc + completeCountOf(t) }
            val hcount = if (isComplete(h)) 1L else 0L
            hcount + rest
        }

      fullBases match {
        case None => 0
        case Some(t) => completeCountOf(t)
      }
    }
  }
}
