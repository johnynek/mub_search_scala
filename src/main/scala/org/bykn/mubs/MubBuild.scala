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
    cp: () => (Int, Int) => Int,
    orthBitSet: BitSet,
    ubBitSet: BitSet,
    next: Int => Option[Int]) {

    import scala.math.pow

    val pOrth = orthBitSet.cardinality.toDouble / standardCount
    val pUb = ubBitSet.cardinality.toDouble / standardCount

    println(s"pOrth = $pOrth, pUb = $pUb")

    private[this] val cpFn = cp()
    def orthFn(i: Int, j: Int): Boolean =
      orthBitSet.get(cpFn(i, j))

    def unbiasedFn(i: Int, j: Int): Boolean =
      ubBitSet.get(cpFn(i, j))

    // all vectors ABOVE init (init is not included)
    // 0 is safe because we start building with 0
    // included
    def allVectorsFrom(init: Int): LazyList[Int] =
      LazyList.iterate(next(init))(_.flatMap(next))
        .takeWhile(_.isDefined)
        .map(_.get)

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

    def addVector(bases: Bases, i: Int, vec: Int): Option[Bases] =
      //
      // TODO: we are not maintaining the sorted MUB
      // requirement, which is causing us to
      // search equivalent orders many times (especially
      // for larger MUBs). We should augment
      // the filters here to enforce that
      // items are sorted
      bases
        .toList
        .traverse {
          case (basis, (vecs, s)) =>
            if (basis == i) {
              val s1 = s.filter { v0 =>
                // we add in sorted order
                (v0 > vec) && orthFn(vec, v0)
              }
              val v1 = vec :: vecs

              if ((s1.size + v1.length) < dim) {
                // we can't reach a complete set
                None
              }
              else {
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
    private def extendBasis(b: Bases, i: Int): Option[TreeB] = {
      val orthVectors: List[Int] = forBasis(b, i)

      if (orthVectors.length == dim) {
        // we know this isn't complete and can't be
        // completed in this direction
        None
      }
      else {
        // make this a def so the head can be GCe'd below
        def choices = b(i)._2.to(LazyList)

        def extension(vec: Int): Option[Tree.NonEmpty[LazyList, Bases]] =
          addVector(b, i, vec).flatMap(extendFully)

        val children = choices.flatMap(extension(_))
        if (children.isEmpty) None
        else Some(Tree.NonEmpty(b, children))
      }
    }

    def extendFully(b: Bases): Option[Tree.NonEmpty[LazyList, Bases]] = {
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
            extendBasis(b, basis)
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

    lazy val fullBases: Option[Tree.NonEmpty[LazyList, Bases]] = extendFully(initBasis)

    lazy val firstCompleteExample: Option[Bases] =
      fullBases.flatMap(firstComplete(_))
  }
}
