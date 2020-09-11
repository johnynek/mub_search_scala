package org.bykn.mubs

import cats.data.OneAnd
import java.util.BitSet
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

  class Instance(
    val dim: Int,
    val goalHads: Int,
    isOrth: () => (Int, Int) => Boolean,
    isUB: () => (Int, Int) => Boolean,
    next: Int => Option[Int],
    pOrth: Double,
    pUb: Double) {

    import scala.math.pow

    private[this] val hads = (0 until goalHads).toList

    type Bases = Map[Int, List[Int]]
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
        b.get(basis) match {
          case Some(l) => l.length == dim
          case None => false
        }
      }

    def extensionProb(b: Bases, i: Int): Double = {

      val orthVectors: Int = b.getOrElse(i, Nil).length
      val res =
        if (orthVectors == dim) 0.0
        else if ((i > 0) && (b.getOrElse(i - 1, Nil).isEmpty)) {
          // assembly bases in order
          0.0
        }
        else {
          val unbiasedVectors: Int =
            b.iterator.map {
              case (basis, vecs) if basis != i => vecs.length
              case _ => 0
            }
            .sum
          pow(pOrth, orthVectors) * pow(pUb, unbiasedVectors)
        }

      //println(s"extension prob = $b -> $i = $res")
      res
    }

    // all vectors ABOVE init (init is not included)
    // 0 is safe because we start building with 0
    // included
    def allVectorsFrom(init: Int): LazyList[Int] =
      LazyList.iterate(next(init))(_.flatMap(next))
        .takeWhile(_.isDefined)
        .map(_.get)

    // fully extend an incomplete basis
    private def extendBasis(b: Bases, i: Int): Option[TreeB] = {
      val orthVectors: List[Int] = b.getOrElse(i, Nil)

      if (orthVectors.length == dim) {
        // we know this isn't complete and can't be
        // completed in this direction
        None
      }
      else {
        val unbiasedVectors: List[Int] =
          b.iterator.flatMap {
            case (basis, vecs) if basis != i => vecs
            case _ => List.empty
          }
          .toList

        val orthFn = isOrth()
        val unbiasedFn = isUB()

        // we can always go build
        // the basis in a sorted order
        // so, the vec has to be greater than all
        // items in the vector currently
        //
        // similarly, we can sort the mubs,
        val lowerBound: Int = {
          val lowestVec: Int = 0

          val unbiasedLB: Int =
            if (i > 0) {
              // don't build on a basis unless
              // the previous exists and
              // the vector is greater than the smallest
              // vector in the previous
              val prevBasis = b.getOrElse(i - 1, Nil)
              prevBasis.lastOption match {
                case None => Int.MaxValue
                case Some(lb) => lb
              }
            }
          else lowestVec

          val orthLB: Int =
            orthVectors.headOption.getOrElse(lowestVec)

          math.max(unbiasedLB, orthLB)
        }

        def extension(vec: Int): Option[Tree.NonEmpty[LazyList, Bases]] = {

          val keep =
            unbiasedVectors.forall(unbiasedFn(_, vec)) &&
              orthVectors.forall(orthFn(_, vec))

          if (keep) {
            val nextBases = {
              val initVs = b.getOrElse(i, Nil)
              b.updated(i, vec :: initVs)
            }

            extendFully(nextBases)
          }
          else None
        }

        val children = allVectorsFrom(lowerBound).flatMap(extension(_))
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
          hads.sortBy(extensionProb(b, _)).reverse

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

    val initBasis: Bases = Map((0, 0 :: Nil))

    lazy val fullBases: Option[Tree.NonEmpty[LazyList, Bases]] = extendFully(initBasis)

    lazy val firstCompleteExample: Option[Bases] =
      fullBases.flatMap(firstComplete(_))
  }
}
