package org.bykn.mubs

import cats.{Eval, Traverse}
import cats.data.NonEmptyList
import scala.reflect.ClassTag
import scala.concurrent.{ExecutionContext, Future}
import org.typelevel.paiges.Doc

import cats.implicits._

object Cliques {
  /**
   * Represents a test of cliques all of which
   * begin with the same item
   */
  sealed abstract class Family[+A] {
    def headOption: Option[A]
    def cliques: LazyList[List[A]]
    // how big are the cliques
    def cliqueSize: Int
    // how many cliques are in this family
    def cliqueCount: Long
    // return the same cliqueSize family
    // such that all items have true
    def filter(fn: A => Boolean): Option[Family[A]]

    def map[B](fn: A => B): Family[B]


    def toDoc: Doc

    override def toString = toDoc.renderTrim(80)
  }
  object Family {
    implicit class InvariantMethods[A](private val self: Family[A]) extends AnyVal {
      def collectHead(fn: A => Option[A]): Option[Family[A]] =
        self match {
          case Empty => Some(Empty)
          case NonEmpty(a, rest) =>
            fn(a).map(NonEmpty(_, rest))
        }

    }

    final case object Empty extends Family[Nothing] {
      def headOption: Option[Nothing] = None
      def cliques = LazyList(Nil)
      def cliqueSize: Int = 0
      def cliqueCount: Long = 1L
      def filter(fn: Nothing => Boolean): Option[Family[Nothing]] = Some(Empty)
      def map[B](fn: Nothing => B): Family[B] = this
      def toDoc = Doc.text("{}")
    }
    // invariants:
    // 1. all items in tails have the same cliqueSize
    // 2. head < all heads in tails
    final case class NonEmpty[A](head: A, tails: NonEmptyList[Family[A]]) extends Family[A] {
      def headOption: Option[A] = Some(head)
      def cliques = tails.toList.to(LazyList).flatMap { tail => tail.cliques.map(head :: _) }
      def cliqueSize: Int = tails.head.cliqueSize + 1
      lazy val cliqueCount: Long =
        tails.foldLeft(0L)(_ + _.cliqueCount)

      def filter(fn: A => Boolean): Option[Family[A]] =
        if (fn(head)) {
          NonEmptyList.fromList(tails.toList.flatMap(_.filter(fn)))
            .map(NonEmpty(head, _))
        }
        else None

      def map[B](fn: A => B): Family[B] =
        NonEmpty(fn(head), tails.map(_.map(fn)))

      def toDoc = {
        val tdoc = tails.toList.map(_.toDoc)

        val children = Doc.intercalate(Doc.comma + Doc.lineOrSpace, tdoc).nested(2)

        Doc.char('{') + (Doc.space + Doc.text(head.toString) + Doc.lineOrSpace + Doc.char(':') +
          Doc.lineOrSpace + (Doc.char('[') + Doc.lineOrSpace + children + Doc.lineOrSpace + Doc.char(']')).nested(2)).nested(2) +
          Doc.char('}')
      }
    }

    def chooseN[A](n: Int, items: List[A]): LazyList[Family[A]] =
      if (n < 0) LazyList.empty
      else if (n == 0) LazyList(Empty)
      else if (items.isEmpty) LazyList.empty // can't take more than 0 from an empty list
      else {
        NonEmptyList.fromList(chooseN(n - 1, items).toList) match {
          case None => LazyList.empty
          case Some(rest) =>
            // compute the tail once and share
            // the reference with all items
            items.to(LazyList).map { a => NonEmpty(a, rest) }
        }
      }

    implicit val traverseForFamily: Traverse[Family] =
      new Traverse[Family] {
        override def map[A, B](fa: Family[A])(fn: A => B): Family[B] =
          fa.map(fn)

        def foldLeft[A, B](fa: Family[A], b: B)(f: (B, A) => B): B =
          fa match {
            case Empty => b
            case NonEmpty(a, rest) =>
              val b1 = f(b, a)
              rest.foldLeft(b1) { case (b, fam) =>
                foldLeft(fam, b)(f)
              }
          }
        def foldRight[A, B](fa: Family[A], lb: Eval[B])(f: (A, Eval[B]) => Eval[B]): Eval[B] =
          fa match {
            case Empty => lb
            case NonEmpty(a, rest) =>
              val restRes: Eval[B] =
                Eval.defer(rest.foldRight(lb) { case (fam, lb) =>
                  foldRight(fam, lb)(f)
                })
              f(a, restRes)
          }

        def traverse[G[_], A, B](fa: Family[A])(f: A => G[B])(implicit G: cats.Applicative[G]): G[Family[B]] =
          fa match {
            case Empty => G.pure(Empty)
            case NonEmpty(a, rest) =>
              (f(a), rest.traverse(traverse(_)(f)))
                .mapN(NonEmpty(_, _))
          }
        }

      // this is like a clique from two cliques
      def cliqueMerge[A, B, C](fa: Family[A], fb: Family[B])(fn: ((A, B), (A, B)) => Boolean): Option[Family[(A, B)]] = {

        def loop(outer: List[(A, B)], fa: Family[A], fb: Family[B]): Option[Family[(A, B)]] =
          (fa, fb) match {
            case (Empty, Empty) => Some(Empty)
            case (NonEmpty(a, as), NonEmpty(b, bs)) =>
              val headAB = (a, b)
              if (!outer.forall(fn(_, headAB))) {
                // we cannot add to this clique
                None
              }
              else {
                val outer1 = headAB :: outer
                val children =
                  for {
                    aa <- as.toList
                    bb <- bs.toList
                    ab <- loop(outer1, aa, bb).toList
                  } yield ab

                NonEmptyList.fromList(children)
                  .map(NonEmpty(headAB, _))
              }

            case _ =>
              // these are misaligned
              None
          }

        loop(Nil, fa, fb)
      }

    /**
     * See the law in the tests, but this:
     * crossProduct(ff).flatMap(_.cliques).toList
     *
     * should create the same set as fully expanding
     * the families
     */
    def crossProduct[A](f2: Family[Family[A]]): LazyList[Family[List[A]]] =
      f2 match {
        case Empty => LazyList(Empty)
        case NonEmpty(fa, rest) =>
          val restWork = rest.toList.to(LazyList).map(crossProduct(_))
          for {
            first <- fa.cliques
            tails <- restWork
            // we know restWork.nonEmpty since it was from a result from crossProduct
            tailNEL = NonEmptyList.fromListUnsafe(tails.toList)
          } yield NonEmpty(first, tailNEL)
      }
  }

  final def andN[@specialized(Int) A](n0: A => Boolean, n1: A => Boolean): A => Boolean =
    { n: A => n0(n) && n1(n) }

  private def findCheat[@specialized(Int) A](
    size: Int,
    initNode: A,
    incNode: A => A,
    isLastNode: A => Boolean,
    inClique: A => Boolean,
    nfn: A => A => Boolean,
    searchNext: Boolean,
    acc: List[List[A]]): List[List[A]] =
      find(size, initNode, incNode, isLastNode, inClique, nfn, searchNext, acc)

  /**
   * Final all cliques starting with initNode
   * that have a given size
   */
  @annotation.tailrec
  private def find[@specialized(Int) A](
    size: Int,
    initNode: A,
    incNode: A => A,
    isLastNode: A => Boolean,
    inClique: A => Boolean,
    nfn: A => A => Boolean,
    searchNext: Boolean,
    acc: List[List[A]]): List[List[A]] =

    if (size <= 0) (Nil :: acc).reverse
    else if (size == 1) {
      val acc1 =
        if (inClique(initNode)) {
          val c1: List[A] = initNode :: Nil
          (c1 :: acc)
        }
        else acc

        if (isLastNode(initNode) || !searchNext) acc1.reverse
        else find(size, incNode(initNode), incNode, isLastNode, inClique, nfn, true, acc1)
    }
    else {
      // size is 2 or more
      if (isLastNode(initNode)) {
        // we can't find 2
        acc.reverse
      }
      else {
        val nextNode = incNode(initNode)
        // now we go through all these and find
        // cliques of size - 1
        //
        // to be in the clique, you need to be
        // a neighbor to initNode and n
        val withInit =
          if (inClique(initNode)) {
            val inClique2: A => Boolean = andN(nfn(initNode), inClique)

            findCheat(
              size - 1,
              nextNode,
              incNode,
              isLastNode,
              inClique2,
              nfn,
              true,
              Nil).map(initNode :: _)
          }
          else Nil

        if (searchNext) {
          val acc1 = withInit reverse_::: acc
          find(size, nextNode, incNode, isLastNode, inClique, nfn, true, acc1)
        }
        else {
          acc reverse_::: withInit
        }
      }
    }

  def allNodes[@specialized(Int) A](initNode: A, incNode: A => A, isLastNode: A => Boolean): LazyList[A] =
    LazyList
      .iterate(Option(initNode)) {
        case Some(n) =>
          if (isLastNode(n)) None
          else Some(incNode(n))
        case None => None
      }
      .takeWhile(_.isDefined)
      .map(_.get)

  /**
   * By using Lists as the clique type we can share
   * the memory for all the smaller internal cliques
   * which can be a significant memory savings
   */
  def async[A: Ordering](
    size: Int,
    initNode: A,
    incNode: A => A,
    isLastNode: A => Boolean,
    buildNfn: () => A => A => Boolean)(implicit ec: ExecutionContext): Future[List[Family[A]]] = {
      def all = allNodes(initNode, incNode, isLastNode).iterator

      def loop(size: Int): Future[List[Family[A]]] =
        if (size <= 1) {
          // there are no cliques with negative size
          // there is exactly 1 clique with 0 size
          // and each node can be in a clique of size 1
          if (size < 0) Future.successful(Nil)
          else if (size == 0) Future.successful(Family.Empty :: Nil)
          else {
            val emptyChildren = NonEmptyList(Family.Empty, Nil)
            Future.successful(all.map(Family.NonEmpty(_, emptyChildren)).toList)
          }
        }
        else {
          val ord = implicitly[Ordering[A]]
          loop(size - 1)
            .flatMap { smaller =>
              if (smaller.isEmpty) Future.successful(Nil)
              else {
                // now we see which of these we can add a single node to:
                batched(all, 1000) { n1 =>
                  Future {
                    val nfn = buildNfn()
                    val neighborToN1 = nfn(n1)

                    val n1Children =
                      smaller
                        .flatMap {
                          case f@Family.NonEmpty(h, rest) if ord.lt(n1, h) && neighborToN1(h) =>
                            f.filter(neighborToN1)
                          case _ =>
                            None
                        }

                    NonEmptyList.fromList(n1Children)
                      .map(Family.NonEmpty(n1, _))
                  }
                } { _.flatten }
              }
            }
        }

      loop(size)
  }

  /**
   * By using Lists as the clique type we can share
   * the memory for all the smaller internal cliques
   * which can be a significant memory savings
   */
  def sync[A: Ordering](
    size: Int,
    initNode: A,
    incNode: A => A,
    isLastNode: A => Boolean,
    nfn: A => A => Boolean): LazyList[Family[A]] = {
      def all = allNodes(initNode, incNode, isLastNode)
      def loop(size: Int): LazyList[Family[A]] =
        if (size <= 1) {
          if (size < 0) LazyList.empty
          else if (size == 0) LazyList(Family.Empty)
          else {
            val empty = NonEmptyList(Family.Empty, Nil)
            all.map { n => Family.NonEmpty(n, empty) }
          }
        }
        else {
          val smaller = loop(size - 1)
          if (smaller.isEmpty) LazyList.empty
          else {
            val ord = implicitly[Ordering[A]]
            // now we see which of these we can add a single node to:
            all.flatMap { n1 =>
              val neighborToN1 = nfn(n1)
              val n1Children =
                smaller
                  .flatMap {
                    case f@Family.NonEmpty(h, rest) if ord.lt(n1, h) && neighborToN1(h) =>
                      f.filter(neighborToN1)
                    case _ =>
                      None
                  }

              NonEmptyList.fromList(n1Children.toList)
                .map(Family.NonEmpty(n1, _))
            }
          }
        }

      loop(size)
  }

  final def batched[A, B, C](iter: Iterator[A], size: Int)(fn: A => Future[B])(onBatch: List[B] => List[C])(implicit ec: ExecutionContext): Future[List[C]] = {
    val it = iter.grouped(size)

    def next(): Option[List[A]] =
      it.synchronized {
        if (it.hasNext) Some(it.next().toList)
        else None
      }

    def step(batch: List[A]): Future[List[C]] =
      Future.traverse(batch)(fn).map(onBatch)

    def result(): Future[List[C]] =
      next() match {
        case None => Future.successful(List.empty)
        case Some(batch) =>
          for {
            head <- step(batch)
            // we don't work on the next batch until the previous is done
            tail <- result()
          } yield head ::: tail
      }

    result()
  }

  /**
   * In parallel try to find all cliques
   * the neighbor function is built once for each
   * thread, so there is no sharing. If you want
   * to build a cache, it is safe
   */
  final def findAllFuture[@specialized(Int) A, C](
    size: Int,
    initNode: A,
    incNode: A => A,
    isLastNode: A => Boolean,
    buildNfn: () => A => A => Boolean,
    repr: List[A] => C)(implicit ec: ExecutionContext): Future[List[C]] =
    batched(allNodes(initNode, incNode, isLastNode).iterator, 10000)({n =>
      Future {
        // do this once per thread
        val edgeFn = buildNfn()
        find(size, n, incNode, isLastNode, Function.const(true), edgeFn, false, Nil)
      }
    })({ resBatch =>
      resBatch.filter(_.nonEmpty).flatMap(_.map(repr))
    })
}
