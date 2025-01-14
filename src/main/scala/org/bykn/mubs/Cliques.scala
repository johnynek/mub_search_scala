package org.bykn.mubs

import cats.{Eval, Order, Traverse}
import cats.data.{NonEmptyList, NonEmptyLazyList}
import scala.reflect.ClassTag
import scala.concurrent.{ExecutionContext, Future}
import scala.collection.immutable.SortedMap
import org.typelevel.paiges.Doc

import cats.implicits._
import scala.collection.immutable

object Cliques {
  /**
   * Represents a set of cliques all of which
   * begin with the same item or are empty
   * All of them have the same size
   */
  sealed abstract class Family[+A] {
    def headOption: Option[A]
    def cliques: NonEmptyLazyList[List[A]]
    // how big are the cliques
    def cliqueSize: Int
    // how many cliques are in this family
    def cliqueCount: Long
    // return the same cliqueSize family
    // such that all items have true
    def filter(fn: A => Boolean): Option[Family[A]]

    // given each reversed prefix, see if we need to keep recursing in
    // this allows us to cut out whole trees without recursing further
    def filterRevPrefixes(fn: NonEmptyList[A] => Boolean): Option[Family[A]]

    def map[B](fn: A => B): Family[B]
    def mapExpand[B](fn: A => NonEmptyLazyList[B]): NonEmptyLazyList[Family[B]]

    def toDoc: Doc

    def summary: String = s"Cliques.Family size = $cliqueSize, count = $cliqueCount"
    override def toString = toDoc.renderTrim(80)

    def prefix[A1 >: A](a1: A1): Family[A1] =
      Family.NonEmpty(a1, NonEmptyLazyList.fromLazyListPrepend(this, LazyList.empty))
  }
  object Family {
    implicit class InvariantMethods[A](private val self: Family[A]) extends AnyVal {
      def collectHead(fn: A => Option[A]): Option[Family[A]] =
        self match {
          case Empty => Some(Empty)
          case NonEmpty(a, rest) =>
            fn(a).map(NonEmpty(_, rest))
        }

      def contains(lst: List[A])(implicit A: cats.Eq[A]): Boolean =
        self match {
          case Empty => lst.isEmpty
          case NonEmpty(a, rest) =>
            lst match {
              case h :: t =>
                A.eqv(h, a) && rest.exists(_.contains(t))
              case Nil => false
            }
        }
    }

    final case object Empty extends Family[Nothing] {
      def headOption: Option[Nothing] = None
      val cliques = NonEmptyLazyList.fromLazyListPrepend(Nil, LazyList.empty)
      def cliqueSize: Int = 0
      def cliqueCount: Long = 1L
      def filter(fn: Nothing => Boolean): Option[Family[Nothing]] = Some(Empty)
      def filterRevPrefixes(fn: NonEmptyList[Nothing] => Boolean) = Some(Empty)
      def map[B](fn: Nothing => B): Family[B] = this
      def mapExpand[B](fn: Nothing => NonEmptyLazyList[B]): NonEmptyLazyList[Family[B]] = NonEmptyLazyList(this)
      def toDoc = Doc.text("{}")
    }
    // invariant:
    // all items in tails have the same cliqueSize
    final case class NonEmpty[A](head: A, tails: NonEmptyLazyList[Family[A]]) extends Family[A] {
      def headOption: Option[A] = Some(head)
      def cliques = tails.flatMap { tail => tail.cliques.map(head :: _) }
      def cliqueSize: Int = tails.head.cliqueSize + 1
      lazy val cliqueCount: Long =
        tails.foldLeft(0L)(_ + _.cliqueCount)

      def filter(fn: A => Boolean): Option[Family[A]] =
        if (fn(head)) {
          NonEmptyLazyList.fromLazyList(tails.toLazyList.flatMap(_.filter(fn)))
            .map(NonEmpty(head, _))
        }
        else None

      def filterRevPrefixes(fn: NonEmptyList[A] => Boolean): Option[Family[A]] = {
        def loop(tails: NonEmptyLazyList[Family[A]], prefix: NonEmptyList[A]): Option[Family[A]] =
          if (fn(prefix)) {
            NonEmptyLazyList.fromLazyList(tails.toLazyList.flatMap {
              case Empty => Some(Empty)  
              case NonEmpty(h, t) => loop(t, h :: prefix)
            })
            .map(NonEmpty(prefix.head, _))
          }
          else None

        loop(tails, NonEmptyList.one(head))
      }

      def map[B](fn: A => B): Family[B] =
        NonEmpty(fn(head), tails.map(_.map(fn)))

      def mapExpand[B](fn: A => NonEmptyLazyList[B]): NonEmptyLazyList[Family[B]] =
        fn(head)
          .flatMap { headB =>
            // we could cache lazyTraverse(tails)(_.mapExpand(fn)), but that would materialize into memory
            // maybe more than we want
            lazyTraverse(tails)(_.mapExpand(fn))
              .map(NonEmpty(headB, _))
          }

      def toDoc = {
        val tdoc = tails.toList.map(_.toDoc)

        val children = Doc.intercalate(Doc.comma + Doc.lineOrSpace, tdoc).nested(2)

        Doc.char('{') + (Doc.space + Doc.text(head.toString) + Doc.lineOrSpace + Doc.char(':') +
          Doc.lineOrSpace + (Doc.char('[') + Doc.lineOrSpace + children + Doc.lineOrSpace + Doc.char(']')).nested(2)).nested(2) +
          Doc.char('}')
      }
    }

    def lazyTraverse[A, B](nel: NonEmptyLazyList[A])(fn: A => NonEmptyLazyList[B]): NonEmptyLazyList[NonEmptyLazyList[B]] =
      fn(nel.head)
        .flatMap { h =>
          NonEmptyLazyList.fromLazyList(nel.tail) match {
            case None => NonEmptyLazyList(NonEmptyLazyList(h))
            case Some(nelTail) => lazyTraverse(nelTail)(fn).map(h +: _)
          }
        }
        

    // if the inner lists are all the same size, return this as a family
    def fromList[A: Order](lst: List[List[A]]): Option[NonEmptyList[Family[A]]] =
      NonEmptyList.fromList(lst).flatMap { nel0 =>
        val nel = nel0.distinct
        val len = nel.head.length
        if (nel.tail.forall(_.length == len)) {
          // we have verified the invariant that all inner elements have the same length and are distinct
          def loop(groups: NonEmptyList[List[A]]): NonEmptyList[Family[A]] =
            if (groups.head.isEmpty) NonEmptyList.one(Empty)
            else {
              val headOrder = groups
                .iterator
                .map { nel => nel.head }
                .zipWithIndex
                .foldLeft(SortedMap.empty[A, Int](Order[A].toOrdering)) { case (map, (k, idx)) =>
                  if (map.contains(k)) map  
                  else map.updated(k, idx)
                }
              
              // preserve the order of the original list
              val grouped = groups.groupByNem(_.head)(Order[Int].contramap(headOrder))

              grouped
                .toNel
                .map { case (head, all) =>
                  // all is nonEmpty because each inner starts with head 
                  val allNE = all.map(_.tail)
                  NonEmpty(head, NonEmptyLazyList.fromNonEmptyList(loop(allNE)))
                }

            }

          Some(loop(nel))
        } 
        else None
      }

    // This is choosing with replacement
    def chooseN[A](n: Int, items: List[A]): LazyList[Family[A]] = {
      val itemsLL = items.to(LazyList)

      def loop(n: Int): LazyList[Family[A]] =
        if (n == 0) LazyList(Empty)
        else {
          NonEmptyLazyList.fromLazyList(loop(n - 1)) match {
            case None => LazyList.empty
            case Some(rest) =>
              // compute the tail once and share
              // the reference with all items
              itemsLL.map { a => NonEmpty(a, rest) }
          }
        }

      if (n == 0) LazyList(Empty)
      else if (n < 0 || items.isEmpty) LazyList.empty
      else loop(n)
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
      def cliqueMerge[A, B](fa: Family[A], fb: Family[B])(fn: ((A, B), (A, B)) => Boolean): Option[Family[(A, B)]] = {

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
                    aa <- as.toLazyList
                    bb <- bs.toLazyList
                    ab <- loop(outer1, aa, bb).toList
                  } yield ab

                NonEmptyLazyList.fromLazyList(children)
                  .map(NonEmpty(headAB, _))
              }

            case _ =>
              // these are misaligned
              None
          }

        loop(Nil, fa, fb)
      }

      // Lazily combine two families if the cliques are the same size
      def product[A, B](fa: Family[A], fb: Family[B]): Option[Family[(A, B)]] =
        if (fa.cliqueSize == fb.cliqueSize) {
          def loop(fa: Family[A], fb: Family[B]): Family[(A, B)] =
            (fa, fb) match {
              case (Empty, Empty) => Empty
              case (NonEmpty(a, as), NonEmpty(b, bs)) =>
                val children =
                  for {
                    aa <- as
                    bb <- bs
                  } yield loop(aa, bb)

                NonEmpty((a, b), children)

              case notAligned =>
                // these are misaligned
                sys.error(s"invariant violation: $notAligned")
            }

          Some(loop(fa, fb))
        }
        else None

    /**
     * See the law in the tests, but this:
     * expand(ff).flatMap(_.cliques).toList
     *
     * should create the same set as fully expanding
     * the families
     */
    def expand[A](f2: Family[Family[A]]): LazyList[Family[List[A]]] =
      expandWith(f2)(_.cliques.toLazyList)

    def expandWith[A, B](f2: Family[A])(cliquesOf: A => LazyList[B]): LazyList[Family[B]] =
      f2 match {
        case Empty => LazyList(Empty)
        case NonEmpty(fa, rest) =>
          val faCliques = cliquesOf(fa)
          if (faCliques.isEmpty) LazyList.empty
          else {
            // use the if to avoid recursing when faCliques is empty
            // make this lazy so we only evaluate it when faCliques is nonEmpty
            val restWork = rest.map(expandWith(_)(cliquesOf))
            for {
              first <- faCliques
              tails <- restWork.toLazyList
              if (tails.nonEmpty)
            } yield NonEmpty(first, NonEmptyLazyList.fromLazyListUnsafe(tails))
        }
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

      val emptyChildren = NonEmptyLazyList.fromLazyListPrepend(Family.Empty, LazyList.empty)

      def loop(size: Int): Future[List[Family[A]]] =
        if (size <= 1) Future.successful {
          // there are no cliques with negative size
          // there is exactly 1 clique with 0 size
          // and each node can be in a clique of size 1
          if (size < 0) Nil
          else if (size == 0) (Family.Empty :: Nil)
          else {
            all.map(Family.NonEmpty(_, emptyChildren)).toList
          }
        }
        else {
          loop(size - 1)
            .flatMap { smaller =>
              if (smaller.isEmpty) Future.successful(Nil)
              else {
                // now we see which of these we can add a single node to:
                batched(all, 1000) { n1 =>
                  Future {
                    val nfn = buildNfn()
                    val neighborToN1 = nfn(n1)

                    val ord = implicitly[Ordering[A]]
                    val n1Children =
                      smaller
                        .to(LazyList)
                        .flatMap {
                          case f@Family.NonEmpty(h, rest) if ord.lt(n1, h) && neighborToN1(h) =>
                            f.filter(neighborToN1)
                          case _ =>
                            None
                        }

                    NonEmptyLazyList.fromLazyList(n1Children)
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
      val empty = NonEmptyLazyList.fromLazyListPrepend(Family.Empty, LazyList.empty)

      def loop(size: Int): LazyList[Family[A]] =
        if (size <= 1) {
          if (size < 0) LazyList.empty
          else if (size == 0) LazyList(Family.Empty)
          else {
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

              NonEmptyLazyList.fromLazyList(n1Children)
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
