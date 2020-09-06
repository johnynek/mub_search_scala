package org.bykn.mubs

import scala.reflect.ClassTag
import scala.concurrent.{ExecutionContext, Future}

object Cliques {

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
  def async[A](
    size: Int,
    initNode: A,
    incNode: A => A,
    isLastNode: A => Boolean,
    buildNfn: () => A => A => Boolean,
    lessThan: (A, A) => Boolean)(implicit ec: ExecutionContext): Future[List[List[A]]] = {
      def all = allNodes(initNode, incNode, isLastNode).iterator

      def loop(size: Int): Future[List[List[A]]] =
        if (size <= 1) {
          // there are no cliques with negative size
          // there is exactly 1 clique with 0 size
          // and each node can be in a clique of size 1
          if (size < 0) Future.successful(Nil)
          else if (size == 0) Future.successful(Nil :: Nil)
          else Future.successful(all.map(_ :: Nil).toList)
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

                    // we enumerate all the previous items and see if we can find more
                    smaller
                      .filter { clique =>
                        // since size >= 2, previous clique size is not empty, so .head is okay
                        val isSmaller = lessThan(n1, clique.head)

                        isSmaller && clique.forall(neighborToN1)
                      }
                      .map(n1 :: _)
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
  def sync[A](
    size: Int,
    initNode: A,
    incNode: A => A,
    isLastNode: A => Boolean,
    nfn: A => A => Boolean,
    lessThan: (A, A) => Boolean): LazyList[List[A]] = {
      def all = allNodes(initNode, incNode, isLastNode)
      def loop(size: Int): LazyList[List[A]] =
        if (size <= 0) LazyList(Nil)
        else if (size == 1) all.map(_ :: Nil)
        else {
          val smaller = loop(size - 1)
          // now we see which of these we can add a single node to:
          all.flatMap { n1 =>
            val neighborToN1 = nfn(n1)
            smaller
              .filter { clique =>
                // we know that clique is not empty because size >= 2
                val isSmaller = lessThan(n1, clique.head)

                isSmaller && clique.forall(neighborToN1)
              }
              .map(n1 :: _)
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
