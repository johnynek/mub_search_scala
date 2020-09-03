package org.bykn.mubs

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
        if (inClique(initNode)) {
          val inClique2: A => Boolean = andN(nfn(initNode), inClique)

          val withInit = findCheat(
            size - 1,
            nextNode,
            incNode,
            isLastNode,
            inClique2,
            nfn,
            true,
            Nil).map(initNode :: _)

          val acc1 = withInit reverse_::: acc
          if (searchNext) find(size, incNode(initNode), incNode, isLastNode, inClique, nfn, true, acc1)
          else acc1.reverse
        }
        else if (searchNext) find(size, incNode(initNode), incNode, isLastNode, inClique, nfn, true, acc)
        else acc.reverse
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
    repr: List[A] => C)(implicit ec: ExecutionContext): Future[List[C]] = {

    Future.traverse(allNodes(initNode, incNode, isLastNode).toList) { n =>
      Future {
        // we want to force inside the future
        find(size, n, incNode, isLastNode, Function.const(true), buildNfn(), false, Nil)
          .map(repr)
      }
    }
    .map(_.flatten)
  }
}