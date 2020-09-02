package org.bykn.mubs

import scala.concurrent.{ExecutionContext, Future}

object Cliques {

  final def andN[@specialized(Int) A](n0: A => Boolean, n1: A => Boolean): A => Boolean =
    { n: A => n0(n) && n1(n) }

  /**
   * Final all cliques starting with initNode
   * that have a given size
   */
  private def find[@specialized(Int) A](
    size: Int,
    initNode: A,
    incNode: A => A,
    isLastNode: A => Boolean,
    inClique: A => Boolean,
    nfn: A => A => Boolean,
    searchNext: Boolean): LazyList[List[A]] = {

    def fromNext: LazyList[List[A]] =
      if (searchNext) find(size, incNode(initNode), incNode, isLastNode, inClique, nfn, true)
      else LazyList.empty[List[A]]

    if (size <= 0) LazyList(Nil)
    else if (size == 1) {
      def tail: LazyList[List[A]] =
        if (isLastNode(initNode)) LazyList.empty[List[A]]
        else fromNext


      if (inClique(initNode)) {
        val c1: List[A] = initNode :: Nil
        (c1 #:: tail)
      }
      else tail
    }
    else {
      // size is 2 or more
      if (isLastNode(initNode)) {
        // we can't find 2
        LazyList.empty
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

          val withInit = find(
            size - 1,
            nextNode,
            incNode,
            isLastNode,
            inClique2,
            nfn,
            true).map(initNode :: _)

          withInit #::: fromNext
        }
        else fromNext
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
   * In parallel try to find all cliques
   */
  final def findAllFuture[@specialized(Int) A](
    size: Int,
    initNode: A,
    incNode: A => A,
    isLastNode: A => Boolean,
    nfn: A => A => Boolean)(implicit ec: ExecutionContext): Future[LazyList[List[A]]] = {

    Future.traverse(allNodes(initNode, incNode, isLastNode)) { n =>
      Future {
        // we want to force inside the future
        find(size, n, incNode, isLastNode, Function.const(true), nfn, false).toList
      }
    }
    .map(_.flatten)
  }
}
