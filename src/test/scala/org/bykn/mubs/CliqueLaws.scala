package org.bykn.mubs

import org.scalacheck.Prop.forAll

import org.scalacheck.Prop
import java.util.concurrent.Executors
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.concurrent.duration.Duration.Inf

class CliqueLaws extends munit.ScalaCheckSuite {

  implicit val cpuEC: ExecutionContext = ExecutionContext.fromExecutorService(Executors.newFixedThreadPool(Runtime.getRuntime().availableProcessors()))

  // make all possible combinations of size, then filter such that they are all neighbors
  @annotation.tailrec
  final def isClique[A](lst: List[A])(nfn: (A, A) => Boolean): Boolean =
    lst match {
      case Nil => true
      case h1 :: tail =>
        tail.forall { h2 => (h1 != h2) && nfn(h1, h2) } && isClique(tail)(nfn)
    }

  def naiveCliques[A: Ordering](size: Int, nodes: LazyList[A], nfn: (A, A) => Boolean): LazyList[List[A]] = {
    def allCombos(size: Int, ns: LazyList[A]): LazyList[List[A]] =
      if (size <= 0) LazyList(Nil)
      else if (ns.isEmpty) LazyList.empty
      else {
        for {
          h <- ns
          tail <- allCombos(size - 1, ns.tail)
        } yield h :: tail
      }

    allCombos(size, nodes)
      .filter { s =>
        s.sliding(2).forall { case Seq(a, b) =>
          Ordering[A].lt(a, b)
        }
      }
      .filter(isClique(_)(nfn))
  }

  def isCliqueLaw(size: Int, maxNodes: Int)(nfn: (Int, Int) => Boolean): Prop = {
    val next: Int => Int = _ + 1
    val last: Int => Boolean = _ >= maxNodes

    val nodes = Cliques.allNodes(0, next, last)

    val cliqres = Cliques.findAllFuture(size, 0, next, last, { n1: Int => nfn(n1, _) })

    val cliq = Await.result(cliqres.map(_.toList), Inf)

    cliq.forall(isClique(_)(nfn))
  }

  def matchLaw(size: Int, maxNodes: Int)(nfn: (Int, Int) => Boolean): Prop = {
    val next: Int => Int = _ + 1
    val last: Int => Boolean = _ >= maxNodes

    val nodes = Cliques.allNodes(0, next, last)

    val cliqres = Cliques.findAllFuture(size, 0, next, last, { n1: Int => nfn(n1, _) })
    val naive = naiveCliques(size, nodes, nfn).toList

    val cliq = Await.result(cliqres.map(_.toList), Inf)

    val res = (cliq == naive)

    if (!res) {
      println(s"$cliq != $naive")
    }

    res
  }

  property("for cliques of size 2 we emit only cliques") {
    forAll(isCliqueLaw(2, 20)(_))
  }

  property("for cliques of size 3 we emit only cliques") {
    forAll(isCliqueLaw(3, 20)(_))
  }

  property("for cliques of size 4 we emit only cliques") {
    forAll(isCliqueLaw(4, 20)(_))
  }

  property("for cliques of size 2 we match naive") {
    forAll(matchLaw(2, 20)(_))
  }

  property("for cliques of size 3 we match naive") {
    forAll(matchLaw(3, 20)(_))
  }

  property("for cliques of size 4 we match naive") {
    forAll(matchLaw(4, 20)(_))
  }
}
