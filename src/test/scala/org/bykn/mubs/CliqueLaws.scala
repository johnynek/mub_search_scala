package org.bykn.mubs

import cats.data.NonEmptyList
import java.util.concurrent.Executors
import org.scalacheck.Prop.forAll
import org.scalacheck.Arbitrary.arbitrary
import org.scalacheck.{Gen, Prop}
import org.typelevel.paiges.Doc
import scala.concurrent.duration.Duration.Inf
import scala.concurrent.{Await, ExecutionContext, Future}

class CliqueLaws extends munit.ScalaCheckSuite {

  implicit val cpuEC: ExecutionContext = ExecutionContext.fromExecutorService(Executors.newFixedThreadPool(Runtime.getRuntime().availableProcessors()))


  def genCliqueFamily[A](size: Int, ga: Gen[A], branch: Gen[Int]): Gen[Cliques.Family[A]] =
    if (size <= 0) Gen.const(Cliques.Family.Empty)
    else {
      val recur = Gen.lzy(genCliqueFamily(size - 1, ga, branch))
      for {
        head <- ga
        children <- branch
        // make sure we have at least 1 to make an NEL
        childList0 <- Gen.listOfN(children max 1, recur)
        // make sure we generate legit cliques so that we don't repeat head branches in children
        childList = childList0.groupBy(_.headOption).iterator.map { case (_, vs) => (vs.head) }.toList
      } yield Cliques.Family.NonEmpty(head, NonEmptyList.fromListUnsafe(childList))
    }

  // make all possible combinations of size, then filter such that they are all neighbors
  @annotation.tailrec
  final def isClique[A](lst: List[A])(nfn: (A, A) => Boolean): Boolean =
    lst match {
      case Nil => true
      case h1 :: tail =>
        tail.forall { h2 => (h1 != h2) && nfn(h1, h2) } && isClique(tail)(nfn)
    }
  // this isClique doesn't care about nodes being distinct
  @annotation.tailrec
  final def isCliqueLax[A](lst: List[A])(nfn: (A, A) => Boolean): Boolean =
    lst match {
      case Nil => true
      case h1 :: tail =>
        tail.forall { h2 => nfn(h1, h2) } && isCliqueLax(tail)(nfn)
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

  def timeit[A](name: String)(a: => A): A = {
    val start = System.nanoTime()
    val res = a
    val nanos = System.nanoTime() - start
    //println(s"$name: ${nanos/1e6}ms")
    res
  }

  def isCliqueLaw(size: Int, maxNodes: Int)(nfn: (Int, Int) => Boolean): Prop = {
    val next: Int => Int = _ + 1
    val last: Int => Boolean = _ >= maxNodes

    val nodes = Cliques.allNodes(0, next, last)

    val cliqres2 = timeit(s"sync $size $maxNodes") {
      Cliques.sync[Int](size, 0, next, last, { n1: Int => nfn(n1, _) }).toList.flatMap(_.cliques.toList)
    }

    val cliq = timeit(s"findAllFuture $size $maxNodes") {
      val cliqres = Cliques.findAllFuture(size, 0, next, last, () => { n1: Int => nfn(n1, _) }, identity[List[Int]])
      Await.result(cliqres.map(_.toList), Inf)
    }

    val cliq3 = timeit(s"async $size $maxNodes") {
      val cliqres = Cliques.async(size, 0, next, last, () => { n1: Int => nfn(n1, _) })
      Await.result(cliqres, Inf)
        .flatMap(_.cliques)
    }

    cliq.forall(isClique(_)(nfn)) &&
      cliqres2.forall(isClique(_)(nfn)) &&
      cliq3.forall(isClique(_)(nfn))
  }

  def matchLaw(size: Int, maxNodes: Int)(nfn: (Int, Int) => Boolean): Prop = {
    val next: Int => Int = _ + 1
    val last: Int => Boolean = _ >= maxNodes

    val nodes = Cliques.allNodes(0, next, last)

    val cliqres = Cliques.findAllFuture(size, 0, next, last, () => { n1: Int => nfn(n1, _) }, identity[List[Int]])
    val cliqres2 =
      Cliques
        .sync[Int](size, 0, next, last, { n1: Int => nfn(n1, _) })
        .toList
        .flatMap(_.cliques.toList)

    val naive = naiveCliques(size, nodes, nfn).toList

    val cliq = Await.result(cliqres.map(_.toList), Inf)

    val res = (cliq == naive)
    val res2 = (cliqres2 == naive)

    if (!(res && res2)) {
      if (!res) println(s"$cliq\n\n!=\n\n$naive")
      if (!res2) println(s"$cliqres2\n\n!=\n\n$naive")
    }

    res && res2
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
    forAll(matchLaw(2, 10)(_))
  }

  property("for cliques of size 3 we match naive") {
    forAll(matchLaw(3, 10)(_))
  }

  property("for cliques of size 4 we match naive") {
    forAll(matchLaw(4, 10)(_))
  }

  implicit def listOrd[A: Ordering]: Ordering[List[A]] =
    new Ordering[List[A]] {
      @annotation.tailrec
      final def compare(left: List[A], right: List[A]): Int =
        (left, right) match {
          case (Nil, Nil) => 0
          case (Nil, _) => -1
          case (_ :: _, Nil) => 1
          case (lh :: lt, rh :: rt) =>
            val c = Ordering[A].compare(lh, rh)
            if (c == 0) compare(lt, rt)
            else c
        }
    }

  property("cliqueMerge matches a naive crossproduct + filter") {
    val pair =
      Gen.choose(0, 3)
        .flatMap { size =>
          val genC = genCliqueFamily(size, Gen.oneOf(true, false), Gen.choose(1, 4))
          Gen.zip(genC, genC)
        }

    val mergeFn = arbitrary[((Boolean, Boolean), (Boolean, Boolean)) => Boolean]

    forAll(pair, mergeFn) { case ((cl0, cl1), fn) =>
      val cl01 = Cliques.Family.cliqueMerge(cl0, cl1)(fn)

      val naive: List[List[(Boolean, Boolean)]] =
        (for {
          c0 <- cl0.cliques
          c1 <- cl1.cliques
          zipped = c0.zip(c1)
          if (isCliqueLax(zipped)(fn))
        } yield zipped).toList.map(_.sorted).sorted

      val fancy: List[List[(Boolean, Boolean)]] =
        cl01.to(LazyList).flatMap(_.cliques).toList
          .map(_.sorted).sorted

      assert(fancy == naive, s"$fancy\n\n!=\n\n$naive\n\n($cl01)")
    }
  }

  def cross[A](as: List[List[A]]): List[List[A]] =
    as match {
      case Nil => Nil :: Nil
      case h :: rest =>
        for {
          head <- h
          tail <- cross(rest)
        } yield head :: tail
    }

  def crossSimple[A](as: Cliques.Family[Cliques.Family[A]]): List[List[List[A]]] =
    as.cliques
      .toList
      .flatMap { listFam: List[Cliques.Family[A]] =>
        // make the full cross-product
        val expanded: List[List[List[A]]] =
          listFam.map(_.cliques.toList)

        cross(expanded)
      }

  def sort3[A: Ordering](s: List[List[List[A]]]): List[List[List[A]]] =
    s.map(_.map(_.sorted).sorted).sorted

  test("crossSimple is simple") {
    val twoBits = Cliques.Family.chooseN(2, List(true, false))
    val fourBits = Cliques.Family.chooseN(2, twoBits)

    assert(cross(List(List(1), List(2))) == List(List(1, 2)))
    assert(cross(List(List(1, 2), List(3, 4))) == List(List(1, 3), List(1, 4), List(2, 3), List(2, 4)))
    assert(cross(List(List(1, 2), List(3, 4, 5))) == List(List(1, 3), List(1, 4), List(1, 5), List(2, 3), List(2, 4), List(2, 5)))
    assert(cross(List(List(1, 2), List(3, 4), List(5))) == List(List(1, 3, 5), List(1, 4, 5), List(2, 3, 5), List(2, 4, 5)))


    val fourCross = fourBits.flatMap(crossSimple(_))

    assert(sort3(fourCross) == sort3(List(
      List(List(true, true), List(true, true)),
      List(List(true, true), List(true, false)),
      List(List(true, true), List(false, true)),
      List(List(true, true), List(false, false)),
      List(List(true, false), List(true, true)),
      List(List(true, false), List(true, false)),
      List(List(true, false), List(false, true)),
      List(List(true, false), List(false, false)),
      List(List(false, true), List(true, true)),
      List(List(false, true), List(true, false)),
      List(List(false, true), List(false, true)),
      List(List(false, true), List(false, false)),
      List(List(false, false), List(true, true)),
      List(List(false, false), List(true, false)),
      List(List(false, false), List(false, true)),
      List(List(false, false), List(false, false)))))
  }

  property("crossProduct is lawful") {
    val genC1 =
      Gen.zip(Gen.choose(0, 3), Gen.choose(0, 3))
        .flatMap { case (s1, s2) =>
          val genC0 = genCliqueFamily(s1, Gen.oneOf(true, false), Gen.choose(1, 4))
          genCliqueFamily(s2, genC0, Gen.choose(1, 4))
        }

    forAll(genC1) { ff =>
      val ll0: List[List[List[Boolean]]] =
        Cliques.Family.crossProduct(ff).flatMap(_.cliques).toList

      val ll1: List[List[List[Boolean]]] =
        crossSimple(ff)

      val left = sort3(ll0)
      val right = sort3(ll1)
      assert(left == right, s"$left != $right")
    }
  }
}
