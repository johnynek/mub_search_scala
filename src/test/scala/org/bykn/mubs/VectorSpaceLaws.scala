package org.bykn.mubs

import org.scalacheck.Prop.forAll

import org.scalacheck.Gen

class VectorSpaceLaws extends munit.ScalaCheckSuite {
  val dim = 6

  val space = new VectorSpace.Space[Cyclotomic.N3, Cyclotomic.L3](dim, 20)

  val genInt: Gen[Int] =
    Gen.choose(0, space.vectorCount.toInt - 1)

  val genVec: Gen[Array[Int]] =
    genInt
      .map { i =>
        val ary = new Array[Int](dim)
        space.intToVector(i, ary)
        ary
      }

  def shuffle[A](ary: Array[A]): Gen[Array[A]] = {
    val res = ary.clone()

    def loop(idx: Int): Gen[Array[A]] =
      if (idx >= ary.length) Gen.const(res)
      else
        Gen.choose(idx, ary.length - 1)
          .flatMap { targ =>
            val tmp = res(idx)
            res(idx) = res(targ)
            res(targ) = tmp
            loop(idx + 1)
          }

    loop(0)
  }

  property("trace is invariant to shuffle") {
    val genPair: Gen[(Array[Int], Array[Int])] =
      genVec.flatMap { v => shuffle(v).map((v, _)) }

    forAll(genPair) { case (v1, v2) =>
      space.trace(v1) == space.trace(v2)
    }
  }

  property("conjProd + trace == dotAbs") {
    val targ = new Array[Int](dim)
    forAll(genVec, genVec) { (v1, v2) =>
      space.conjProd(v1, v2, targ)

      space.trace(targ) == space.dotAbs(v1, v2)
    }
  }

  property("intToVector and vectorToInt roundTrip") {
    val ary = new Array[Int](dim)
    forAll(genInt) { i: Int =>
      space.intToVector(i, ary)
      val i1 = space.vectorToInt(ary)
      i1 == i
    }
  }

  property("incInPlace is like adding 1") {
    val ary = new Array[Int](dim)
    forAll(genInt) { i: Int =>
      space.intToVector(i, ary)
      space.incInPlace(ary)
      val i1 = space.vectorToInt(ary)
      i1 == (i + 1)
    }
  }

  property("conjProdInt works like conjProd") {
    val v1 = new Array[Int](dim)
    val v2 = new Array[Int](dim)
    val v3 = new Array[Int](dim)
    val cp = space.conjProdInt()
    forAll(genInt, genInt) { (i1, i2) =>
      space.intToVector(i1, v1)
      space.intToVector(i2, v2)
      space.conjProd(v1, v2, v3)
      val i3 = space.vectorToInt(v3)
      assert(cp(i1, i2) == i3)
    }
  }

  property("chooseN(n, x) returns x.length^n items each with exactly n items and no duplicates") {
    forAll(Gen.choose(0, 4), Gen.choose(0, 10).flatMap(Gen.listOfN(_, Gen.const(())))) { (n, x) =>
      // zipWithIndex to make each item unique
      val items = VectorSpace.chooseN(n, x.zipWithIndex)
      assert(items.length == math.pow(x.length, n).toInt)
      assert(items.forall(_.length == n))
      assert(items.distinct == items)
    }
  }

  property("allDistinctPairs returns n(n-1)/2 items") {
    forAll(Gen.choose(0, 100).flatMap(Gen.listOfN(_, Gen.const(())))) { x =>
      // zipWithIndex to make each item unique
      val uniq = x.zipWithIndex
      val items = VectorSpace.allDistinctPairs(uniq)
      val n = x.length
      assert(items.length == (n*(n-1)/2))
      val allSet = items.toSet
      assert(allSet.size == items.length)
      // we don't contain x and x.swap
      assert(items.forall { pair => !allSet(pair.swap) })
    }
  }
}
