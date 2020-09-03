package org.bykn.mubs

import org.scalacheck.Prop.forAll

import org.scalacheck.Gen

class VectorSpaceLaws extends munit.ScalaCheckSuite {
  val dim = 6

  val space = new VectorSpace.Space[Cyclotomic.N3, Cyclotomic.L3](dim, 20)

  val genVec: Gen[Array[Int]] =
    Gen.choose(0, space.vectorCount.toInt - 1)
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
    forAll(Gen.choose(0, space.vectorCount.toInt - 1)) { i: Int =>
      space.intToVector(i, ary)
      val i1 = space.vectorToInt(ary)
      i1 == i
    }
  }

  property("incInPlace is like adding 1") {
    val ary = new Array[Int](dim)
    forAll(Gen.choose(0, space.vectorCount.toInt - 1)) { i: Int =>
      space.intToVector(i, ary)
      space.incInPlace(ary)
      val i1 = space.vectorToInt(ary)
      i1 == (i + 1)
    }
  }
}
