package org.bykn.mubs

import algebra.ring.Ring
import org.scalacheck.Prop.forAll
import spire.math.{Complex, Real}
import org.scalacheck.Gen

class VectorSpaceLaws extends munit.ScalaCheckSuite {
  val dim = 6

  val space = new VectorSpace.Space[Cyclotomic.N3, Cyclotomic.L3](dim, 20)

  val genInt: Gen[Int] =
    Gen.choose(0, space.standardCount - 1)

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

  test("eps = 2 d sin(pi/n) when n > 1, else 2d") {
    val expectedEps =
      Real(2 * dim) * Real.sin(Real.pi / space.C.roots.length)
    assert(space.eps == expectedEps, s"${space.eps} != $expectedEps")
  }

  property("trace is invariant to shuffle") {
    val genPair: Gen[(Array[Int], Array[Int])] =
      genVec.flatMap { v => shuffle(v).map((v, _)) }

    forAll(genPair) { case (v1, v2) =>
      space.trace(v1) == space.trace(v2)
    }
  }

  property("conjProd + trace == dotAbs2") {
    val targ = new Array[Int](dim)
    forAll(genVec, genVec) { (v1, v2) =>
      space.conjProd(v1, v2, targ)

      space.trace(targ) == space.dotAbs2(v1, v2)
    }
  }

  property("dotAbs2(x, x) = d^2") {
    forAll(genVec) { v =>
      assert(space.dotAbs2(v, v) == Real(dim*dim))
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

  property("dotAbs2 is symmetric") {
    forAll(genVec, genVec) { (v1, v2) =>
      assert(space.dotAbs2(v1, v2) == space.dotAbs2(v2, v1))
    }
  }

  property("chooseN(n, x) returns x.length^n items each with exactly n items and no duplicates") {
    forAll(Gen.choose(0, 4), Gen.choose(0, 10).flatMap(Gen.listOfN(_, Gen.const(())))) { (n, x) =>
      // zipWithIndex to make each item unique
      val items = VectorSpace.chooseN(n, x.zipWithIndex).toList
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

  /**
   * Some tests with smaller spaces that we can afford to examine
   */
  val space2 = new VectorSpace.Space[Cyclotomic.N5, Cyclotomic.L5](2, 20)

  test("allMubVectors are all unbiased to each other and 0") {
    val ubBitSet = space2.buildCache(space2.isUnbiased)
    val nextFn = space2.nextFn(ubBitSet)

    (0 until space2.standardCount).foreach { v =>
      val v1 = nextFn(v)

      assert(ubBitSet.get(v1) || (v1 >= space2.standardCount), s"v = $v, v1 = $v1, count = ${space2.standardCount}")
    }

    (1 to 3).foreach { mubSize =>
      space2
        .allMubVectors(mubSize)
        .foreach { mubSet =>
          val z = space2.zeroVec()
          val vv1 = space2.zeroVec()

          val nonStandards = mubSet.filter(_ >= space2.standardCount).toList
          val allOrth0 = Cliques.allNodes[Int](nextFn(0), nextFn, { i => i >= (space2.standardCount - 1) }).toList
          assert(nonStandards == Nil, s"non-standards: $nonStandards, ${mubSet.toList}, allOrth0 = $allOrth0")

          mubSet.foreach { v =>
            // all mubs are standard:
            space2.intToVector(v, vv1)
            assert(vv1(vv1.length - 1) == 0, s"last = ${vv1(vv1.length - 1)}")
            assert(ubBitSet.get(v), s"v = $v")
            assert(space2.maybeUnbiased(z, vv1), s"${vv1.toList}")
          }

          val vv2 = space2.zeroVec()
          VectorSpace.allDistinctPairs(mubSet.toList)
            .foreach { case (v1, v2) =>
              space2.intToVector(v1, vv1)
              space2.intToVector(v2, vv2)
              assert(space2.maybeUnbiased(vv1, vv2))
              assert(space2.maybeUnbiased(vv2, vv1))
            }
        }
    }
  }

  //
  // Here we check some of the properties for the case of d = 3
  // where we can make a construction
  def expITheta(theta: Real): Complex[Real] =
    Complex(Real.cos(theta), Real.sin(theta))

  val unit = Complex(Real.one, Real.zero)
  val w3 = expITheta(Real(2) * Real.pi / Real(3))
  val w3_2 = w3.pow(2)

  //[1 1 1]
  //[1 w w2]
  //[1 w2 w]

  val h1 = List(
    List(unit, unit, unit),
    List(unit, w3, w3_2),
    List(unit, w3_2, w3))

  val h2 = List(
    List(unit, w3, w3),
    List(unit, w3_2, unit),
    List(unit, unit, w3_2))

  val h3 = List(
    List(unit, w3_2, w3_2),
    List(unit, unit, w3),
    List(unit, w3, unit))

  def dot2(v1: List[Complex[Real]], v2: List[Complex[Real]]): Real =
    Ring[Complex[Real]]
      .sum(v1.zip(v2).map { case (c1, c2) =>
        c1.conjugate * c2
      }).absSquare

  def isUB(v1: List[Complex[Real]], v2: List[Complex[Real]], d: Int): Boolean =
    dot2(v1, v2) == Real(d)

  implicit val ordReal: Ordering[Real] =
    new Ordering[Real] {
      def compare(r1: Real, r2: Real) = r1.compare(r2)
    }

  def nearest(r: Complex[Real], discrete: Iterable[Complex[Real]]): Complex[Real] =
    discrete.minBy { d => (r - d).absSquare }

  def isOrthBasis(basis: List[List[Complex[Real]]]): Boolean =
    VectorSpace.allDistinctPairs(basis)
      .forall { case (v1, v2) =>
        dot2(v1, v2) == Real.zero
      }

  def areUnbiased(basis1: List[List[Complex[Real]]], basis2: List[List[Complex[Real]]]): Boolean = {
    val d = basis1.head.size

    basis1.forall { v1 =>
      basis2.forall { v2 =>
        isUB(v1, v2, d)
      }
    }
  }

  test("given construction is unbiased for d = 3") {
    val bases = List(h1, h2, h3)
    bases.foreach { b =>
      assert(isOrthBasis(b))
    }

    VectorSpace.allDistinctPairs(bases)
      .foreach { case (b1, b2) =>
        assert(areUnbiased(b1, b2))
      }
  }

  test("Space detects standard d=3 mubs with n=32") {
    val space5 = new VectorSpace.Space[Cyclotomic.N5, Cyclotomic.L5](3, 20)
    def isApproxOrthBasis(basis: List[List[Complex[Real]]]): Boolean =
      VectorSpace.allDistinctPairs(basis)
        .forall { case (v1, v2) =>
          space5.isOrth(dot2(v1, v2))
        }

    def areApproxUnbiased(basis1: List[List[Complex[Real]]], basis2: List[List[Complex[Real]]]): Boolean = {
      val d = basis1.head.size

      basis1.forall { v1 =>
        basis2.forall { v2 =>
          space5.isUnbiased(dot2(v1, v2))
        }
      }
    }

    val bases = List(h1, h2, h3)
    bases.foreach { b =>
      assert(isApproxOrthBasis(b))
    }

    VectorSpace.allDistinctPairs(bases)
      .foreach { case (b1, b2) =>
        assert(areApproxUnbiased(b1, b2))
      }
  }

  property("if we quantize to nearest root of unity, the inner product error is <= 2|<u, v>| eps + eps^2 with eps = 2d sin(pi/n)") {

    case class Example(v1: List[Complex[Real]], v2: List[Complex[Real]], nth: Int) {
      require(v1.length == v2.length)
      require(nth >= 1)

      val d = v1.length

      val roots = (0 until nth).map { i => expITheta(Real(2*i) * Real.pi / Real(nth)) }

      val quantV1 = v1.map(nearest(_, roots))
      val quantV2 = v2.map(nearest(_, roots))

      // the magnitude difference
      val mag = dot2(v1, v2)
      val quantMag = dot2(quantV1, quantV2)

      // here is the theorem of the paper:
      val diff = (mag - quantMag).abs

      def explain: String =
        List(
          s"n = $nth",
          s"v1 = $v1",
          s"v2 = $v2",
          s"quantV1 = $quantV1",
          s"quantV2 = $quantV2",
          s"mag = $mag",
          s"quantMag = $quantMag",
          s"diff = $diff",
          s"gap = ${diff - eps}"
        ).mkString("\n")

      val gamma = if (nth == 1) Real(2*d) else Real(2*d) * Real.sin(Real.pi / nth)
      val eps = mag.sqrt * gamma * Real(2) + gamma.pow(2)
      val law = diff.compare(eps) <= 0
    }

    val genRoot: Gen[Complex[Real]] =
      Gen.choose(0, Int.MaxValue)
        .map { i => expITheta(Real(i) * Real.pi * Real.two / Real(Int.MaxValue)) }

    def genVec(d: Int): Gen[List[Complex[Real]]] =
      Gen.listOfN(d, genRoot)

    val genExample: Gen[Example] =
      for {
        d <- Gen.choose(1, 10)
        gv = genVec(d)
        v1 <- gv
        v2 <- gv
        n <- Gen.choose(1, 64)
      } yield Example(v1, v2, n)

    forAll(genExample) { ex =>
      if (!(ex.law)) {
        println(ex.explain)
      }

      ex.law
    }
  }
}
