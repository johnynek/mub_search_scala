package org.bykn.mubs

import spire.math.{Complex, Real}
import org.scalacheck.{Arbitrary, Gen}
import org.scalacheck.Prop.forAll

abstract class CyclotomicLaws[N <: BinNat, C](implicit cyclotomic0: => Cyclotomic[N, C], ft: BinNat.FromType[N]) extends munit.ScalaCheckSuite {

  override def scalaCheckTestParameters =
    super.scalaCheckTestParameters
      .withMinSuccessfulTests(500)
      .withMaxDiscardRatio(10)

  lazy val cyclotomic = cyclotomic0

  test("print the string") {
    println(cyclotomic.toString)
  }

  val roots: Int = cyclotomic.roots.length

  def depth: String = roots.toString + " " + getClass.getName

  lazy val gen: Gen[C] = {
    val rec = Gen.lzy(gen)

    def op(fn: (C, C) => C): Gen[C] =
      Gen.zip(rec, rec).map { case (a, b) => fn(a, b) }

    Gen.frequency(
      (1, Gen.const(cyclotomic.zero)),
      (4, Gen.choose(0, roots - 1).map(cyclotomic.roots(_))),
      (2, rec.map(cyclotomic.negate(_))),
      (1, op(cyclotomic.plus(_, _))),
      (1, op(cyclotomic.minus(_, _))),
      (1, op(cyclotomic.times(_, _))))
  }

  implicit lazy val arbCyc: Arbitrary[C] =
    Arbitrary(gen)

  test("roots matches N") {
    assert(roots == ft.value.toBigInt.toInt)
  }

  property(s"C$depth cyclotomic plus is associative") {
    forAll { (a: C, b: C, c: C) =>
      cyclotomic.plus(a, cyclotomic.plus(b, c)) ==
        cyclotomic.plus(cyclotomic.plus(a, b), c)
    }
  }

  property(s"C$depth cyclotomic times is associative") {
    forAll { (a: C, b: C, c: C) =>
      cyclotomic.times(a, cyclotomic.times(b, c)) ==
        cyclotomic.times(cyclotomic.times(a, b), c)
    }
  }

  property(s"C$depth cyclotomic plus is commutative") {
    forAll { (a: C, b: C) =>
      cyclotomic.plus(a, b) == cyclotomic.plus(b, a)
    }
  }

  property(s"C$depth cyclotomic times is commutative") {
    forAll { (a: C, b: C) =>
      cyclotomic.times(a, b) == cyclotomic.times(b, a)
    }
  }

  property(s"C$depth cyclotomic a + 0 = a") {
    forAll { a: C =>
      cyclotomic.plus(a, cyclotomic.zero) == a
    }
  }

  property(s"C$depth cyclotomic a * 0 = 0") {
    forAll { a: C =>
      cyclotomic.times(a, cyclotomic.zero) == cyclotomic.zero
    }
  }

  property(s"C$depth cyclotomic a * w = timesOmega(a)") {
    forAll { a: C =>
      cyclotomic.times(a, cyclotomic.omega) == cyclotomic.timesOmega(a)
    }
  }

  property(s"C$depth cyclotomic a * 1 = a") {
    forAll { a: C =>
      cyclotomic.times(a, cyclotomic.one) == a
    }
  }

  property(s"C$depth a - a == 0") {
    forAll { (a: C) =>
      cyclotomic.minus(a, a) == cyclotomic.zero
    }
  }

  property(s"C$depth (a + b) * c == a*c + b*c") {
    forAll { (a: C, b: C, c: C) =>
      val ab = cyclotomic.plus(a, b)
      val left = cyclotomic.times(ab, c)
      val right = cyclotomic.plus(cyclotomic.times(a, c), cyclotomic.times(b, c))

      left == right
    }
  }

  property(s"C$depth abs2(c) == re(c)^2 + im(c)^2") {
    forAll { (c: C) =>
      val left = cyclotomic.abs2(c)
      val right = cyclotomic.re(c).pow(2) + cyclotomic.im(c).pow(2)
      left == right
    }
  }

  property(s"C$depth triangle inequality") {
    forAll { (a: C, b: C) =>
      val plus = cyclotomic.plus(a, b)
      val abs = cyclotomic.abs2(plus).sqrt

      assert(abs.compare(cyclotomic.abs2(a).sqrt + cyclotomic.abs2(b).sqrt) <= 0)
    }
  }

  test(s"C$depth omega = cos(2 pi / n) + i sin(2 pi / n)") {
    val theta = Real.pi * Real.two / Real(roots)
    assert(cyclotomic.reOmega == Real.cos(theta), s"${cyclotomic.reOmega} != ${Real.cos(theta)}")
    assert(cyclotomic.imOmega == Real.sin(theta))
  }

  val factors: List[Int] =
    (2 until roots).filter(roots % _ == 0).toList

  test(s"C$depth if $roots = a*b, sum_i {0..(b-1)} omega ^ (a*i) == 0") {

    val shouldBeOne = cyclotomic.pow(cyclotomic.omega, roots)
    assert(shouldBeOne == cyclotomic.one, s"$shouldBeOne != ${cyclotomic.one}")

    factors.foreach { factor =>
      val pow = roots / factor
      val sring = cyclotomic
        .sum(
          (0 until pow)
            .map { p =>
              cyclotomic.pow(cyclotomic.omega, factor * p)
            })

      assert(cyclotomic.toComplex(sring) == Real.zero, s"$sring != ${cyclotomic.zero}, $pow * $factor == $roots")
      //assert(sring == cyclotomic.zero, s"$sring != ${cyclotomic.zero}, $pow * $factor == $roots")
    }
  }

  /*
   * this isn't true unfortunately
  property("C$depth there is only one representation of zero") {
    forAll { c: C =>
      val cComp = cyclotomic.toComplex(c)
      assert((cComp == Real.zero) == (c == cyclotomic.zero), s"cComp = $cComp, c = $c")
    }
  }
  */

  test(s"C$depth sum of all roots is 0") {
    val left = cyclotomic.roots.reduce(cyclotomic.plus(_, _))
    assert(left == cyclotomic.zero, cyclotomic.toComplex(left).toString)
  }

  test(s"C$depth abs2(omega) == 1") {
    val one = cyclotomic.abs2(cyclotomic.omega)
    assert(one == Real.one, one.toString)
  }

  test(s"C$depth abs2(root) == 1") {
    cyclotomic.roots.foreach { r =>
      val one = cyclotomic.abs2(r)
      assert(one == Real.one, one.toString)
    }
  }

  test(s"C$depth toComplex(omega).sqrt == reOmega + i*imOmega") {
    val rootOmega = cyclotomic.toComplex(cyclotomic.omega)
    assert(rootOmega.real.compare(cyclotomic.reOmega) == 0, s"${rootOmega.real} != ${cyclotomic.reOmega}")
    assert(rootOmega.imag.compare(cyclotomic.imOmega) == 0, s"${rootOmega.imag} != ${cyclotomic.imOmega}")
  }
}

class CyclotomicLaws2 extends CyclotomicLaws[BinNat._2, Cyclotomic.C2]
//class CyclotomicLaws3 extends CyclotomicLaws[BinNat._3, Cyclotomic.C3]
class CyclotomicLaws4 extends CyclotomicLaws[BinNat._4, Cyclotomic.C4]
class CyclotomicLaws6 extends CyclotomicLaws[BinNat._6, Cyclotomic.C6]
// class CyclotomicLaws8 extends CyclotomicLaws[BinNat._8, Cyclotomic.C8]
class CyclotomicLaws12 extends CyclotomicLaws[BinNat._12, Cyclotomic.C12]
class CyclotomicLaws16 extends CyclotomicLaws[BinNat._16, Cyclotomic.C16]
// class CyclotomicLaws18 extends CyclotomicLaws[BinNat._18, Cyclotomic.C18]
// class CyclotomicLaws24 extends CyclotomicLaws[BinNat._24, Cyclotomic.C24]
// class CyclotomicLaws27 extends CyclotomicLaws[BinNat._27, Cyclotomic.C27]
// class CyclotomicLaws32 extends CyclotomicLaws[BinNat._32, Cyclotomic.C32]

class CyclotomicLawsL2 extends CyclotomicLaws[BinNat._2, Cyclotomic.L2]
//class CyclotomicLawsL3 extends CyclotomicLaws[BinNat._3, Cyclotomic.L3]
//class CyclotomicLawsL4 extends CyclotomicLaws[BinNat._4, Cyclotomic.L4]
////class CyclotomicLawsL5 extends CyclotomicLaws[BinNat._5, Cyclotomic.L5]
class CyclotomicLawsL6 extends CyclotomicLaws[BinNat._6, Cyclotomic.L6]
class CyclotomicLawsL8 extends CyclotomicLaws[BinNat._8, Cyclotomic.L8]
class CyclotomicLawsL9 extends CyclotomicLaws[BinNat._9, Cyclotomic.L9]
//class CyclotomicLawsL10 extends CyclotomicLaws[BinNat._10, Cyclotomic.L10]
class CyclotomicLawsL12 extends CyclotomicLaws[BinNat._12, Cyclotomic.L12]
//class CyclotomicLawsL15 extends CyclotomicLaws[BinNat._15, Cyclotomic.L15]
class CyclotomicLawsL16 extends CyclotomicLaws[BinNat._16, Cyclotomic.L16]
//class CyclotomicLawsL18 extends CyclotomicLaws[BinNat._18, Cyclotomic.L18]
//class CyclotomicLawsL20 extends CyclotomicLaws[BinNat._20, Cyclotomic.L20]
//class CyclotomicLawsL24 extends CyclotomicLaws[BinNat._24, Cyclotomic.L24]
//class CyclotomicLawsL27 extends CyclotomicLaws[BinNat._27, Cyclotomic.L27]
//class CyclotomicLawsL32 extends CyclotomicLaws[BinNat._32, Cyclotomic.L32]
