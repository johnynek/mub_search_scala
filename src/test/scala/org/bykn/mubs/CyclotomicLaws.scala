package org.bykn.mubs

import spire.math.{Complex, Real}
import org.scalacheck.{Arbitrary, Gen}
import org.scalacheck.Prop.forAll

abstract class CyclotomicLaws[N <: BinNat, C](implicit cyclotomic: Cyclotomic[N, C], N: BinNat.FromType[N]) extends munit.ScalaCheckSuite {

  def depth: String = N.value.toString + " " + getClass.getName

  val twoM: Int = N.value.toBigInt.toInt

  lazy val gen: Gen[C] = {
    val rec = Gen.lzy(gen)

    def op(fn: (C, C) => C): Gen[C] =
      Gen.zip(rec, rec).map { case (a, b) => fn(a, b) }

    Gen.frequency(
      (3, Gen.const(cyclotomic.zero)),
      (3, Gen.const(cyclotomic.one)),
      (3, Gen.const(cyclotomic.omega)),
      (1, op(cyclotomic.plus(_, _))),
      (1, op(cyclotomic.minus(_, _))),
      (1, op(cyclotomic.times(_, _))))
  }

  implicit lazy val arbCyc: Arbitrary[C] =
    Arbitrary(gen)

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
    val theta = Real.pi * 2 / twoM
    assert(cyclotomic.reOmega == Real.cos(theta))
    assert(cyclotomic.imOmega == Real.sin(theta))
  }

  test(s"C$depth omega ^ (2^m) == 1") {

    val shouldBeOne = cyclotomic.pow(cyclotomic.omega, twoM)
    assert(shouldBeOne == cyclotomic.one)

    if (twoM > 1) {
      val shouldBeNOne = cyclotomic.pow(cyclotomic.omega, twoM / 2)
      assert(shouldBeNOne == cyclotomic.negate(cyclotomic.one))
    }
  }

  if (twoM > 1) {
    test(s"C$depth sum of all roots is 0") {
      val left = cyclotomic.roots.reduce(cyclotomic.plus(_, _))
      assert(left == cyclotomic.zero, cyclotomic.toComplex(left).toString)
    }
  }

  test(s"C$depth abs2(omega) == 1") {
    val one = cyclotomic.abs2(cyclotomic.omega)
    assert(one == Real.one, one.toString)
  }

  test(s"C$depth toComplex(omega).sqrt == reOmega + i*imOmega") {
    val rootOmega = cyclotomic.toComplex(cyclotomic.omega)
    assert(rootOmega.real.compare(cyclotomic.reOmega) == 0, s"${rootOmega.real} != ${cyclotomic.reOmega}")
    assert(rootOmega.imag.compare(cyclotomic.imOmega) == 0, s"${rootOmega.imag} != ${cyclotomic.imOmega}")
  }
}

class CyclotomicLaws2 extends CyclotomicLaws[BinNat._2, Cyclotomic.C2]
class CyclotomicLaws4 extends CyclotomicLaws[BinNat._4, Cyclotomic.C4]
class CyclotomicLaws8 extends CyclotomicLaws[BinNat._8, Cyclotomic.C8]
class CyclotomicLaws16 extends CyclotomicLaws[BinNat._16, Cyclotomic.C16]
class CyclotomicLaws32 extends CyclotomicLaws[BinNat._32, Cyclotomic.C32]

class CyclotomicLawsL2 extends CyclotomicLaws[BinNat._2, Cyclotomic.L2]
class CyclotomicLawsL4 extends CyclotomicLaws[BinNat._4, Cyclotomic.L4]
class CyclotomicLawsL8 extends CyclotomicLaws[BinNat._8, Cyclotomic.L8]
class CyclotomicLawsL16 extends CyclotomicLaws[BinNat._16, Cyclotomic.L16]
class CyclotomicLawsL32 extends CyclotomicLaws[BinNat._32, Cyclotomic.L32]
