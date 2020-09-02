package org.bykn.mubs

import shapeless.ops.nat
import shapeless.Nat
import org.scalacheck.{Arbitrary, Gen}
import org.scalacheck.Prop.forAll

abstract class CyclotomicLaws[N <: Nat, C](implicit cyclotomic: Cyclotomic[N, C], nToInt: nat.ToInt[N]) extends munit.ScalaCheckSuite {

  def depth: String = nToInt().toString

  val twoM: Int = 1 << nToInt()

  lazy val gen: Gen[C] = {
    val rec = Gen.lzy(gen)

    def op(fn: (C, C) => C): Gen[C] =
      Gen.zip(rec, rec).map { case (a, b) => fn(a, b) }

    Gen.frequency(
      (3, Gen.const(cyclotomic.zero)),
      (3, Gen.const(cyclotomic.one)),
      (3, Gen.const(cyclotomic.omega)),
      (1, op(cyclotomic.add(_, _))),
      (1, op(cyclotomic.sub(_, _))),
      (1, op(cyclotomic.mult(_, _))))
  }

  implicit lazy val arbCyc: Arbitrary[C] =
    Arbitrary(gen)

  property(s"C$depth cyclotomic add is associative") {
    forAll { (a: C, b: C, c: C) =>
      cyclotomic.add(a, cyclotomic.add(b, c)) ==
        cyclotomic.add(cyclotomic.add(a, b), c)
    }
  }

  property(s"C$depth cyclotomic mult is associative") {
    forAll { (a: C, b: C, c: C) =>
      cyclotomic.mult(a, cyclotomic.mult(b, c)) ==
        cyclotomic.mult(cyclotomic.mult(a, b), c)
    }
  }

  property(s"C$depth cyclotomic add is commutative") {
    forAll { (a: C, b: C) =>
      cyclotomic.add(a, b) == cyclotomic.add(b, a)
    }
  }

  property(s"C$depth cyclotomic mult is commutative") {
    forAll { (a: C, b: C) =>
      cyclotomic.mult(a, b) == cyclotomic.mult(b, a)
    }
  }

  property(s"C$depth cyclotomic a + 0 = a") {
    forAll { a: C =>
      cyclotomic.add(a, cyclotomic.zero) == a
    }
  }

  property(s"C$depth cyclotomic a * 0 = 0") {
    forAll { a: C =>
      cyclotomic.mult(a, cyclotomic.zero) == cyclotomic.zero
    }
  }

  property(s"C$depth cyclotomic a * 1 = a") {
    forAll { a: C =>
      cyclotomic.mult(a, cyclotomic.one) == a
    }
  }

  property(s"C$depth a - a == 0") {
    forAll { (a: C) =>
      cyclotomic.sub(a, a) == cyclotomic.zero
    }
  }

  property(s"C$depth (a + b) * c == a*c + b*c") {
    forAll { (a: C, b: C, c: C) =>
      val ab = cyclotomic.add(a, b)
      val left = cyclotomic.mult(ab, c)
      val right = cyclotomic.add(cyclotomic.mult(a, c), cyclotomic.mult(b, c))

      left == right
    }
  }

  test(s"C$depth omega ^ (2^m) == 1") {

    def pow(c: C, n: Int): C =
      if (n <= 0) c
      else pow(cyclotomic.mult(cyclotomic.omega, c), n - 1)

    val shouldBeOne = pow(cyclotomic.one, twoM)
    assert(shouldBeOne == cyclotomic.one)

    if (twoM > 1) {
      val shouldBeNOne = pow(cyclotomic.one, twoM / 2)
      assert(shouldBeNOne == cyclotomic.sub(cyclotomic.zero, cyclotomic.one))
    }
  }
}

class CyclotomicLaws0 extends CyclotomicLaws[Cyclotomic.N0, Cyclotomic.C0]
class CyclotomicLaws1 extends CyclotomicLaws[Cyclotomic.N1, Cyclotomic.C1]
class CyclotomicLaws2 extends CyclotomicLaws[Cyclotomic.N2, Cyclotomic.C2]
class CyclotomicLaws3 extends CyclotomicLaws[Cyclotomic.N3, Cyclotomic.C3]
class CyclotomicLaws4 extends CyclotomicLaws[Cyclotomic.N4, Cyclotomic.C4]
