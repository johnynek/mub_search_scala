package org.bykn.mubs

import org.scalacheck.Gen
import org.scalacheck.Prop.forAll
import java.util.Random

class BinNatTests extends munit.ScalaCheckSuite {

  import BinNat._
  import FromType.value

  override def scalaCheckTestParameters =
    super.scalaCheckTestParameters
      .withMinSuccessfulTests(20000)
      .withMaxDiscardRatio(10)

  val upTo16 =
    (0 to 16).scanLeft(Zero: Value[BinNat]) { (b, _) => b.inc }.toVector

  def genValue(depth: Int): Gen[Value[BinNat]] = {
    if (depth <= 0) Gen.const(Zero)
    else {
      val rec = Gen.lzy(genValue(depth - 1))

      Gen.frequency(
        (1, Gen.oneOf(upTo16.take(depth * 2))),
        (4, Gen.const(Zero)),
        (1, Gen.zip(rec, rec).map { case (a, b) => a + b }),
        (1, Gen.zip(rec, rec).map { case (a, b) => a * b }),
        (2, rec.map(_.inc)))
    }
  }

  val genValue10: Gen[Value[BinNat]] = genValue(10)
  val genValue2: Gen[Value[BinNat]] = genValue(3)

  property("inc is a homomorphism with toBigInt") {
    forAll(genValue10) { a =>
      assert(a.inc.toBigInt == (a.toBigInt + 1))
    }
  }

  property("add is a homomorphism with toBigInt") {
    forAll(genValue10, genValue10) { (a, b) =>
      assert((a + b).toBigInt == (a.toBigInt + b.toBigInt))
    }
  }

  property("mult is a homomorphism with toBigInt") {
    forAll(genValue10, genValue10) { (a, b) =>
      assert((a * b).toBigInt == (a.toBigInt * b.toBigInt))
    }
  }

  property("pow is a homomorphism with toBigInt") {
    forAll(genValue10, genValue2) { (a, b) =>
      assert(a.pow(b).toBigInt == (a.toBigInt.pow(b.toBigInt.toInt)))
    }
  }

  property("powMod matches pow + %") {
    forAll(genValue10, genValue2, genValue10) { (a, p, m) =>
      assert(a.powMod(p, m) == (a.pow(p) % m))
    }
  }

  property("powMod matches BigInt modPow") {
    forAll(genValue10, genValue2, genValue10) { (a, p, m) =>
      if (m != BinNat.Zero) {
        assert(a.powMod(p, m).toBigInt == a.toBigInt.modPow(p.toBigInt, m.toBigInt))
      }
      else {
        assert(a.powMod(p, m) == a.pow(p))
      }
    }
  }

  property("- is a homomorphism with toBigInt") {
    forAll(genValue10, genValue10) { (a, b) =>
      val ba = a.toBigInt
      val bb = b.toBigInt
      if (ba >= bb) 
        assert((a - b).toBigInt == (ba - bb))
      else assert((a - b).toBigInt == BigInt(0), s"${a - b}")
    }
  }

  property("< is a homomorphism with toBigInt") {
    forAll(genValue10, genValue10) { (a, b) =>
      val ba = a.toBigInt
      val bb = b.toBigInt
      assert((a < b) == (ba < bb))
    }
  }

  property("divmod is lawful") {
    forAll(genValue10, genValue10) { (a, b) =>
      val (d, m) = a.divmod(b)
      val res = b * d + m
      assert(a == res, s"d = $d, m = $m")
      if (BinNat.Zero < b) {
        assert(a.toBigInt / b.toBigInt == d.toBigInt)
        assert(m < b, s"d = $d, m = $m")
      }
      else {
        assert(m == a)
        assert(d == Zero)
      }
    }
  }

  property("divmod._2 == %") {
    forAll(genValue10, genValue10) { (a, b) =>
      assert(a.divmod(b)._2 == (a % b))
    }
  }

  property("gcd is a homomorphism with toBigInt") {
    forAll(genValue10, genValue10) { (a, b) =>
      val bn = a.gcd(b)
      val ba = a.toBigInt
      val bb = b.toBigInt
      val bg = ba.gcd(bb)
      assert(bn.toBigInt == bg, s"$bn != $bg")

      val gcd1 = (a / bn).gcd(b / bn)
      if (a == BinNat.Zero && b == BinNat.Zero) {
        assert(gcd1 == BinNat.Zero)
      }
      else {
        assert(gcd1 == BinNat.Zero.inc)
      }
    }
  }

  property("bitCount is lawful") {
    forAll(genValue10) { b =>
      val bc = b.bitCount
      assert(b < BinNat._2.pow(bc))
      val lower = BinNat._2.pow(bc - BinNat._1)
      assert(b == BinNat.Zero || lower < b || (lower == b))
    }
  }
  

  property("toBigInt <-> valueFromBigInt is identity") {
    forAll(genValue10) { a =>
      assert(valueFromBigInt(a.toBigInt) == a)
    }
  }

  property("_2 * x == x.times2") {
    forAll(genValue10) { a =>
      assert(_2 * a == a.times2)
    }
  }

  property("x.dec = x - _1") {
    forAll(genValue10) { x =>
      assert(x.dec == (x - _1))
    }
  }

  property("random generates in bounds") {
    forAll(genValue10, Gen.choose(Long.MinValue, Long.MaxValue)) { (n, seed) =>
      val rand = BinNat.BoolGen.fromRandom(new Random(seed))

      val n1 = BinNat.random(rand, n)
      assert(n1 < n.inc, s"$n1 >= $n + 1")
    }
  }

  property("isProbablyPrime matches") {
    forAll(genValue10, Gen.choose(Long.MinValue, Long.MaxValue), Gen.choose(0, 50)) { (n, seed, k) =>
      val rand = BinNat.BoolGen.fromRandom(new Random(seed))
      assert(n.millerRabinPrime(rand, 2*k + 10) == n.toBigInt.isProbablePrime(2*k + 10))
    }
  }

  /*
   * this either doesn't work or is insanely slow
  */
  property("generating random primes works") {
    forAll(Gen.choose(2, 8), Gen.choose(Long.MinValue, Long.MaxValue)) { (bits0, seed) =>
      val bits = math.max(bits0, 2)
      val rand = BinNat.BoolGen.fromRandom(new Random(seed))

      val conf = 10
      val p = BinNat.randomPrime(rand, bits, conf)
      assert(p.bitCount == valueFromBigInt(bits), s"${p.bitCount} != $bits")
      assert(p.toBigInt.isProbablePrime(conf))
      assert(p.millerRabinPrime(rand, conf))
    }
  }

  test("some particular examples") {
    assert(value[_0].toBigInt == BigInt(0))
    assert(value[_1].toBigInt == BigInt(1))
    assert(value[_2].toBigInt == BigInt(2))
    assert(value[_3].toBigInt == BigInt(3))
    assert(value[_4].toBigInt == BigInt(4))
    assert(value[_5].toBigInt == BigInt(5))
  }

  test("test inc") {
    assert(implicitly[Inc.Aux[_0, _1]].apply(FromType.value[_0]) == FromType.value[_0].inc)
    assert(implicitly[Inc.Aux[_1, _2]].apply(FromType.value[_1]) == FromType.value[_1].inc)
    assert(implicitly[Inc.Aux[_2, _3]].apply(FromType.value[_2]) == FromType.value[_2].inc)
    assert(implicitly[Inc.Aux[_3, _4]].apply(FromType.value[_3]) == FromType.value[_3].inc)
    assert(implicitly[Inc.Aux[_4, _5]].apply(FromType.value[_4]) == FromType.value[_4].inc)
    assert(implicitly[Inc.Aux[_5, _6]].apply(FromType.value[_5]) == FromType.value[_5].inc)
  }

  test("test some negative examples: Inc") {
    assertNoDiff(
      compileErrors("implicitly[Inc.Aux[_0, _2]]"),
    """|error: could not find implicit value for parameter e: org.bykn.mubs.BinNat.Inc.Aux[org.bykn.mubs.BinNat._0,org.bykn.mubs.BinNat._2]
       |implicitly[Inc.Aux[_0, _2]]
       |          ^
       |""".stripMargin)

  }

  implicitly[Times2.Aux[_0, _0]]
  implicitly[Times2.Aux[_1, _2]]
  implicitly[Times2.Aux[_2, _4]]
  implicitly[Times2.Aux[_3, _6]]
  implicitly[Times2.Aux[_4, _8]]

  test("test some negative examples: Times2") {
    assertNoDiff(
      compileErrors("implicitly[Times2.Aux[_1, _3]]"),
    """|error: could not find implicit value for parameter e: org.bykn.mubs.BinNat.Times2.Aux[org.bykn.mubs.BinNat._1,org.bykn.mubs.BinNat._3]
       |implicitly[Times2.Aux[_1, _3]]
       |          ^
       |""".stripMargin)

  }

  test("test Add") {
    assert(implicitly[Add.Aux[_0, _0, _0]].apply(value[_0], value[_0]) == (value[_0] + value[_0]))
    assert(implicitly[Add.Aux[_0, _1, _1]].apply(value[_0], value[_1]) == (value[_0] + value[_1]))
    assert(implicitly[Add.Aux[_1, _0, _1]].apply(value[_1], value[_0]) == (value[_1] + value[_0]))
    assert(implicitly[Add.Aux[_1, _1, _2]].apply(value[_1], value[_1]) == (value[_1] + value[_1]))
    assert(implicitly[Add.Aux[_2, _0, _2]].apply(value[_2], value[_0]) == (value[_2] + value[_0]))
    assert(implicitly[Add.Aux[_0, _2, _2]].apply(value[_0], value[_2]) == (value[_0] + value[_2]))
    assert(implicitly[Add.Aux[_2, _1, _3]].apply(value[_2], value[_1]) == (value[_2] + value[_1]))
    assert(implicitly[Add.Aux[_1, _2, _3]].apply(value[_1], value[_2]) == (value[_1] + value[_2]))
    assert(implicitly[Add.Aux[_2, _2, _4]].apply(value[_2], value[_2]) == (value[_2] + value[_2]))
    assert(implicitly[Add.Aux[_3, _0, _3]].apply(value[_3], value[_0]) == (value[_3] + value[_0]))
    assert(implicitly[Add.Aux[_0, _3, _3]].apply(value[_0], value[_3]) == (value[_0] + value[_3]))
    assert(implicitly[Add.Aux[_2, _3, _5]].apply(value[_2], value[_3]) == (value[_2] + value[_3]))
    assert(implicitly[Add.Aux[_3, _2, _5]].apply(value[_3], value[_2]) == (value[_3] + value[_2]))
    assert(implicitly[Add.Aux[_3, _3, _6]].apply(value[_3], value[_3]) == (value[_3] + value[_3]))
    assert(implicitly[Add.Aux[_4, _1, _5]].apply(value[_4], value[_1]) == (value[_4] + value[_1]))
    assert(implicitly[Add.Aux[_1, _4, _5]].apply(value[_1], value[_4]) == (value[_4] + value[_1]))
    assert(implicitly[Add.Aux[_4, _2, _6]].apply(value[_4], value[_2]) == (value[_4] + value[_2]))
    assert(implicitly[Add.Aux[_2, _4, _6]].apply(value[_2], value[_4]) == (value[_4] + value[_2]))
    assert(implicitly[Add.Aux[_4, _3, _7]].apply(value[_4], value[_3]) == (value[_4] + value[_3]))
    assert(implicitly[Add.Aux[_3, _4, _7]].apply(value[_3], value[_4]) == (value[_4] + value[_3]))
    assert(implicitly[Add.Aux[_4, _4, _8]].apply(value[_4], value[_4]) == (value[_4] + value[_4]))
  }


  test("test some negative examples: Add") {
    assertNoDiff(
      compileErrors("implicitly[Add.Aux[_0, _2, _3]]"),
    """|error: could not find implicit value for parameter e: org.bykn.mubs.BinNat.Add.Aux[org.bykn.mubs.BinNat._0,org.bykn.mubs.BinNat._2,org.bykn.mubs.BinNat._3]
       |implicitly[Add.Aux[_0, _2, _3]]
       |          ^
       |""".stripMargin)

  }

  test("test Mult") {
    implicitly[Mult.Aux[_0, _0, _0]]
    implicitly[Mult.Aux[_0, _1, _0]]
    implicitly[Mult.Aux[_1, _0, _0]]
    implicitly[Mult.Aux[_1, _1, _1]]
    implicitly[Mult.Aux[_1, _2, _2]]
    implicitly[Mult.Aux[_2, _2, _4]]
    implicitly[Mult.Aux[_3, _1, _3]]
    implicitly[Mult.Aux[_1, _3, _3]]
    implicitly[Mult.Aux[_3, _2, _6]]
    implicitly[Mult.Aux[_2, _3, _6]]
    implicitly[Mult.Aux[_3, _3, _9]]
    implicitly[Mult.Aux[_4, _1, _4]]
    implicitly[Mult.Aux[_1, _4, _4]]
    implicitly[Mult.Aux[_4, _2, _8]]
    implicitly[Mult.Aux[_2, _4, _8]]
    implicitly[Mult.Aux[_4, _3, _12]]
    implicitly[Mult.Aux[_3, _4, _12]]
    implicitly[Mult.Aux[_4, _4, _16]]


    assert(Mult(value[_0], value[_0]) == (value[_0] * value[_0]))
    assert(Mult(value[_1], value[_0]) == (value[_1] * value[_0]))
    assert(Mult(value[_0], value[_1]) == (value[_1] * value[_0]))
    assert(Mult(value[_1], value[_1]) == value[_1])
    assert(Mult(value[_2], value[_1]) == value[_2])
    assert(Mult(value[_1], value[_2]) == value[_2])
    assert(Mult(value[_2], value[_2]) == value[_4])
    assert(Mult(value[_2], value[_3]) == value[_6])
    assert(Mult(value[_3], value[_2]) == value[_6])
    assert(Mult(value[_3], value[_4]) == value[_12])
    assert(Mult(value[_4], value[_3]) == value[_12])

    assert(Mult(value[_32], value[_32]) == (value[_32] * value[_32]))
  }

  test("test some negative examples: Mult") {
    assertNoDiff(
      compileErrors("implicitly[Mult.Aux[_0, _2, _3]]"),
    """|error: could not find implicit value for parameter e: org.bykn.mubs.BinNat.Mult.Aux[org.bykn.mubs.BinNat._0,org.bykn.mubs.BinNat._2,org.bykn.mubs.BinNat._3]
       |implicitly[Mult.Aux[_0, _2, _3]]
       |          ^
       |""".stripMargin)

  }


  test("test Pow") {
    assert(implicitly[Pow.Aux[_0, _0, _1]].apply(value[_0], value[_0]) == value[_0].pow(value[_0]))
    assert(implicitly[Pow.Aux[_0, _1, _0]].apply(value[_0], value[_1]) == value[_0].pow(value[_1]))
    assert(implicitly[Pow.Aux[_1, _0, _1]].apply(value[_1], value[_0]) == value[_1].pow(value[_0]))

    assert(implicitly[Pow.Aux[_2, _2, _4]].apply(value[_2], value[_2]) == value[_2].pow(value[_2]))
    assert(implicitly[Pow.Aux[_2, _3, _8]].apply(value[_2], value[_3]) == value[_2].pow(value[_3]))

    // try some really large examples:

    val fourBil = implicitly[Pow[_2, _32]]

    assert(fourBil(value[_2], value[_32]) == valueFromBigInt(BigInt(1) << 32))
  }
}
