package org.bykn.mubs

/**
 * Represents a type to hold a number in a binary
 * representation, so compilation is relatively
 * fast compared to the naive Zero, Succ representation
 *
 * There are no values of type BinNat, instead
 * we can get values of type Value[B <: BinNat] for
 * each valid nat.
 */
sealed trait BinNat

import java.util.Random
import java.security.SecureRandom

object BinNat {

  val _1 = succ1(Zero) 
  val _2 = succ2(Zero) 

  trait BoolGen {
    def nextBoolean(): Boolean
  }

  object BoolGen {
    def fromRandom(r: Random): BoolGen =
      new BoolGen {
        def nextBoolean() = r.nextBoolean()
      }

    def fromSecureRandom(sr: SecureRandom): BoolGen =
      new BoolGen {
        val buf = new Array[Byte](32)
        val maxPos = 32 * 8
        var pos = maxPos

        def nextBoolean(): Boolean = {
          if (pos < maxPos) {
            val byte = pos >> 3
            val bit = pos & 0x7
            pos += 1
            ((buf(byte).toInt >> bit) & 1) == 1
          }
          else {
            sr.nextBytes(buf)
            pos = 0
            nextBoolean()
          }
        }
      }

    def secure(): BoolGen =
      fromSecureRandom(SecureRandom.getInstanceStrong())
  }

  /**
   * Values correspond the actual numbers of a given type
   */
  sealed abstract class Value[+B <: BinNat] {
    def toBigInt: BigInt
    override def toString = toBigInt.toString

    def inc: Value[BinNat]
    def +(that: Value[BinNat]): Value[BinNat]
    def *(that: Value[BinNat]): Value[BinNat]
    def pow(that: Value[BinNat]): Value[BinNat] =
      that match {
        case Zero => _1
        case B1(p1) =>
          if (p1 eq Zero) this
          else {
            // x^(2n + 1) = x * (x^n)^2
            val y = pow(p1)
            this * y * y
          }
        case B2(p1) =>
          // x^(2n + 2) = (x^(n + 1))^2
          val y = pow(p1.inc)
          y * y
      }

    def <(that: Value[BinNat]): Boolean =
      (this: Value[BinNat]) match {
        case Zero =>
          that match {
            case Zero => false
            case _ => true
          }
        case B1(n) =>
          // 2n + 1
          that match {
            case Zero => false
            case B1(m) => n < m
            case B2(m) =>
              // 2n + 1 < 2m + 2
              // if 2n < 2m + 1
              // whicn is n <= m
              !(m < n)
            }
        case B2(n) =>
          // 2n + 2
          that match {
            case Zero => false
              // both cases result in the same
              // condition:
              //
              // 2n + 2 < 2m + 1
              // is 2n < 2m - 1
              // n <= (m - 1)
              //
              // 2n + 2 < 2m + 2
            case B1(m) => n < m
            case B2(m) => n < m
          }
      }

    def -(that: Value[BinNat]): Value[BinNat] =
      (this: Value[BinNat]) match {
        case Zero => Zero
        case B1(n) =>
          that match {
            case Zero => this
            case B1(m) =>
              // 2n + 1 - (2m + 1) = 2(n - m)
              (n - m).times2
            case B2(m) =>
              // 2n + 1 - (2m + 2) = 2(n - m) - 1
              (n - m).times2.dec
          }
        case B2(n) =>
          that match {
            case Zero => this
            case B1(m) =>
              // 2n + 2 - (2m + 1) = 2(n - m) + 1
              if (this < that) Zero
              else succ1(n - m)
            case B2(m) =>
              // 2n + 2 - (2m + 2) = 2(n - m)
              (n - m).times2
          }
      }

    def times2: Value[BinNat] =
      (this: Value[BinNat]) match {
        case Zero => Zero
        case B1(n) =>
          // (2n + 1) * 2 = 2(2n) + 2
          succ2(n.times2)
        case B2(n) =>
          // (2n + 2) * 2 = 4n + 4
          // 2(2n + 1) + 2
          succ2(succ1(n))
      }
    // n divmod m = (d, r)
    // then n = d * m + r
    // and r < n or m = 0
    def divmod(that: Value[BinNat]): (Value[BinNat], Value[BinNat]) =
      (this: Value[BinNat], that) match {
        case (_, Zero) => (Zero, this)
        case (Zero, _) => (Zero, Zero)
        case (_, B1(Zero)) => (this, Zero)
        case (B1(Zero), _) =>
          // we know that > 1
          (Zero, _1)
        case (B2(Zero), _) =>
          that match {
            case B2(Zero) => (_1, Zero)
            case _ =>
              // 2 / n where n > 2
              (Zero, _2)
          }
        case (B2(n), B2(m)) =>
          // (2n1 + 2) / (2n2 + 2) = (n1 + 1) / (n2 + 1)
          // if n mod m = x
          // then 2n mod 2m = 2x
          //
          val (d, r) = n.inc.divmod(m.inc)
          (d, r.times2)
        case (B1(n), _) =>
          // (2n + 1) / that =
          // 2n / that = d1 m + r1
          // 1 / that = d2 m + r2 = 0*m + 1 (because that > 1) 
          // 
          // 2n/that = 2*(n/that) =
          // n/that = d3 m + r3
          val (d3, r3) = n.divmod(that)
          var d = d3.times2
          // r = 2r3 + 1 = succ1(r3)
          var r: Value[BinNat] = succ1(r3)
          // since r3 < that, 2r3 + 1 < 2that + 1
          // so we could have to subtract that twice
          while(!(r < that)) {
            r = r - that
            d = d.inc
          }
          (d, r)
        case (B2(n), _) =>
          // (2n + 2) / that
          //  == 2 * ((n + 1) / that)
          val (d, r) = n.inc.divmod(that)
          // n + 1 = d2 * that + r2
          // 2n + 2 = 2*d2*that + 2*r2
          //
          val r2 = r.times2
          // r3 could be > that, if so, we overflow
          if (r2 < that)
            (d.times2 , r2)
          else {
            // that <= r3 < 2that
            // 0 <= r3 - that < that
            (succ1(d), r2 - that)
          }
      }

    def /(that: Value[BinNat]): Value[BinNat] =
      this.divmod(that)._1

    def %(that: Value[BinNat]): Value[BinNat] =
      // this could be optimized
      (this: Value[BinNat], that) match {
        case (_, Zero) => this
        case (Zero, _) | (_, B1(Zero)) => Zero
        case (B1(Zero), _) =>
          that match {
            case B1(Zero) => Zero
            case _ => _1
          }
        case (B2(Zero), _) =>
          that match {
            case B2(Zero) => Zero
            case _ =>
              // 2 % n where n > 2
              _2
          }
        case (B2(n), B2(m)) =>
          // (2n1 + 2) / (2n2 + 2) = (n1 + 1) / (n2 + 1)
          // if n mod m = x
          // then 2n mod 2m = 2x
          //
          (n.inc % m.inc).times2
        case (B1(n), _) =>
          // (2n + 1) / that =
          // (n + 1 + n) / that
          val r2 = n.inc % that
          val r1 = n % that
          // n + 1 = d2 * that + r2
          // n = d1 * that  + r1
          // 2n + 1 = (d2 + d1)*that + (r2 + r1)
          val r3 = r1 + r2
          // r3 could be > that, if so, we overflow
          if (r3 < that) r3
          else (r3 - that)
        case (B2(n), _) =>
          // (2n + 2) / that
          //  == 2 * ((n + 1) / that)
          val r = n.inc % that
          // n + 1 = d2 * that + r2
          // 2n + 2 = 2*d2*that + 2*r2
          //
          val r2 = r.times2
          // r3 could be > that, if so, we overflow
          if (r2 < that) r2
          else {
            // that <= r3 < 2that
            // 0 <= r3 - that < that
            r2 - that
          }
      }

    // gcd(a, b) = n
    // means a = ka * n, b = kb * n
    // and gcd(a/n, b/n) == 1
    // if (a == 0 && b == 0) 0
    def gcd(that: Value[BinNat]): Value[BinNat] =
      (this: Value[BinNat], that) match {
        case (a, Zero) => a
        case (Zero, b) => b
        case (a, b) =>
          @annotation.tailrec
          def loop(a: Value[BinNat], b: Value[BinNat]): Value[BinNat] =
            if (a < b) loop(b, a)
            else {
              val r = a % b
              // if the remainder is 0, then b divides a
              if (r == Zero) b
              else loop(b, r)
            }
          loop(a, b)
      }

    // some as (this ^ p) % m
    def powMod(p: Value[BinNat], m: Value[BinNat]): Value[BinNat] =
      if (m eq Zero) this.pow(p)
      else if (m == _1) Zero
      else {
        // reduce down to < m to start
        val self = this % m

        def loop(p: Value[BinNat]): Value[BinNat] = {
          p match {
            case Zero => _1
            case B1(n) =>
              if (n eq Zero) self
              else {
                // this ^ (2n + 1) % m =
                // this * (this^2n) % m
                // this * (this ^ n) ^2 % m
                val half = loop(n)
                // I think we need timesMod to make this fast
                (self * ((half * half) % m)) % m
              }
            case B2(n) =>
              // this ^ (2n + 2) % m =
              // (this^2(n + 1)) % m
              // (this ^ (n+1)) ^2 % m
              val half = loop(n.inc)
              (half * half) % m
          }
        }

        loop(p)
      }

      /**
       * see: https://en.wikipedia.org/wiki/Miller–Rabin_primality_test
       */
      def millerRabinPrime(rand: BoolGen, k: Int): Boolean =
        (this: Value[BinNat]) match {
          case Zero | B1(Zero) => false
          case B2(Zero) | B1(B1(Zero)) => true // 2 or 3
          case B2(_) => false // evens 4 or more is not prime
          case B1(m) =>
            // this >= 5
            type V = Value[BinNat]
            // n = 2m + 1
            // write n = 2^r * d + 1
            def comp(m: V): (V, V) =
              m match {
                case B2(x) =>
                  // m = 2^r * d = 2(n + 1)
                  val (r1, d) = comp(x.inc)
                  (r1.inc, d)
                case notEven =>
                  // r = 0, this is d
                  (Zero, notEven)
              }

            val _4 = _2.times2
            val this_4 = this - _4
            val _n1 = this.dec
            val (r, d) = comp(m)
            // n = this = 2^r * d + 1
            @annotation.tailrec
            def loop(k: Int): Boolean =
              if (k <= 0) true
              else {
                // [2, n - 2] =
                // 2 + [0, n - 4]
                val a = _2 + BinNat.random(rand, this_4)
                val x = a.powMod(d, this)
                if ((x == _1) || (x == _n1)) loop(k - 1)
                else {
                  var r0 = r
                  var x0 = x
                  var isComposite = true
                  while (r0 ne Zero) {
                    x0 = (x0 * x0) % this
                    if (x0 == _n1) {
                      // we continue on the loop
                      isComposite = false
                      r0 = Zero
                    }
                    else {
                      r0 = r0.dec
                    }
                  }
                  if (isComposite) false
                  else loop(k - 1)
                }
              }

            loop(k)
        }

      /**
       * this < 2^bitCount
       * if this != 0, thens
       * 2^(bitCount - 1) <= this
       */
      def bitCount: Value[BinNat] =
        (this: Value[BinNat]) match {
          case Zero => Zero
          case B2(n) =>
            // 2(n + 1)
            n.inc.bitCount.inc
          case _ =>
            (this / _2).bitCount.inc
        }

      def dec: Value[BinNat] =
        (this: Value[BinNat]) match {
          case Zero => Zero
          case B1(n) =>
            n match {
              case Zero => Zero
              case _ =>
                // (2n + 1) - 1
                // = 2(n - 1) + 2
                succ2(n.dec)
            }
          case B2(n) =>
            // 2n + 2 - 1 = 2n + 1
            succ1(n)
        }
  }

  // compute a random Value[BinNat] x such that 0 <= x <= r
  def random(r: BoolGen, upper: Value[BinNat]): Value[BinNat] = {
    upper match {
      case Zero => Zero
      case B1(n) => 
        // x <= 2n + 1
        // x < 2n + 2
        // so there are n + 1 items in each bucket
        // [0, ... n, n + 1 ... 2n + 1]
        // either pick on the left or right half
        val x = random(r, n) 
        if (r.nextBoolean())  x
        else (x + n.inc)
      case _ =>
        // we have an odd number here [0, 1... 2n + 2]
        def genRandIntBits(bits: Value[BinNat], acc: Value[BinNat]): Value[BinNat] = {
          if (bits eq Zero) acc
          else {
            val shift = acc.times2
            val acc1 =
              if (r.nextBoolean()) shift.inc
              else shift
            genRandIntBits(bits.dec, acc1)
          }
        }
        val ex = upper.inc
        val num = genRandIntBits(ex.bitCount, Zero)
        if (num < ex) num
        else {
          // we failed to generate in the range, just try again
          random(r, upper)
        }
    }
  }

  // generate a random prime in [2^(bits - 1) + 1, 2^bits - 1]
  // with probability at most (1/4)^confidence probability of error
  // using confidence = 64 to 128 is probably a good choice
  def randomPrime(r: BoolGen, bits: Int, confidence: Int): Value[BinNat] = {
    if (bits <= 2) // return 2 or 3, the only 2 bit primes
      if (r.nextBoolean()) _2 else succ1(_1)
    else {
      def pow2(n: Int, acc: Value[BinNat]): Value[BinNat] =
        if (n <= 0) acc
        else pow2(n - 1, acc.times2)

      val low = pow2(bits - 1, _1).inc
      val high = pow2(bits, _1).dec
      val diff = high - low

      def loop(): Value[BinNat] = {
        val candidate = random(r, diff) + low
        if (candidate.millerRabinPrime(r, confidence)) candidate
        else loop()
      }

      loop()
    }
  }

  case object Zero extends Value[_0] {
    def toBigInt: BigInt = BigInt(0)
    def inc: Value[BinNat] = B1[_0, Zero.type](Zero)
    def +(that: Value[BinNat]): Value[BinNat] = that
    def *(that: Value[BinNat]): Value[BinNat] = this
  }

  // 2n + 1
  case class B1[B <: BinNat, V <: Value[B]](of: V) extends Value[Succ1[B]]{
    def toBigInt: BigInt = of.toBigInt * 2 + 1
    def inc: Value[BinNat] = B2[B, V](of)
    def +(that: Value[BinNat]): Value[BinNat] =
      that match {
        case Zero => this
        case B1(o1) =>
          // (2n1 + 1) + (2n2 + 1) = 2(n1 + n2) + 2
          succ2(of + o1)
        case B2(o2) =>
          // (2n1 + 1) + (2n2 + 2) = 2(n1 + n2 + 1) + 1
          succ1((of + o2).inc)
      }
    def *(that: Value[BinNat]): Value[BinNat] =
      that match {
        case Zero => Zero
        case v1@B1(o1) =>
          // (2n1 + 1)(2n2 + 1) =
          //   2(2n1n2 + n1 + n2) + 1
          //   2(n1(2n2 + 1) + n2) + 1
          succ1((of * v1) + o1)
        case v2@B2(o2) =>
          // (2n1 + 1)(2n2 + 2) = 4n1n2 + 2n2 + 4n1 + 2
          //   2(n1 * 2(n2 + 1) + n2) + 2
          succ2((of * v2) + o2)
      }
  }
  // 2n + 2
  case class B2[B <: BinNat, V <: Value[B]](of: V) extends Value[Succ2[B]] {
    def toBigInt: BigInt = of.toBigInt * 2 + 2
    // 2n + 2 + 1 = 2(n + 1) + 1
    def inc: Value[BinNat] = B1[BinNat, Value[BinNat]](of.inc)
    def +(that: Value[BinNat]): Value[BinNat] =
      that match {
        case Zero => this
        case B1(o1) =>
          // (2n1 + 2) + (2n2 + 1) = 2(n1 + n2 + 1) + 1
          succ1((of + o1).inc)
        case B2(o2) =>
          // (2n1 + 2) + (2n2 + 2) = 2(n1 + n2 + 1) + 2
          succ2((of + o2).inc)
      }
    def *(that: Value[BinNat]): Value[BinNat] =
      that match {
        case Zero => Zero
        case B1(o1) =>
          // (2n1 + 2)(2n2 + 1) = 4n1n2 + 4n2 + 2n1 + 2
          //   2(n2 * 2(n1 + 1) + n1) + 2
          succ2((o1 * this) + of)
        case v2@B2(o2) =>
          // (2n1 + 2)(2n2 + 2) = 4n1n2 + 4n1 + 4n2 + 4
          // = 2(n1(2 n2 + 2) + 2n2 + 1) + 2
          succ2((of *  v2) + succ1(o2))
      }
  }

  def succ1[B <: BinNat](v: Value[B]): Value[Succ1[B]] =
    B1(v)

  def succ2[B <: BinNat](v: Value[B]): Value[Succ2[B]] =
    B2(v)

  def valueFromBigInt(i: BigInt): Value[BinNat] =
    if (i.compare(BigInt(0)) <= 0) Zero
    else {
      // we are > 0
      // 2n + 1 or 2n + 2 for n >= 0
      val mod = (i % 2).toInt
      val half = i / 2
      if (mod == 1) succ1(valueFromBigInt(half))
      else {
        // i / 2 = n + 1
        succ2(valueFromBigInt(half - 1))
      }
    }

  // there can only be one value of this type: B1
  def half1[B <: BinNat](v: Value[Succ1[B]]): Value[B] =
    v match {
      case B1(h) => h
    }

  // there can only be one value of this type: B2
  def half2[B <: BinNat](v: Value[Succ2[B]]): Value[B] =
    v match {
      case B2(h) => h
    }

  // These exist only to give the types names, they have
  // no values associated with them
  sealed trait _0 extends BinNat

  // 2n + 1
  sealed trait Succ1[B0 <: BinNat] extends BinNat

  // 2n + 2
  sealed trait Succ2[B0 <: BinNat] extends BinNat

  // given a type, get the value back
  sealed trait FromType[B <: BinNat] {
    def value: Value[B]
  }
  object FromType {
    final case class Instance[B <: BinNat](value: Value[B]) extends FromType[B]

    implicit val zeroFromType: FromType[_0] = Instance(Zero)

    implicit def fromType1[B <: BinNat](implicit ft: FromType[B]): FromType[Succ1[B]] =
      Instance(B1(ft.value))

    implicit def fromType2[B <: BinNat](implicit ft: FromType[B]): FromType[Succ2[B]] =
      Instance(B2(ft.value))

    def value[B <: BinNat](implicit ft: FromType[B]): Value[B] =
      ft.value
  }

  sealed trait Inc[B <: BinNat] {
    type Out <: BinNat

    def apply(v: Value[B]): Value[Out]
  }

  object Inc {
    type Aux[B <: BinNat, O <: BinNat] = Inc[B] { type Out = O }

    implicit val inc0: Inc.Aux[_0, Succ1[_0]] =
      new Inc[_0] {
        type Out = Succ1[_0]
        def apply(v0: Value[_0]): Value[Succ1[_0]] =
          B1(v0)
      }

    // (2n + 1) + 1 = 2n + 2
    implicit def incS1[B <: BinNat]: Inc.Aux[Succ1[B], Succ2[B]] =
      new Inc[Succ1[B]] {
        type Out = Succ2[B]
        def apply(v1: Value[Succ1[B]]): Value[Succ2[B]] =
          B2(half1(v1))
      }
    // (2n + 2) + 1 = 2(n + 1) + 1
    implicit def incS2[B <: BinNat, O <: BinNat](implicit inc0: Inc.Aux[B, O]): Inc.Aux[Succ2[B], Succ1[O]] =
      new Inc[Succ2[B]] {
        type Out = Succ1[O]
        def apply(v1: Value[Succ2[B]]): Value[Succ1[inc0.Out]] =
          B1(inc0(half2(v1)))
      }
  }

  // multiply by 2
  sealed trait Times2[B <: BinNat] {
    type Out <: BinNat

    def apply(b: Value[B]): Value[Out]
  }

  object Times2 {
    type Aux[B <: BinNat, O <: BinNat] = Times2[B] { type Out = O }

    // 2 * 0 = 0
    implicit val shift0: Times2.Aux[_0, _0] =
      new Times2[_0] {
        type Out = _0
        def apply(b: Value[_0]): Value[_0] = b
      }
    // 2*(2n + 1) = 2(2n) + 2
    implicit def shiftS1[B <: BinNat, O <: BinNat](implicit sn: Times2.Aux[B, O]): Times2.Aux[Succ1[B], Succ2[O]] =
      new Times2[Succ1[B]] {
        type Out = Succ2[O]
        def apply(b: Value[Succ1[B]]): Value[Out] = {
          val twoN = sn(half1(b))
          B2[sn.Out, twoN.type](twoN)
        }
      }
    // 2*(2n + 2) = 4n + 4 = 2(2n + 1) + 2
    implicit def incS2[B <: BinNat]: Times2.Aux[Succ2[B], Succ2[Succ1[B]]]=
      new Times2[Succ2[B]] {
        type Out = Succ2[Succ1[B]]
        def apply(b: Value[Succ2[B]]): Value[Out] = {
          val twoN1: Value[Succ1[B]] = B1(half2(b))
          B2[Succ1[B], Value[Succ1[B]]](twoN1)
        }
      }
  }

  sealed trait Lt[B1 <: BinNat, B2 <: BinNat]
  object Lt extends Lt1 {
    implicit def apply[B1 <: BinNat, B2 <: BinNat](implicit lt: Lt[B1, B2]): Lt[B1, B2] =
      lt

    implicit def zeroLtSucc1[B <: BinNat]: Lt[_0, Succ1[B]] = inst
    implicit def zeroLtSucc2[B <: BinNat]: Lt[_0, Succ2[B]] = inst

    // 2n + 1 < 2n + 2
    implicit def succ1LtSucc2[B <: BinNat]: Lt[Succ1[B], Succ2[B]] = inst

  }

  trait Lt1 {
    protected def inst[B1 <: BinNat, B2 <: BinNat]: Lt[B1, B2] =
      new Lt[B1, B2] { }

    // 2n1 + 1 < 2n2 + 2 => n1 < n2
    implicit def lt0[B1 <: BinNat, B2 <: BinNat](implicit ltprev: Lt[B1, B2]): Lt[Succ1[B1], Succ1[B2]] = inst
    implicit def lt1[B1 <: BinNat, B2 <: BinNat](implicit ltprev: Lt[B1, B2]): Lt[Succ2[B1], Succ2[B2]] = inst
    implicit def lt2[B1 <: BinNat, B2 <: BinNat](implicit ltprev: Lt[B1, B2]): Lt[Succ2[B1], Succ1[B2]] = inst
    implicit def lt3[B1 <: BinNat, B2 <: BinNat](implicit ltprev: Lt[B1, B2]): Lt[Succ1[B1], Succ2[B2]] = inst
  }

  sealed trait Add[B1 <: BinNat, B2 <: BinNat] {
    type Out <: BinNat

    def apply(b1: Value[B1], b2: Value[B2]): Value[Out]
  }

  object Add extends Add1 {
    type Aux[B1 <: BinNat, B2 <: BinNat, O <: BinNat] = Add[B1, B2] { type Out = O }
    /*
     * 0 + x = 0
     * (2n1 + 1) + (2n2 + 1) = 2*(n1 + n2) + 2
     * (2n1 + 1) + (2n2 + 2) = 2*(n1 + n2 + 1) + 1
     * (2n1 + 2) + (2n2 + 2) = 2*(n1 + n2 + 1) + 2
     *
     * else x + y = y + x
     */
    implicit def add0[B <: BinNat]: Add.Aux[_0, B, B] =
      new Add[_0, B] {
        type Out = B
        def apply(b1: Value[_0], b2: Value[B]): Value[B] = b2
      }
    implicit def addS1[B1 <: BinNat, B2 <: BinNat, O <: BinNat](implicit sn: Add.Aux[B1, B2, O]): Add.Aux[Succ1[B1], Succ1[B2], Succ2[O]] =
      new Add[Succ1[B1], Succ1[B2]] {
        type Out = Succ2[O]
        def apply(b1: Value[Succ1[B1]], b2: Value[Succ1[B2]]): Value[Out] = {
          // (2n1 + 1) + (2n2 + 1) = 2*(n1 + n2) + 2
          val n12: Value[sn.Out] = sn(half1(b1), half1(b2))
          B2[sn.Out, Value[sn.Out]](n12)
        }
      }
    implicit def addS12[B1 <: BinNat, B2 <: BinNat, O1 <: BinNat, O <: BinNat](implicit sn: Add.Aux[B1, B2, O1], i: Inc.Aux[O1, O]): Add.Aux[Succ1[B1], Succ2[B2], Succ1[O]]=
      new Add[Succ1[B1], Succ2[B2]] {
        type Out = Succ1[O]
        def apply(b1: Value[Succ1[B1]], b2: Value[Succ2[B2]]): Value[Out] = {
          // (2n1 + 1) + (2n2 + 2) = 2*(n1 + n2 + 1) + 1
          val n12: Value[i.Out] = i(sn(half1(b1), half2(b2)))
          B1[i.Out, Value[i.Out]](n12)
        }
      }

    implicit def addS21[B1 <: BinNat, B2 <: BinNat, O1 <: BinNat, O <: BinNat](implicit sn: Add.Aux[B1, B2, O1], i: Inc.Aux[O1, O]): Add.Aux[Succ2[B1], Succ1[B2], Succ1[O]]=
      new Add[Succ2[B1], Succ1[B2]] {
        type Out = Succ1[O]
        def apply(b1: Value[Succ2[B1]], b2: Value[Succ1[B2]]): Value[Out] = {
          // (2n1 + 2) + (2n2 + 1) = 2*(n1 + n2 + 1) + 1
          val n12: Value[i.Out] = i(sn(half2(b1), half1(b2)))
          B1[i.Out, Value[i.Out]](n12)
        }
      }
    implicit def addS22[B1 <: BinNat, B2 <: BinNat, O1 <: BinNat, O <: BinNat](implicit sn: Add.Aux[B1, B2, O1], i: Inc.Aux[O1, O]): Add.Aux[Succ2[B1], Succ2[B2], Succ2[O]]=
      new Add[Succ2[B1], Succ2[B2]] {
        type Out = Succ2[O]
        def apply(b1: Value[Succ2[B1]], b2: Value[Succ2[B2]]): Value[Out] = {
          // (2n1 + 2) + (2n2 + 2) = 2*(n1 + n2 + 1) + 2
          val n12: Value[i.Out] = i(sn(half2(b1), half2(b2)))
          B2[i.Out, Value[i.Out]](n12)
        }
      }
  }

  trait Add1 {
    implicit def add0R[B <: BinNat]: Add.Aux[B, _0, B] =
      new Add[B, _0] {
        type Out = B
        def apply(b1: Value[B], b2: Value[_0]): Value[B] = b1
      }
  }

  sealed trait Mult[B1 <: BinNat, B2 <: BinNat] {
    type Out <: BinNat
    def apply(v1: Value[B1], v2: Value[B2]): Value[Out]
  }

  object Mult extends Mult1 {
    type Aux[B1 <: BinNat, B2 <: BinNat, O <: BinNat] = Mult[B1, B2] { type Out = O }


    def apply[B1 <: BinNat, B2 <: BinNat](b1: Value[B1], b2: Value[B2])(implicit mult: Mult[B1, B2]): Value[mult.Out] =
      mult(b1, b2)

    /*
     * 0 * x = 0
     * (2n1 + 1)(2n2 + 1) = 2(2*n1n2 + (n1 + n2)) + 1
     * (2n1 + 1)(2n2 + 2) = 2(2*n1 (n2 + 1) + n2) + 2
     * (2n1 + 2)(2n2 + 2) = 2 *(2*(n1n2 + n1 + n2) + 2)
     *
     * else x * y = y * x
     */
    implicit def mult0[B <: BinNat]: Mult.Aux[_0, B, _0] =
      new Mult[_0, B] {
        type Out = _0
        // 0 * x = 0
        def apply(v1: Value[_0], v2: Value[B]): Value[_0] = Zero
      }

    implicit def multS1[
      B1 <: BinNat,
      B2 <: BinNat,
      A1 <: BinNat,
      P1 <: BinNat](
        implicit
        mult: Mult.Aux[B1, Succ1[B2], P1],
        add: Add.Aux[P1, B2, A1]
        ): Mult.Aux[Succ1[B1], Succ1[B2], Succ1[A1]] =
      new Mult[Succ1[B1], Succ1[B2]] {
        type Out = Succ1[A1]
        // (2n1 + 1)(2n2 + 1) =
        //   2(2n1n2 + n1 + n2) + 1
        //   2(n1(2n2 + 1) + n2) + 1
        def apply(v1: Value[Succ1[B1]], v2: Value[Succ1[B2]]): Value[Out] = {
          val n1 = half1(v1)
          val n2 = half1(v2)
          val p1 = mult(n1, v2)
          val a1 = add(p1, n2)
          B1(a1)
        }
      }

    implicit def multS12[
      B1 <: BinNat,
      B2 <: BinNat,
      Prod12 <: BinNat,
      O <: BinNat](
        implicit mult: Mult.Aux[B1, Succ2[B2], Prod12],
        add: Add.Aux[Prod12, B2, O]
        ): Mult.Aux[Succ1[B1], Succ2[B2], Succ2[O]] =
      new Mult[Succ1[B1], Succ2[B2]] {
        type Out = Succ2[O]
        // (2n1 + 1)(2n2 + 2) = 4n1n2 + 2n2 + 4n1 + 2
        //   2(n1 * 2(n2 + 1) + n2) + 2
        def apply(v1: Value[Succ1[B1]], v2: Value[Succ2[B2]]): Value[Out] = {
          val n1 = half1(v1)
          val n2 = half2(v2)
          val p12: Value[Prod12] = mult(n1, v2)
          val a12: Value[add.Out] = add(p12, n2)
          B2(a12)
        }
      }

    implicit def multS21[
      B1 <: BinNat,
      B2 <: BinNat,
      Prod12 <: BinNat,
      O <: BinNat](
        implicit
        mult: Mult.Aux[B2, Succ2[B1], Prod12],
        addPs: Add.Aux[Prod12, B1, O]
        ): Mult.Aux[Succ2[B1], Succ1[B2], Succ2[O]] =
      new Mult[Succ2[B1], Succ1[B2]] {
        type Out = Succ2[O]
        // (2n1 + 2)(2n2 + 1) = 4n1n2 + 4n2 + 2n1 + 2
        //   2(n2 * 2(n1 + 1) + n1) + 2
        def apply(v1: Value[Succ2[B1]], v2: Value[Succ1[B2]]): Value[Out] = {
          val n1 = half2(v1)
          val n2 = half1(v2)
          val p12: Value[Prod12] = mult(n2, v1)
          val a12: Value[addPs.Out] = addPs(p12, n1)
          B2(a12)
        }
      }


    implicit def multS22[
      B1 <: BinNat,
      B2 <: BinNat,
      P1 <: BinNat,
      A1 <: BinNat](
        implicit
        mult: Mult.Aux[B1, Succ2[B2], P1],
        add1: Add.Aux[P1, Succ1[B2], A1],
      ): Mult.Aux[Succ2[B1], Succ2[B2], Succ2[A1]] =
      new Mult[Succ2[B1], Succ2[B2]] {
        type Out = Succ2[A1]
        // (2n1 + 2)(2n2 + 2) = 4n1n2 + 4n1 + 4n2 + 4
        // = 2(n1(2 n2 + 2) + 2n2 + 1) + 2
        def apply(v1: Value[Succ2[B1]], v2: Value[Succ2[B2]]): Value[Out] = {
          val n1 = half2(v1)
          val n2 = half2(v2)
          val p1 = mult(n1, v2)
          val a1 = add1(p1, B1(n2))
          B2(a1)
        }
      }
  }

  trait Mult1 {
    implicit def mult0R[B <: BinNat]: Mult.Aux[B, _0, _0] =
      new Mult[B, _0] {
        type Out = _0
        // 0 * x = 0
        def apply(v1: Value[B], v2: Value[_0]): Value[_0] = Zero
      }
  }

  sealed trait Pow[B1 <: BinNat, B2 <: BinNat] {
    type Out <: BinNat
    def apply(v1: Value[B1], exp: Value[B2]): Value[Out]
  }

  object Pow {
    type Aux[B1 <: BinNat, B2 <: BinNat, O <: BinNat] = Pow[B1, B2] { type Out = O }

    implicit def powZero[B <: BinNat]: Aux[B, _0, _1] =
      new Pow[B, _0] {
        type Out = _1
        def apply(v1: Value[B], v2: Value[_0]): Value[_1] = succ1(v2)
      }

    implicit def powS1[
      B1 <: BinNat,
      B2 <: BinNat,
      P1 <: BinNat,
      P2 <: BinNat,
      O <: BinNat](
        implicit
        p1: Aux[B1, B2, P1],
        m1: Mult.Aux[P1, P1, P2],
        m2: Mult.Aux[P2, B1, O]
      ): Aux[B1, Succ1[B2], O] =
        new Pow[B1, Succ1[B2]] {
          type Out = O
          def apply(v1: Value[B1], v2: Value[Succ1[B2]]): Value[O] = {
            val n2 = half1(v2)
            val pow1 = p1(v1, n2)
            m2(m1(pow1, pow1), v1)
          }
        }

    implicit def powS2[
      B1 <: BinNat,
      B2 <: BinNat,
      I1 <: BinNat,
      P1 <: BinNat,
      O <: BinNat](
        implicit
        i1: Inc.Aux[B2, I1],
        p1: Aux[B1, I1, P1],
        m1: Mult.Aux[P1, P1, O],
      ): Aux[B1, Succ2[B2], O] =
        new Pow[B1, Succ2[B2]] {
          type Out = O
          def apply(v1: Value[B1], v2: Value[Succ2[B2]]): Value[O] = {
            val n2 = i1(half2(v2))
            val pow = p1(v1, n2)
            m1(pow, pow)
          }
        }
  }

  // smallest factor
  // 0, 2*0 + 1 => Nothing
  // 2(n + 1) => 2
  // 2*1 + 1 => 3
  // 2*2 + 1 => 5
  // 2*3 + 1 => 7
  // 2*4 + 1 => 3
  // 2n + 1 => if (

  type _1 = Succ1[_0]
  type _2 = Succ2[_0]
  type _3 = Succ1[_1]
  type _4 = Succ2[_1] // Succ2[Succ1[_0]]
  type _5 = Succ1[_2]
  type _6 = Succ2[_2]
  type _7 = Succ1[_3]
  type _8 = Succ2[_3]
  type _9 = Succ1[_4]
  type _10 = Succ2[_4]
  type _11 = Succ1[_5]
  type _12 = Succ2[_5]
  type _13 = Succ1[_6]
  type _14 = Succ2[_6]
  type _15 = Succ1[_7]
  type _16 = Succ2[_7]
  type _17 = Succ1[_8]
  type _18 = Succ2[_8]
  type _19 = Succ1[_9]
  type _20 = Succ2[_9]
  type _21 = Succ1[_10]
  type _22 = Succ2[_10]
  type _23 = Succ1[_11]
  type _24 = Succ2[_11]
  type _25 = Succ1[_12]
  type _26 = Succ2[_12]
  type _27 = Succ1[_13]
  type _28 = Succ2[_13]
  type _29 = Succ1[_14]
  type _30 = Succ2[_14]
  type _31 = Succ1[_15]
  type _32 = Succ2[_15]
  type _33 = Succ1[_16]
  type _34 = Succ2[_16]
  type _35 = Succ1[_17]
  type _36 = Succ2[_17]

  // generate the above code
  def makeTypes(max: Int): String = {
    (1 to max)
      .iterator
      .map { i =>
        val mod = i % 2
        val half = (i - 1) / 2

        val cons =
          if (mod == 1) "Succ1"
          else "Succ2"

        s"type _$i = $cons[_$half]"
      }
      .mkString("\n")
  }
}
