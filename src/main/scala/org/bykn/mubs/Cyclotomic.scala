package org.bykn.mubs

import algebra.ring.CommutativeRing
import shapeless.{Nat, Succ}
import shapeless.ops.nat.ToInt
import spire.math.{Complex, Natural, Real, Rational, SafeLong}

/**
 * represents values in field adjoining rationals with the 2^N-th primitive
 * root of unity: exp(2 * pi * i / 2^N) for some N > 0
 *
 * See: https://encyclopediaofmath.org/wiki/Cyclotomic_field
 *
 */
sealed abstract class Cyclotomic[N <: Nat, C] extends CommutativeRing[C] {
  // this is |x|^2 of the current number
  def abs2(c: C): Real
  def re(c: C): Real
  def im(c: C): Real

  def one: C
  def zero: C
  // the principle root of unity at this level
  def omega: C
  // this is Re(omega)
  def reOmega: Real
  // this is Im(omega)
  def imOmega: Real

  // this can often be optimized
  def timesOmega(c: C): C

  def root: N

  // a vector of length 2^N
  // starting with 1, omega, omega^2, ...
  def roots: Vector[C]

  def toComplex(c: C): Complex[Real] =
    Complex(re(c), im(c))
}

object Cyclotomic {

  def apply[N <: Nat, C](implicit C: Cyclotomic[N, C]): Cyclotomic[N, C] = C

  implicit val rationalZeroIsCyclotomic: Cyclotomic[Nat._0, Rational] =
    new Cyclotomic[Nat._0, Rational] {
      def plus(left: Rational, right: Rational): Rational =
        left + right
      override def minus(left: Rational, right: Rational): Rational =
        left - right
      def times(left: Rational, right: Rational): Rational =
        left * right

      def negate(r: Rational): Rational = -r
      // this is |x|^2 of the current number
      def abs2(c: Rational): Real = Real.Exact(c * c)
      def re(c: Rational): Real = Real.Exact(c)
      def im(c: Rational): Real = Real.zero

      def one = Rational.one
      def zero = Rational.zero
      // omega to the 2^(root) power == one
      // omega to the (2^root - 1) power != one
      def omega = Rational.one
      def timesOmega(c: Rational) = c
      def reOmega = Rational.one
      def imOmega = Rational.zero

      def root: Nat._0 = Nat._0

      val roots: Vector[Rational] = Vector(one)
    }

  implicit val rationalOneIsCyclotomic: Cyclotomic[Nat._1, Rational] =
    new Cyclotomic[Nat._1, Rational] {
      def plus(left: Rational, right: Rational): Rational =
        left + right
      override def minus(left: Rational, right: Rational): Rational =
        left - right
      def times(left: Rational, right: Rational): Rational =
        left * right

      def negate(r: Rational): Rational = -r
      // this is |x|^2 of the current number
      def abs2(c: Rational): Real = Real.Exact(c * c)
      def re(c: Rational): Real = Real.Exact(c)
      def im(c: Rational): Real = Real.zero

      def one = Rational.one
      def zero = Rational.zero
      // omega to the 2^root power == one
      def omega = -Rational.one
      def timesOmega(r: Rational) = -r
      val reOmega = -Real.one
      val imOmega = Real.zero

      val root: Nat._1 = Succ()
      val roots: Vector[Rational] = Vector(one, omega)
    }

  implicit val safeLongOneIsCyclotomic: Cyclotomic[Nat._1, SafeLong] =
    new Cyclotomic[Nat._1, SafeLong] {
      def plus(left: SafeLong, right: SafeLong): SafeLong =
        left + right
      override def minus(left: SafeLong, right: SafeLong): SafeLong =
        left - right
      def times(left: SafeLong, right: SafeLong): SafeLong =
        left * right

      def negate(r: SafeLong): SafeLong = -r
      // this is |x|^2 of the current number
      def abs2(c: SafeLong): Real = Real.Exact(c * c)
      def re(c: SafeLong): Real = Real.Exact(c)
      def im(c: SafeLong): Real = Real.zero

      def one = SafeLong.one
      def zero = SafeLong.zero
      // omega to the 2^root power == one
      def omega = -SafeLong.one
      val reOmega = -Real.one
      val imOmega = Real.zero
      def timesOmega(c: SafeLong) = -c

      val root: Nat._1 = Succ()
      val roots: Vector[SafeLong] = Vector(one, omega)
    }


  /**
   * this is alpha + sqrt(w(n)) * beta
   * this representation works because we are dealing with roots of 2^N, so
   */
  case class Root[N <: Nat, C](alpha: C, beta: C)

  type _2 = Succ[Nat._1]

  // there are roots 2 and higher
  // can be represented with rationals alone. the second root,
  // we need i, which cannot be (complex numbers)
  implicit def rootNIsCyclotomic[N <: Nat, C](implicit C: Cyclotomic[N, C], toI: ToInt[N]): Cyclotomic[Succ[N], Root[Succ[N], C]] =
    new Cyclotomic[Succ[N], Root[Succ[N], C]] {
      def plus(left: Root[Succ[N], C], right: Root[Succ[N], C]): Root[Succ[N], C] =
        if (left eq zero) right
        else if (right eq zero) left
        else {
          // (a1 + sqrt(w) * b1) + (a2 + sqrt(w) * b2) =
          Root(C.plus(left.alpha, right.alpha), C.plus(left.beta, right.beta))
        }

      override def minus(left: Root[Succ[N], C], right: Root[Succ[N], C]): Root[Succ[N], C] =
        // (a1 + sqrt(w) * b1) - (a2 + sqrt(w) * b2) =
        Root(C.minus(left.alpha, right.alpha), C.minus(left.beta, right.beta))

      def times(left: Root[Succ[N], C], right: Root[Succ[N], C]): Root[Succ[N], C] =
        if ((left eq zero) || (right eq zero)) zero
        else if (left eq one) right
        else if (right eq one) left
        else {
          // (a1 + sqrt(w) * b1) * (a2 + sqrt(w) * b2) =
          // ((a1 * a2 + w * b1 * b2) + sqrt(w) * (b1 * a2 + b2 * a1)
          val a12 = C.times(left.alpha, right.alpha)
          val b12 = C.times(left.beta, right.beta)
          val a1b2 = C.times(left.alpha, right.beta)
          val a2b1 = C.times(left.beta, right.alpha)

          Root(
            C.plus(a12, C.timesOmega(b12)),
            C.plus(a1b2, a2b1))
        }

      def timesOmega(c: Root[Succ[N], C]): Root[Succ[N], C] =
        // sqrt(w) * (a2 + sqrt(w) * b2) =
        // w * b2 + sqrt(w) a2
        if (c eq zero) zero
        else if (c eq one) omega
        // we could imagine special casing any element of roots
        // but that would take roots.length work on each
        // call for a maybe rare case
        else Root(C.timesOmega(c.beta), c.alpha)

      def negate(c: Root[Succ[N], C]) =
        if (c eq zero) zero
        else Root(C.negate(c.alpha), C.negate(c.beta))

      // re(a + sqrt(w) * b) =
      // re(a) + re(sqrt(w)) * re(b) - im(sqrt(w)) * im(b)
      def re(c: Root[Succ[N], C]): Real =
        if (c eq zero) Real.zero
        else if (c eq one) Real.one
        else if (c eq omega) reOmega
        else C.re(c.alpha) + reOmega * C.re(c.beta) - (imOmega * C.im(c.beta))

      // im(a + sqrt(w) * b) =
      // im(a) + im(sqrt(w)) * re(b) + re(sqrt(w)) * im(b)
      def im(c: Root[Succ[N], C]): Real =
        if ((c eq zero) || (c eq one)) Real.zero
        else if (c eq omega) imOmega
        else C.im(c.alpha) + imOmega * C.re(c.beta) + (reOmega * C.im(c.beta))

      //|a + sqrt(w)*b|^2 =
      //(a + sqrt(w)*b)*(a' + sqrt(w)'b')
      //|a|^2 + |w|*|b|^2 + a'*sqrt(w)*b + a*sqrt(w)'b'
      //|a|^2 + |b|^2 + 2 re(a' * sqrt(w) * b)
      //|a|^2 + |b|^2 + 2 re((re(a) - i im(a))*(re(sw) + i im(sw))*(re(b) + i im(b)))
      //|a|^2 + |b|^2 + 2 re(
      //  re(a)re(sw)re(b) +
      // i re(a)re(sw)im(b) +
      // i re(a)im(sw)re(b) +
      // -re(a)im(sw)im(b) +
      // -i im(a)re(sw)re(b) +
      //   im(a)re(sw)im(b) +
      //   im(a)im(sw)re(b) +
      // +i im(a)im(sw)im(b))
      def abs2(c: Root[Succ[N], C]): Real =
        if (c eq zero) Real.zero
        else if ((c eq one) || (c eq omega)) Real.one
        else {
          val a = c.alpha
          val b = c.beta

          val a2 = C.abs2(a)
          val b2 = C.abs2(b)
          val reA = C.re(a)
          val reB = C.re(b)
          val imA = C.im(a)
          val imB = C.im(b)

          val rePart = (
              reA * (reOmega * reB - imOmega * imB)
            + imA * (reOmega * imB + imOmega * reB)
          )

          a2 + b2 + 2 * rePart
        }

      val zero = Root(C.zero, C.zero)
      val one = Root(C.one, C.zero)

      // omega to the 2^root power == one
      // this omega = sqrt(C.omega)
      val omega: Root[Succ[N], C] = Root(C.zero, C.one)

      /**
       * cos(theta) = cos(C.theta/2) = sqrt((1 + cos(C.theta))/2)
       */
      val reOmega: Real = ((Real.one + C.reOmega) / Real.two).sqrt

      /**
       * sin(theta) = sin(C.theta/2) = sqrt((1 - cos(C.theta))/2)
       */
      val imOmega: Real = ((Real.one - C.reOmega) / Real.two).sqrt

      val root: Succ[N] = Succ()

      val roots: Vector[Root[Succ[N], C]] = {
        val m = toI() + 1
        val twoM = 1 << m
        (1 until twoM).scanLeft(one) { (prev, _) =>
          timesOmega(prev)
        }
        .toVector
      }

    }

  // 1 = 1st roots
  type N0 = Nat._0
  type C0 = Rational

  // 2 = 2nd roots (1, -1)
  type N1 = Succ[Nat._0]
  type C1 = Rational
  type L1 = SafeLong

  // 2^2 = 4th roots
  type N2 = Succ[N1]
  type C2 = Root[N2, C1]
  type L2 = Root[N2, L1]

  // 2^3 = 8th roots
  type N3 = Succ[N2]
  type C3 = Root[N3, C2]
  type L3 = Root[N3, L2]

  // 2^4 = 16th roots
  type N4 = Succ[N3]
  type C4 = Root[N4, C3]
  type L4 = Root[N4, L3]

  // 2^5 = 32th roots
  type N5 = Succ[N4]
  type C5 = Root[N5, C4]
  type L5 = Root[N5, L4]

  // 2^6 = 64th roots
  type N6 = Succ[N5]
  type C6 = Root[N6, C5]
  type L6 = Root[N6, L5]

  // 2^7 = 128th roots
  type N7 = Succ[N6]
  type C7 = Root[N7, C6]
  type L7 = Root[N7, L6]
}

