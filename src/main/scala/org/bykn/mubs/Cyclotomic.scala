package org.bykn.mubs

import algebra.ring.CommutativeRing
import spire.math.{Complex, Real, Rational, SafeLong}

/**
 * represents values in field adjoining rationals with the N-th primitive
 * root of unity: exp(2 * pi * i / N) for some N > 0
 *
 * See: https://encyclopediaofmath.org/wiki/Cyclotomic_field
 *
 */
sealed abstract class Cyclotomic[N <: BinNat, C] extends CommutativeRing[C] {
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

  final def root(implicit N: BinNat.FromType[N]): N.Out = N.value

  // a vector of length N
  // starting with 1, omega, omega^2, ...
  def roots: Vector[C]

  def toComplex(c: C): Complex[Real] =
    Complex(re(c), im(c))
}

object Cyclotomic {

  def apply[N <: BinNat, C](implicit C: Cyclotomic[N, C]): Cyclotomic[N, C] = C

  implicit val rationalOneIsCyclotomic: Cyclotomic[BinNat._2, Rational] =
    new Cyclotomic[BinNat._2, Rational] {
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
      // omega to the root power == one
      def omega = -Rational.one
      def timesOmega(r: Rational) = -r
      val reOmega = -Real.one
      val imOmega = Real.zero

      val roots: Vector[Rational] = Vector(one, omega)
    }

  implicit val safeLongOneIsCyclotomic: Cyclotomic[BinNat._2, SafeLong] =
    new Cyclotomic[BinNat._2, SafeLong] {
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

      val roots: Vector[SafeLong] = Vector(one, omega)
    }


  /**
   * this is alpha + sqrt(w(n)) * beta
   * this representation works because we are dealing with roots of 2^N, so
   *
   * This allows us to work with square roots of what-ever the omega is for C
   */
  case class Root2[C](alpha: C, beta: C)

  // there are roots 2 and higher
  // can be represented with rationals alone. the second root,
  // we need i, which cannot be (complex numbers)
  implicit def rootNIsCyclotomic[N <: BinNat, C, O <: BinNat](implicit C: Cyclotomic[N, C], p: BinNat.Times2.Aux[N, O]): Cyclotomic[O, Root2[C]] =
    new Cyclotomic[O, Root2[C]] {
      def plus(left: Root2[C], right: Root2[C]): Root2[C] =
        if (left eq zero) right
        else if (right eq zero) left
        else {
          // (a1 + sqrt(w) * b1) + (a2 + sqrt(w) * b2) =
          Root2(C.plus(left.alpha, right.alpha), C.plus(left.beta, right.beta))
        }

      override def minus(left: Root2[C], right: Root2[C]): Root2[C] =
        // (a1 + sqrt(w) * b1) - (a2 + sqrt(w) * b2) =
        Root2(C.minus(left.alpha, right.alpha), C.minus(left.beta, right.beta))

      def times(left: Root2[C], right: Root2[C]): Root2[C] =
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

          Root2(
            C.plus(a12, C.timesOmega(b12)),
            C.plus(a1b2, a2b1))
        }

      def timesOmega(c: Root2[C]): Root2[C] =
        // sqrt(w) * (a2 + sqrt(w) * b2) =
        // w * b2 + sqrt(w) a2
        if (c eq zero) zero
        else if (c eq one) omega
        // we could imagine special casing any element of roots
        // but that would take roots.length work on each
        // call for a maybe rare case
        else Root2(C.timesOmega(c.beta), c.alpha)

      def negate(c: Root2[C]) =
        if (c eq zero) zero
        else Root2(C.negate(c.alpha), C.negate(c.beta))

      // re(a + sqrt(w) * b) =
      // re(a) + re(sqrt(w)) * re(b) - im(sqrt(w)) * im(b)
      def re(c: Root2[C]): Real =
        if (c eq zero) Real.zero
        else if (c eq one) Real.one
        else if (c eq omega) reOmega
        else C.re(c.alpha) + reOmega * C.re(c.beta) - (imOmega * C.im(c.beta))

      // im(a + sqrt(w) * b) =
      // im(a) + im(sqrt(w)) * re(b) + re(sqrt(w)) * im(b)
      def im(c: Root2[C]): Real =
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
      def abs2(c: Root2[C]): Real =
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

      val zero = Root2(C.zero, C.zero)
      val one = Root2(C.one, C.zero)

      // omega to the 2^root power == one
      // this omega = sqrt(C.omega)
      val omega: Root2[C] = Root2(C.zero, C.one)

      /**
       * cos(theta) = cos(C.theta/2) = sqrt((1 + cos(C.theta))/2)
       */
      val reOmega: Real = ((Real.one + C.reOmega) / Real.two).sqrt

      /**
       * sin(theta) = sin(C.theta/2) = sqrt((1 - cos(C.theta))/2)
       */
      val imOmega: Real = ((Real.one - C.reOmega) / Real.two).sqrt

      val roots: Vector[Root2[C]] = {
        val thisSize = C.roots.length * 2
        (1 until thisSize).scanLeft(one) { (prev, _) =>
          timesOmega(prev)
        }
        .toVector
      }

    }

  // 1 = 1st roots
  type C1 = Rational
  type L1 = SafeLong

  // 2 = 2nd roots (1, -1)
  type C2 = Rational
  type L2 = SafeLong

  // 2^2 = 4th roots
  type C4 = Root2[C2]
  type L4 = Root2[L2]

  // 2^3 = 8th roots
  type C8 = Root2[C4]
  type L8 = Root2[L4]

  // 2^4 = 16th roots
  type C16 = Root2[C8]
  type L16 = Root2[L8]

  // 2^5 = 32th roots
  type C32 = Root2[C16]
  type L32 = Root2[L16]
}

