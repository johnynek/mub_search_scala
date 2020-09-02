package org.bykn.mubs

import algebra.ring.CommutativeRig
import shapeless.{Nat, Succ}
import spire.math.{Complex, Natural, Real, Rational}

/**
 * represents values in field adjoining rationals with the 2^N-th primitive
 * root of unity: exp(2 * pi * i / 2^N) for some N > 0
 *
 * See: https://encyclopediaofmath.org/wiki/Cyclotomic_field
 *
 */
sealed abstract class Cyclotomic[N <: Nat, C] {
  def add(left: C, right: C): C
  def sub(left: C, right: C): C
  def mult(left: C, right: C): C

  // this is |x|^2 of the current number
  def abs2(c: C): Real
  def re(c: C): Real
  def im(c: C): Real

  def one: C
  def zero: C
  // the principle root of unity at this level
  def omega: C

  def root: N

  def toComplex(c: C): Complex[Real] =
    Complex(re(c), im(c))
}

object Cyclotomic {

  def apply[N <: Nat, C](implicit C: Cyclotomic[N, C]): Cyclotomic[N, C] = C

  implicit val rationalZeroIsCyclotomic: Cyclotomic[Nat._0, Rational] =
    new Cyclotomic[Nat._0, Rational] {
      def add(left: Rational, right: Rational): Rational =
        left + right
      def sub(left: Rational, right: Rational): Rational =
        left - right
      def mult(left: Rational, right: Rational): Rational =
        left * right

      // this is |x|^2 of the current number
      def abs2(c: Rational): Real =
        Real.Exact(c * c)
      def re(c: Rational): Real = Real.Exact(c)
      def im(c: Rational): Real = Real.zero

      def one = Rational.one
      def zero = Rational.zero
      // omega to the 2^(root) power == one
      def omega = Rational.one

      def root: Nat._0 = Nat._0
    }

  implicit val rationalOneIsCyclotomic: Cyclotomic[Nat._1, Rational] =
    new Cyclotomic[Nat._1, Rational] {
      def add(left: Rational, right: Rational): Rational =
        left + right
      def sub(left: Rational, right: Rational): Rational =
        left - right
      def mult(left: Rational, right: Rational): Rational =
        left * right

      // this is |x|^2 of the current number
      def abs2(c: Rational): Real =
        Real.Exact(c * c)
      def re(c: Rational): Real = Real.Exact(c)
      def im(c: Rational): Real = Real.zero

      def one = Rational.one
      def zero = Rational.zero
      // omega to the 2^root power == one
      def omega = -Rational.one

      val root: Nat._1 = Succ()
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
  implicit def rootNIsCyclotomic[N <: Nat, C](implicit C: Cyclotomic[N, C]): Cyclotomic[Succ[N], Root[Succ[N], C]] =
    new Cyclotomic[Succ[N], Root[Succ[N], C]] {
      def add(left: Root[Succ[N], C], right: Root[Succ[N], C]): Root[Succ[N], C] =
        // (a1 + sqrt(w) * b1) + (a2 + sqrt(w) * b2) =
        Root(C.add(left.alpha, right.alpha), C.add(left.beta, right.beta))

      def sub(left: Root[Succ[N], C], right: Root[Succ[N], C]): Root[Succ[N], C] =
        // (a1 + sqrt(w) * b1) - (a2 + sqrt(w) * b2) =
        Root(C.sub(left.alpha, right.alpha), C.sub(left.beta, right.beta))

      def mult(left: Root[Succ[N], C], right: Root[Succ[N], C]): Root[Succ[N], C] = {
        // (a1 + sqrt(w) * b1) * (a2 + sqrt(w) * b2) =
        // ((a1 * a2 + w * b1 * b2) + sqrt(w) * (b1 * a2 + b2 * a1)
        val a12 = C.mult(left.alpha, right.alpha)
        val b12 = C.mult(left.beta, right.beta)
        val a1b2 = C.mult(left.alpha, right.beta)
        val a2b1 = C.mult(left.beta, right.alpha)

        Root(
          C.add(a12, C.mult(C.omega, b12)),
          C.add(a1b2, a2b1))
      }

      // re(a + sqrt(w) * b) =
      // re(a) + re(sqrt(w)) * re(b) - im(sqrt(w)) * im(b)
      def re(c: Root[Succ[N], C]): Real =
        C.re(c.alpha) + reRootOmega * C.re(c.beta) - (imRootOmega * C.im(c.beta))

      // im(a + sqrt(w) * b) =
      // im(a) + im(sqrt(w)) * re(b) + re(sqrt(w)) * im(b)
      def im(c: Root[Succ[N], C]): Real =
        C.im(c.alpha) + imRootOmega * C.re(c.beta) + (reRootOmega * C.im(c.beta))

      def abs2(c: Root[Succ[N], C]): Real =
        re(c).pow(2) + im(c).pow(2)

      val zero = Root(C.zero, C.zero)
      val one = Root(C.one, C.zero)
      // omega to the 2^root power == one
      val omega: Root[Succ[N], C] = Root(C.zero, C.one)

      // Re(\sqrt{a+ib}) = \sqrt{(r+a)/2}
      // for omega, r = 1
      val reRootOmega: Real =
        ((Real.one + C.re(C.omega)) / Real.two).sqrt

      // Im(\sqrt{a+ib}) = b/\sqrt{2(r+a)}
      // for omega, r = 1
      val imRootOmega: Real =
        C.im(C.omega) / ((Real.two * (Real.one + C.re(C.omega))).sqrt)

      val root: Succ[N] = Succ()
    }

  // 1 = 1st roots
  type N0 = Nat._0
  type C0 = Rational

  // 2 = 2nd roots (1, -1)
  type N1 = Succ[Nat._0]
  type C1 = Rational

  // 2^2 = 4th roots
  type N2 = Succ[N1]
  type C2 = Root[N2, C1]

  // 2^3 = 8th roots
  type N3 = Succ[N2]
  type C3 = Root[N3, C2]

  // 2^4 = 16th roots
  type N4 = Succ[N3]
  type C4 = Root[N4, C3]

  // 2^5 = 32th roots
  type N5 = Succ[N4]
  type C5 = Root[N5, C4]
}

