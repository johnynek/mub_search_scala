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

object Cyclotomic extends Priority1Cyclotomic {

  def apply[N <: BinNat, C](implicit C: Cyclotomic[N, C]): Cyclotomic[N, C] = C

  implicit val rationalTwoIsCyclotomic: Cyclotomic[BinNat._2, Rational] =
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

  implicit val safeLongTwoIsCyclotomic: Cyclotomic[BinNat._2, SafeLong] =
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
   *
   * This allows us to work with square roots of what-ever the omega is for C
   */
  case class Root2[C](alpha: C, beta: C)

  // there are roots 2 and higher
  // can be represented with rationals alone. the second root,
  // we need i, which cannot be (complex numbers)
  implicit def root2IsCyclotomic[N <: BinNat, C, O <: BinNat](implicit C: Cyclotomic[N, C], p: BinNat.Times2.Aux[N, O]): Cyclotomic[O, Root2[C]] =
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

  /**
   * (w')^3 = w
   * this is alpha + w' * beta + w'*w' * gamma
   *
   * This allows us to work with cube roots of what-ever the omega is for C
   */
  case class Root3[C](alpha: C, beta: C, gamma: C)

  implicit def root3IsCyclotomic[N <: BinNat, C, O <: BinNat](implicit C: Cyclotomic[N, C], p: BinNat.Mult.Aux[BinNat._3, N, O]): Cyclotomic[O, Root3[C]] =
    new Cyclotomic[O, Root3[C]] {
      def plus(left: Root3[C], right: Root3[C]): Root3[C] =
        if (left eq zero) right
        else if (right eq zero) left
        else
          Root3(
            C.plus(left.alpha, right.alpha),
            C.plus(left.beta, right.beta),
            C.plus(left.gamma, right.gamma))

      override def minus(left: Root3[C], right: Root3[C]): Root3[C] =
        Root3(
          C.minus(left.alpha, right.alpha),
          C.minus(left.beta, right.beta),
          C.minus(left.gamma, right.gamma))

      def times(left: Root3[C], right: Root3[C]): Root3[C] =
        if ((left eq zero) || (right eq zero)) zero
        else if (left eq one) right
        else if (right eq one) left
        else {
          // C.omega = w3
          // (a1 + w1 * b1 + w2 * c1) * (a2 + w1 * b2 + w2 * c2) =
          //        (a1 * a2 + w3 * (b1 * c2 + c1 * b2))
          // + w1 * (a1 * b2 + a2 * b1 + w3 * c1 * c2)
          // + w2 * (a1 * c2 + b1 * b2 + c1 * a2)
          val a1a2 = C.times(left.alpha, right.alpha)
          val b1c2 = C.times(left.beta, right.gamma)
          val c1b2 = C.times(left.gamma, right.beta)

          val a1b2 = C.times(left.alpha, right.beta)
          val b1a2 = C.times(left.beta, right.alpha)
          val c1c2 = C.times(left.gamma, right.gamma)

          val a1c2 = C.times(left.alpha, right.gamma)
          val b1b2 = C.times(left.beta, right.beta)
          val c1a2 = C.times(left.gamma, right.alpha)

          Root3(
            C.plus(a1a2, C.timesOmega(C.plus(b1c2, c1b2))),
            C.plus(C.plus(a1b2, b1a2), C.timesOmega(c1c2)),
            C.plus(C.plus(a1c2, b1b2), c1a2))
        }

      def timesOmega(c: Root3[C]): Root3[C] =
        // w1(a + w1 b + w2 c) =
        //  wc + w1 a + w2 b
        if (c eq zero) zero
        else if (c eq one) omega
        else if (c eq omega) omega2
        // we could imagine special casing any element of roots
        // but that would take roots.length work on each
        // call for a maybe rare case
        else Root3(C.timesOmega(c.gamma), c.alpha, c.beta)

      def negate(c: Root3[C]) =
        if (c eq zero) zero
        else Root3(C.negate(c.alpha), C.negate(c.beta), C.negate(c.gamma))

      // re(a + w1 * b + w2 *c) =
      // re(a) + re(w) * re(b) - im(w1) * im(b) + re(w2) * re(c) - im(w2) * im(c)
      def re(c: Root3[C]): Real =
        if (c eq zero) Real.zero
        else if (c eq one) Real.one
        else if (c eq omega) reOmega
        else if (c eq omega2) reOmega2
        else {
          C.re(c.alpha) +
          (reOmega * C.re(c.beta)) -
          (imOmega * C.im(c.beta)) +
          (reOmega2 * C.re(c.gamma)) -
          (imOmega2 * C.im(c.gamma))
        }

      // im(a + sqrt(w) * b) =
      // im(a) + im(w1) * re(b) + re(w1) * im(b) + im(w2) * re(c) + re(w2) * im(c)
      def im(c: Root3[C]): Real =
        if ((c eq zero) || (c eq one)) Real.zero
        else if (c eq omega) imOmega
        else if (c eq omega2) imOmega2
        else {
          C.im(c.alpha) +
          (imOmega * C.re(c.beta)) +
          (reOmega * C.im(c.beta)) +
          (imOmega2 * C.re(c.gamma)) +
          (reOmega2 * C.im(c.gamma))
        }

      def abs2(c: Root3[C]): Real =
        if (c eq zero) Real.zero
        else if ((c eq one) || (c eq omega)) Real.one
        else {
          val r = re(c)
          val i = im(c)

          (r*r) + (i*i)
        }

      val zero = Root3(C.zero, C.zero, C.zero)
      val one = Root3(C.one, C.zero, C.zero)

      // this omega = pow(C.omega, 1/3)
      val omega: Root3[C] = Root3(C.zero, C.one, C.zero)
      val omega2: Root3[C] = Root3(C.zero, C.zero, C.one)

      /**
       * theta is the previous omega
       * w = theta/3
       * using cos(x+y) = cos(x)cos(y) - sin(x)sin(y)
       *
       * cos(3w) = cos(theta) = cos(w) * (4*cos^2 w - 3)
       * we need to solve a cubic equation to find cos(w) = x
       *
       * 4x^3 - 3x - cos(theta) = 0
       * see: https://en.wikipedia.org/wiki/Cubic_equation#General_cubic_formula
       */
      val reOmega: Real = {
        /*
        val a = 4
        // b = 0
        val c = -3
        // d = -C.reOmega

        // delta0 = b^2 - 3ac = 36
        val delta0 = Real(36)
        // delta1 = 2b^3 - 9*a*b*c + 27 * a^2 + d
        val delta1 = -Real(27 * a * a) * C.reOmega

        val innerRoot = delta1.pow(2) - 4 * delta0.pow(3)
        val constC = ((delta1 - innerRoot.sqrt)/Real.two).nroot(3)

        // eps = (1)^(1/3)
        // (-1/3a) * (eps * C + delta0/(eps * C)) =
        // (-1/3a) * (eps * C + conj(eps) * delta0/C) =
        val res = -(Real.one / Real(3*a))*(constC + (delta0 / constC))
        println(s"{res = $res, constC = $constC, innerRoot = $innerRoot, delta1 = $delta1, delta0 = $delta0, C.reOmega = ${C.reOmega}")
        res
        */
        // this is a bummer because it precludes using algebraic,
        // TODO: get things working without cos/acos
        // but it should be correct:
        Real.cos(Real.acos(C.reOmega) / Real(3))
      }

      /**
       * sqrt(1 - reOmega^2)
       */
      val imOmega: Real =
        (Real.one - reOmega * reOmega).sqrt

      // the real(omega^2)
      // cos(2w) = cos^2 w - sin^2(w)
      //         = 2 cos^2 w - 1
      val reOmega2: Real =
        Real.two * reOmega * reOmega - Real.one

      // the im(omega^2)
      // sin(2w) = 2*sinw * cosw
      val imOmega2: Real =
        Real.two * reOmega * imOmega

      val roots: Vector[Root3[C]] = {
        val thisSize = C.roots.length * 3
        (1 until thisSize).scanLeft(one) { (prev, _) =>
          timesOmega(prev)
        }
        .toVector
      }

    }

  // 1st root, which is to say 1
  type C1 = Rational
  type L1 = SafeLong

  // 2 = 2nd roots (1, -1)
  type C2 = Rational
  type L2 = SafeLong

  // 3
  type C3 = Root3[C1]
  type L3 = Root3[L1]

  // 2^2 = 4th roots
  type C4 = Root2[C2]
  type L4 = Root2[L2]

  // 6th roots 3 * 2
  type C6 = Root3[C2]
  type L6 = Root3[L2]

  // 2^3 = 8th roots
  type C8 = Root2[C4]
  type L8 = Root2[L4]

  // 3^2 = 9
  type C9 = Root3[C3]
  type L9 = Root3[L3]

  // 4*3 = 12
  type C12 = Root3[C4]
  type L12 = Root3[L4]

  // 2^4 = 16th roots
  type C16 = Root2[C8]
  type L16 = Root2[L8]

  // 3*6 = 18
  type C18 = Root3[C6]
  type L18 = Root3[L6]

  // 3 * 8 = 24
  type C24 = Root3[C8]
  type L24 = Root3[L8]

  // 3 * 9 = 27
  type C27 = Root3[C9]
  type L27 = Root3[L9]

  // 2^5 = 32th roots
  type C32 = Root2[C16]
  type L32 = Root2[L16]
}

trait Priority1Cyclotomic {

  implicit val rationalOneIsCyclotomic: Cyclotomic[BinNat._1, Rational] =
    new Cyclotomic[BinNat._1, Rational] {
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
      def omega = Rational.one
      def timesOmega(r: Rational) = r
      def reOmega = Real.one
      def imOmega = Real.zero

      val roots: Vector[Rational] = Vector(one)
    }

  implicit val safeLongOneIsCyclotomic: Cyclotomic[BinNat._1, SafeLong] =
    new Cyclotomic[BinNat._1, SafeLong] {
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
      def omega = SafeLong.one
      def reOmega = Real.one
      def imOmega = Real.zero
      def timesOmega(c: SafeLong) = c

      val roots: Vector[SafeLong] = Vector(one)
    }
}

