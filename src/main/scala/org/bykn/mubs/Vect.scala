package org.bykn.mubs

import algebra.ring.Rng
import scala.reflect.ClassTag

sealed abstract class Vect[B <: BinNat, A] {
  import Vect.ComplexSpace

  def apply(idx: Int): A
  def updated(idx: Int, a1: A): Vect[B, A]
  // pointwise multiplication
  def *(that: Vect[B, A])(implicit cs: ComplexSpace[A]): Vect[B, A]
  def conj(implicit cs: ComplexSpace[A]): Vect[B, A]

  def trace(implicit cs: ComplexSpace[A]): cs.Trace

  def cross[B1 <: BinNat, B2 <: BinNat](that: Vect[B1, A])(implicit m: BinNat.Mult.Aux[B, B1, B2], cs: ComplexSpace[A]): Vect[B2, A]

  def length: Int
}

object Vect {
  trait ComplexSpace[A] {
    type Trace
    def conj(a: A): A
    // commutative and associative
    def times(a1: A, a2: A): A

    def emptyTrace: Trace
    def tracePlus(t: Trace, a: A): Trace
  }

  private object Impl {
    class ArrayVect[B <: BinNat, A](ary: Array[A]) extends Vect[B, A] {
      @inline
      implicit def clsa: ClassTag[A] = ClassTag(ary.getClass().getComponentType())

      def apply(idx: Int): A = ary(idx)
      def updated(idx: Int, a1: A): Vect[B, A] =
        new ArrayVect(ary.updated(idx, a1))
      // this is a pointwise multiplication
      def *(that: Vect[B, A])(implicit cs: ComplexSpace[A]): Vect[B, A] = {
        var idx = 0
        val res: Array[A] = new Array[A](ary.length)
        while (idx < ary.length) {
          res(idx) = cs.times(ary(idx), that(idx))
          idx += 1
        }
        new ArrayVect(res)
      }

      def conj(implicit cs: ComplexSpace[A]): Vect[B, A] = {
        var idx = 0
        val res: Array[A] = new Array[A](ary.length)
        while (idx < ary.length) {
          res(idx) = cs.conj(ary(idx))
          idx += 1
        }
        new ArrayVect(res)
      }

      def trace(implicit cs: ComplexSpace[A]): cs.Trace = {
        var idx = 0
        var res = cs.emptyTrace
        while (idx < ary.length) {
          res = cs.tracePlus(res, ary(idx))
        }
        res
      }

      def length: Int = ary.length

      def cross[B1 <: BinNat, B2 <: BinNat](that: Vect[B1, A])(implicit m: BinNat.Mult.Aux[B, B1, B2], cs: ComplexSpace[A]): Vect[B2, A] = {
        val newLen = length * that.length
        // make the right the small index
        val res: Array[A] = new Array[A](newLen)
        for {
          left <- 0 until length
          leftPart = left * that.length
          right <- 0 until that.length
        } {
          res(leftPart + right) = cs.times(ary(left), that(right))
        }

        new ArrayVect(res)
      }
    }
  }


  def apply[B <: BinNat, A](as: Array[A])(implicit ft: BinNat.FromType[B]): Vect[B, A] = {
    if (as.length != ft.value.toBigInt.toInt) {
      throw new IllegalArgumentException(s"expected length of input (${as.length}) != ${ft.value}")
    }
    new Impl.ArrayVect(as)
  }
}
