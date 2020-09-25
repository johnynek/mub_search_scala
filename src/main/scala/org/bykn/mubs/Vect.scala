package org.bykn.mubs

import algebra.ring.Rng
import scala.reflect.ClassTag

sealed abstract class Vect[L <: BinNat, N <: BinNat, A] {

  def apply(idx: Int): A
  def updated(idx: Int, a1: A): Vect[L, N, A]
  // pointwise multiplication
  def *(that: Vect[L, N, A])(implicit cs: Cyclotomic[N, A]): Vect[L, N, A]
  def +(that: Vect[L, N, A])(implicit cs: Cyclotomic[N, A]): Vect[L, N, A]
  def conj(implicit cs: Cyclotomic[N, A]): Vect[L, N, A]

  def trace(implicit cs: Cyclotomic[N, A]): A

  def innerProd(that: Vect[L, N, A])(implicit C: Cyclotomic[N, A]): A

  def cross[B1 <: BinNat, B2 <: BinNat](that: Vect[B1, N, A])(implicit m: BinNat.Mult.Aux[L, B1, B2], cs: Cyclotomic[N, A]): Vect[B2, N, A]

  def length: Int
}

object Vect {
  private object Impl {
    class ArrayVect[L <: BinNat, N <: BinNat, A](ary: Array[A]) extends Vect[L, N, A] {
      @inline
      implicit def clsa: ClassTag[A] = ClassTag(ary.getClass().getComponentType())

      def apply(idx: Int): A = ary(idx)
      def updated(idx: Int, a1: A): Vect[L, N, A] =
        new ArrayVect(ary.updated(idx, a1))
      // this is a pointwise multiplication
      def *(that: Vect[L, N, A])(implicit cs: Cyclotomic[N, A]): Vect[L, N, A] = {
        var idx = 0
        val res: Array[A] = new Array[A](ary.length)
        while (idx < ary.length) {
          res(idx) = cs.times(ary(idx), that(idx))
          idx += 1
        }
        new ArrayVect(res)
      }

      def +(that: Vect[L, N, A])(implicit cs: Cyclotomic[N, A]): Vect[L, N, A] = {
        var idx = 0
        val res: Array[A] = new Array[A](ary.length)
        while (idx < ary.length) {
          res(idx) = cs.plus(ary(idx), that(idx))
          idx += 1
        }
        new ArrayVect(res)
      }

      def conj(implicit cs: Cyclotomic[N, A]): Vect[L, N, A] = {
        var idx = 0
        val res: Array[A] = new Array[A](ary.length)
        while (idx < ary.length) {
          res(idx) = cs.conj(ary(idx))
          idx += 1
        }
        new ArrayVect(res)
      }

      def trace(implicit cs: Cyclotomic[N, A]): A = {
        var idx = 0
        var res = cs.zero
        while (idx < ary.length) {
          res = cs.plus(res, ary(idx))
          idx += 1
        }
        res
      }

      def innerProd(that: Vect[L, N, A])(implicit C: Cyclotomic[N, A]): A = {
        var idx = 0
        var res = C.zero
        while (idx < ary.length) {
          res = C.plus(res, C.times(C.conj(ary(idx)), that(idx)))
          idx += 1
        }
        res
      }

      def length: Int = ary.length

      def cross[B1 <: BinNat, B2 <: BinNat](that: Vect[B1, N, A])(implicit m: BinNat.Mult.Aux[L, B1, B2], cs: Cyclotomic[N, A]): Vect[B2, N, A] = {
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


  def rootVector[L <: BinNat, N <: BinNat, A: ClassTag](as: Int*)(implicit ft: BinNat.FromType[L], C: Cyclotomic[N, A]): Vect[L, N, A] = {
    if (as.length != ft.value.toBigInt.toInt) {
      throw new IllegalArgumentException(s"expected length of input (${as.length}) != ${ft.value}")
    }
    val aAry = as.map(C.roots(_)).toArray
    new Impl.ArrayVect(aAry)
  }

  def standardBasisDim2[N <: BinNat, K <: BinNat, C](
    implicit C: Cyclotomic[N, C],
    ct: ClassTag[C],
    mult: BinNat.Mult.Aux[BinNat._4, K, N],
    ft: BinNat.FromType[K]): List[List[Vect[BinNat._2, N, C]]] = {

    val ki = ft.value.toBigInt.toInt

    def i(root: Int): Int = ki * root

    List(
      List(rootVector(0, 0), rootVector(0, i(2))),
      List(rootVector(0, i(1)), rootVector(0, i(3)))
    )
  }

  def standardBasisDim3[N <: BinNat, K <: BinNat, C](
    implicit C: Cyclotomic[N, C],
    ct: ClassTag[C],
    mult: BinNat.Mult.Aux[BinNat._3, K, N],
    ft: BinNat.FromType[K]): List[List[Vect[BinNat._3, N, C]]] = {

    val ki = ft.value.toBigInt.toInt

    def i(root: Int): Int = ki * root

    List(
      List(
        rootVector(0, 0, 0),
        rootVector(0, i(1), i(2)),
        rootVector(0, i(2), i(1)),
        ),
      List(
        rootVector(0, i(1), i(1)),
        rootVector(0, i(2), 0),
        rootVector(0, 0, i(2)),
        ),
      List(
        rootVector(0, i(2), i(2)),
        rootVector(0, 0, i(1)),
        rootVector(0, i(1), 0),
        )
    )
  }
}
