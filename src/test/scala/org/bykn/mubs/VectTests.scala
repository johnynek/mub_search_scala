package org.bykn.mubs

import spire.math.Real

class VectTests extends munit.FunSuite {

  def areMubs[L <: BinNat, N <: BinNat, C](vs: List[List[Vect[L, N, C]]])(implicit C: Cyclotomic[N, C], F: BinNat.FromType[L]) = {

    // this is a complete set
    assert(vs.length == F.value.toBigInt.toInt)

    for {
      b1 <- vs
      b2 <- vs
    } {
      if (b1 eq b2) {
        // check orthogonality
        for {
          v1 <- b1
          v2 <- b1
        } {
          if (v1 eq v2) {
            // the norm2 is d^2
            assert(C.abs2(v1.innerProd(v2)) == Real(F.value.toBigInt.toInt).pow(2))
          }
          else {
            assert(C.abs2(v1.innerProd(v2)) == Real.zero)
          }
        }
      }
      else {
        // check unbiasedness
        for {
          v1 <- b1
          v2 <- b2
        } {
          // the norm2 is d
          assert(C.abs2(v1.innerProd(v2)) == Real(F.value.toBigInt.toInt))
        }
      }
    }
  }

  test("Vect.standardBasisDim2 is a mub N=4") {
    val n4 =
      Vect.standardBasisDim2[BinNat._4, BinNat._1, Cyclotomic.L4]

    areMubs(n4)
  }

  test("Vect.standardBasisDim2 is a mub N=8") {
    val n8 =
      Vect.standardBasisDim2[BinNat._8, BinNat._2, Cyclotomic.L8]

    areMubs(n8)
  }

  test("Vect.standardBasisDim2 is a mub N=12") {
    val n12 =
      Vect.standardBasisDim2[BinNat._12, BinNat._3, Cyclotomic.L12]

    areMubs(n12)
  }

  test("Vect.standardBasisDim2 is a mub N=24") {
    val n24 =
      Vect.standardBasisDim2[BinNat._24, BinNat._6, Cyclotomic.L24]

    areMubs(n24)
  }

  test("Vect.standardBasisDim3 is a mub N=3") {
    val b =
      Vect.standardBasisDim3[BinNat._3, BinNat._1, Cyclotomic.L3]

    areMubs(b)
  }

  test("Vect.standardBasisDim3 is a mub N=6") {
    val b =
      Vect.standardBasisDim3[BinNat._6, BinNat._2, Cyclotomic.L6]

    areMubs(b)
  }

  test("Vect.standardBasisDim3 is a mub N=12") {
    val b =
      Vect.standardBasisDim3[BinNat._12, BinNat._4, Cyclotomic.L12]

    areMubs(b)
  }

  test("Vect.standardBasisDim3 is a mub N=24") {
    val b =
      Vect.standardBasisDim3[BinNat._24, BinNat._8, Cyclotomic.L24]

    areMubs(b)
  }
}
