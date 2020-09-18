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

object BinNat {

  /**
   * Values correspond the actual numbers of a given type
   */
  sealed abstract class Value[B <: BinNat] {
    type Size = B
    def toBigInt: BigInt
    override def toString = toBigInt.toString
  }

  case object Zero extends Value[_0] {
    def toBigInt: BigInt = BigInt(0)
  }

  // 2n + 1
  case class B1[B <: BinNat, V <: Value[B]](of: V) extends Value[Succ1[B]]{
    def toBigInt: BigInt = of.toBigInt * 2 + 1
  }
  // 2n + 2
  case class B2[B <: BinNat, V <: Value[B]](of: V) extends Value[Succ2[B]] {
    def toBigInt: BigInt = of.toBigInt * 2 + 2
  }

  /**
   * This gives us a way to hold a Value of an unknown
   * type, which is to say, when we don't statically
   * know the value of the number
   */
  sealed abstract class WithType {
    type B <: BinNat
    def value: Value[B]

    override def toString = value.toString
    override def equals(that: Any): Boolean =
      that match {
        case wt: WithType => value == wt.value
        case _ => false
      }
    override def hashCode = value.hashCode
  }

  object WithType {
    def apply[B0 <: BinNat](v: Value[B0]): WithType { type B = B0 } =
      new WithType {
        type B = B0
        def value = v
      }

    val Zero: WithType { type B = _0 } =
      apply(BinNat.Zero)
  }

  def valueFromBigInt(i: BigInt): WithType =
    if (i.compare(BigInt(0)) <= 0) WithType.Zero
    else {
      // we are > 0
      val mod = (i % 2).toInt
      val half = valueFromBigInt(i / 2)
      if (mod == 1) WithType(B1[half.B, Value[half.B]](half.value))
      else WithType(B2[half.B, Value[half.B]](half.value))
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
    type Out <: Value[B]
    def value: Out
  }
  object FromType {
    implicit val zeroFromType: FromType[_0] =
      new FromType[_0] {
        type Out = Zero.type
        def value = Zero
      }
    implicit def fromType1[B <: BinNat](implicit ft: FromType[B]): FromType[Succ1[B]] =
      new FromType[Succ1[B]] {
        type Out = B1[B, ft.Out]
        val value = B1(ft.value)
      }
    implicit def fromType2[B <: BinNat](implicit ft: FromType[B]): FromType[Succ2[B]] =
      new FromType[Succ2[B]] {
        type Out = B2[B, ft.Out]
        val value = B2(ft.value)
      }

    def value[B <: BinNat](implicit ft: FromType[B]): ft.Out =
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
