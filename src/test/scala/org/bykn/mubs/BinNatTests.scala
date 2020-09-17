package org.bykn.mubs

class BinNatTests extends munit.FunSuite {

  import BinNat._

  implicitly[Inc.Aux[_0, _1]]
  implicitly[Inc.Aux[_1, _2]]

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

  implicitly[Add.Aux[_0, _0, _0]]
  implicitly[Add.Aux[_0, _1, _1]]
  implicitly[Add.Aux[_1, _0, _1]]
  implicitly[Add.Aux[_1, _1, _2]]
  implicitly[Add.Aux[_1, _2, _3]]
  implicitly[Add.Aux[_2, _1, _3]]
  implicitly[Add.Aux[_2, _2, _4]]
  implicitly[Add.Aux[_2, _3, _5]]
  implicitly[Add.Aux[_3, _2, _5]]


  test("test some negative examples: Add") {
    assertNoDiff(
      compileErrors("implicitly[Add.Aux[_0, _2, _3]]"),
    """|error: could not find implicit value for parameter e: org.bykn.mubs.BinNat.Add.Aux[org.bykn.mubs.BinNat._0,org.bykn.mubs.BinNat._2,org.bykn.mubs.BinNat._3]
       |implicitly[Add.Aux[_0, _2, _3]]
       |          ^
       |""".stripMargin)

  }

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

  test("test some negative examples: Mult") {
    assertNoDiff(
      compileErrors("implicitly[Mult.Aux[_0, _2, _3]]"),
    """|error: could not find implicit value for parameter e: org.bykn.mubs.BinNat.Mult.Aux[org.bykn.mubs.BinNat._0,org.bykn.mubs.BinNat._2,org.bykn.mubs.BinNat._3]
       |implicitly[Mult.Aux[_0, _2, _3]]
       |          ^
       |""".stripMargin)

  }
}
