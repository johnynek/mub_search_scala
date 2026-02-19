package org.bykn.mubs

import java.util.BitSet
import org.scalacheck.Gen
import org.scalacheck.Prop.forAll

class PartitionedSearchLaws extends munit.ScalaCheckSuite {
  override def scalaCheckTestParameters =
    super.scalaCheckTestParameters
      .withMinSuccessfulTests(1000)
      .withMaxDiscardRatio(10)

  property("Partitioned.selectByHash assigns each value to exactly one worker") {
    val genValue: Gen[List[Int]] = Gen.listOf(Gen.choose(Int.MinValue, Int.MaxValue))

    forAll(Gen.choose(1, 128), genValue) { (count, value) =>
      val hits =
        (0 until count)
          .count { worker =>
            Partitioned(worker, count).selectByHash(value)
          }
      assertEquals(hits, 1, s"value=$value, count=$count")
    }
  }

  property("Partitioned.selectByHash gives disjoint complete partition of a collection") {
    val genValue: Gen[List[Int]] = Gen.listOf(Gen.choose(Int.MinValue, Int.MaxValue))
    val genValues = Gen.listOf(genValue)

    forAll(Gen.choose(1, 64), genValues) { (count, values) =>
      val indexed = values.zipWithIndex
      val assignments: List[(Int, (List[Int], Int))] =
        indexed.flatMap { entry =>
          (0 until count).collect {
            case worker if Partitioned(worker, count).selectByHash(entry) =>
              (worker, entry)
          }
        }

      assertEquals(assignments.length, indexed.length)

      val grouped = assignments.groupBy(_._2).view.mapValues(_.size).toMap
      assert(grouped.values.forall(_ == 1), s"grouped assignments were not unique: $grouped")
    }
  }

  private def allTrueBitSet(size: Int): BitSet = {
    val bs = new BitSet(size)
    bs.set(0, size)
    bs
  }

  test("sum of partitioned completeCount matches unpartitioned (synthetic tiny instance)") {
    val dim = 3
    val standardCount = 4
    val goalHads = 3
    val alwaysTrue = allTrueBitSet(standardCount)
    val cpFn: (Int, Int) => Int = (_, _) => 0

    def countFor(optPart: Option[Partitioned]): Long =
      new MubBuild.Instance(
        dim = dim,
        standardCount = standardCount,
        goalHads = goalHads,
        cpFn = cpFn,
        orthBitSet = alwaysTrue,
        ubBitSet = alwaysTrue,
        optPart = optPart
      ).syncResult.completeCount

    val full = countFor(None)
    assert(full > 0L)

    List(2, 3, 5, 7).foreach { partCount =>
      val sumParts =
        (0 until partCount)
          .map { worker =>
            countFor(Some(Partitioned(worker, partCount)))
          }
          .sum
      assertEquals(sumParts, full, s"partCount=$partCount")
    }
  }

  test("sum of partitioned completeCount matches unpartitioned (real tiny d=3,n=3 instance)") {
    val space = new VectorSpace.Space[BinNat._3, Cyclotomic.L3](dim = 3, realBits = 20)
    val orthSet = space.buildCache(space.isOrth(_, space.epsOrth))
    val ubSet = space.buildCache(space.isUnbiased(_, space.epsUb))
    val goalMubs = 3

    def run(optPart: Option[Partitioned]): MubBuild.Instance#Result =
      new MubBuild.Instance(
        dim = space.dim,
        standardCount = space.standardCount,
        goalHads = goalMubs,
        cpFn = space.conjProdInt _,
        orthBitSet = orthSet,
        ubBitSet = ubSet,
        optPart = optPart
      ).syncResult

    val full = run(None)
    val partCount = 4
    val parts = (0 until partCount).map { worker =>
      run(Some(Partitioned(worker, partCount)))
    }

    val partSum = parts.iterator.map(_.completeCount).sum
    assertEquals(partSum, full.completeCount)

    val anyPartitionFound = parts.exists(_.firstCompleteExample.nonEmpty)
    assertEquals(anyPartitionFound, full.firstCompleteExample.nonEmpty)
  }
}
