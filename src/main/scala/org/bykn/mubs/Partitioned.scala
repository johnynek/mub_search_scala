package org.bykn.mubs

import cats.data.Validated
import com.monovore.decline.Opts
import cats.syntax.all._

case class Partitioned(worker: Int, count: Int) {
  require((0 <= worker) && (worker < count), s"require: 0 <= worker($worker) < count($count)")

  def selectByHash(a: Any): Boolean = {
    val hc = a.hashCode
    // make sure it is positive
    val posHs = hc & Int.MaxValue
    (posHs % count) == worker
  }

  def nonTrivial: Option[Partitioned] =
    if (count == 1) None
    else Some(this)
}

object Partitioned {
  val opts: Opts[Partitioned] =
    Opts.option[Int]("part_worker", "which partition worker to run")
      .product(
        Opts.option[Int]("part_count", "how many partitions in total")
      )
      .mapValidated { case (w, c) =>
        if ((0 <= w) && (w < c)) Validated.valid(Partitioned(w, c))
        else Validated.invalidNel(s"part_worker($w) must be non-negative and less than part_count($c)")
      }
}
