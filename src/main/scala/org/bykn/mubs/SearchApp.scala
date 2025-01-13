package org.bykn.mubs

import cats.data.{NonEmptyList, Validated}
import com.monovore.decline.{CommandApp, Opts}
import java.io.{DataInputStream, DataOutputStream, FileInputStream, FileOutputStream, InputStream, OutputStream}
import java.nio.file.Path
import java.util.concurrent.Executors
import java.util.zip.{GZIPInputStream, GZIPOutputStream}
import scala.concurrent.duration.Duration.Inf
import scala.concurrent.{Await, ExecutionContext, Future}

object SearchApp extends CommandApp(
  name = "mub-search",
  header = "search for approximate mutually unbiased bases",
  main = {
    import VectorSpace.Space

    import cats.implicits._

    val dim = Opts.option[Int]("dim", "the dimension we are working in, should be small!").mapValidated { d =>
      if (d < 2) Validated.invalidNel(s"invalid dimension: $d, should be >= 2")
      else Validated.valid(d)
    }

    val goalMubs = Opts.option[Int]("mubs", "the number of mutually unbiased bases we try to find")

    val threads: Opts[(ExecutionContext => Unit) => Unit] =
      Opts.option[Int]("threads", "number of threads to use, default = number of processors")
        .withDefault(Runtime.getRuntime().availableProcessors())
        .map { t =>
          { (callback: ExecutionContext => Unit) =>
            val eserv = Executors.newFixedThreadPool(t)
            try {
              val ec = ExecutionContext.fromExecutorService(eserv)
              callback(ec)
            }
            finally {
              eserv.shutdown()
            }
          }
        }


    val root = Opts.option[Int]("root", "what root of unity")

    val space = root
      .mapValidated { d =>

        val validSizes: List[Int] =
          List(2, 3, 4, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 27, 30, 32, 36)

        if (validSizes.contains(d)) Validated.valid {
          d match {
            case 2 => { (d: Int, bits: Int) => new Space[BinNat._2, Cyclotomic.L2](d, bits) }
            case 3 => { (d: Int, bits: Int) => new Space[BinNat._3, Cyclotomic.L3](d, bits) }
            case 4 => { (d: Int, bits: Int) => new Space[BinNat._4, Cyclotomic.L4](d, bits) }
            case 6 => { (d: Int, bits: Int) => new Space[BinNat._6, Cyclotomic.L6](d, bits) }
            case 8 => { (d: Int, bits: Int) => new Space[BinNat._8, Cyclotomic.L8](d, bits) }
            case 9 => { (d: Int, bits: Int) => new Space[BinNat._9, Cyclotomic.L9](d, bits) }
            case 10 => { (d: Int, bits: Int) => new Space[BinNat._10, Cyclotomic.L10](d, bits) }
            case 12 => { (d: Int, bits: Int) => new Space[BinNat._12, Cyclotomic.L12](d, bits) }
            case 15 => { (d: Int, bits: Int) => new Space[BinNat._15, Cyclotomic.L15](d, bits) }
            case 16 => { (d: Int, bits: Int) => new Space[BinNat._16, Cyclotomic.L16](d, bits) }
            case 18 => { (d: Int, bits: Int) => new Space[BinNat._18, Cyclotomic.L18](d, bits) }
            case 20 => { (d: Int, bits: Int) => new Space[BinNat._20, Cyclotomic.L20](d, bits) }
            case 24 => { (d: Int, bits: Int) => new Space[BinNat._24, Cyclotomic.L24](d, bits) }
            case 27 => { (d: Int, bits: Int) => new Space[BinNat._27, Cyclotomic.L27](d, bits) }
            case 30 => { (d: Int, bits: Int) => new Space[BinNat._30, Cyclotomic.L30](d, bits) }
            case 32 => { (d: Int, bits: Int) => new Space[BinNat._32, Cyclotomic.L32](d, bits) }
            case 36 => { (d: Int, bits: Int) => new Space[BinNat._36, Cyclotomic.L36](d, bits) }
            case _ =>
              sys.error(s"expected $d in $validSizes")
          }
        }
        else
          Validated.invalidNel(s"invalid root: $d. valid values: ${validSizes}")
      }

    val orthTab = Opts.option[Path]("orth_tab", "path to orthogonality table")
    val ubTab = Opts.option[Path]("ub_tab", "path to unbiasedness table")
    val tableOpts: Opts[(Path, Path)] = orthTab.product(ubTab)

    val limitOpt =
        Opts.option[Int]("limit", "limit printing out to this many mubs").orNone

    val spaceOpt =
      VectorSpace.realBits
        .product(dim)
        .product(space)
        .map { case ((b, d), fn) => fn(d, b) }

    val search =
      (spaceOpt, goalMubs.orNone, threads, tableOpts, Opts.flag("count", "show the total count (default false)").orFalse)
        .mapN { case (space, mubsOpt, cont, (orthPath, ubPath), showCount) =>
          // dim is the most we can get
          val mubs = mubsOpt.getOrElse(space.dim)

          cont { implicit ec =>
            val orthBS = VectorSpace.readPath(space, true, orthPath)
            val ubBS = VectorSpace.readPath(space, false, ubPath)
            Await.result(VectorSpace.search(space, orthBS, ubBS, mubs, showCount), Inf)
          }
        }

    val search0 =
      (spaceOpt, goalMubs.orNone, threads, tableOpts, limitOpt)
        .mapN { case (space, mubsOpt, cont, (orthPath, ubPath), limit) =>
          // dim is the most we can get
          val mubs = mubsOpt.getOrElse(space.dim)

          cont { implicit ec =>
            val orthBS = VectorSpace.readPath(space, true, orthPath)
            val ubBS = VectorSpace.readPath(space, false, ubPath)
            Await.result(VectorSpace.search0(space, orthBS, ubBS, mubs, limit), Inf)
          }
        }


    val info =
      (spaceOpt,
        threads,
        (Opts.flag("bases", "compute all the standard bases and give the size") *> orthTab).orNone,
        Opts.flag("sync", "run synchronous (less memory, but no concurrency)").orFalse,
        (goalMubs.product(ubTab)).orNone,
        limitOpt
        )
        .mapN { (space, cont, bases0, runSync, mubsOpt0, limit) =>
          cont { implicit ec =>
            val bases = bases0.map { path =>
              VectorSpace.readPath(space, true, path)
            }
            val mubsOpt = mubsOpt0.map { case (n, path) =>
              (n, VectorSpace.readPath(space, false, path))
            }
            Await.result(VectorSpace.runInfo(space, bases, runSync, mubsOpt, limit), Inf)
          }
        }

    val writeTable =
      (spaceOpt,
        threads,
        Opts.flag("orth", "build the orthTable").as(true)
          .orElse(Opts.flag("unbiased", "build the unbiasedness table").as(false)),
        Opts.option[Path]("output", "file to write to"),
        VectorSpace.TableMode.opts
        )
        .mapN { (space, cont, isOrth, path, tabMode) =>
          cont { implicit ec =>
            val output = new FileOutputStream(path.toFile)
            val gz = new GZIPOutputStream(output)
            val data = new DataOutputStream(gz)
            val fut = VectorSpace.writeTable(space, isOrth, data, tabMode)
            try Await.result(fut, Inf)
            finally {
              data.close()
            }
          }
        }

    val quantSearch = {
      (spaceOpt,
        threads,
        Opts.option[Long]("seed", "the seed to use, or use nanoTime").orElse(Opts(System.nanoTime())),
        Opts.option[Int]("count", "the number of pairs to check, default = 1000").orElse(Opts(1000)))
        .mapN { (space, cont, seed, cnt) =>
          cont { implicit ec =>
            Await.result(VectorSpace.quantBoundSearch(space, seed, cnt), Inf)
          }
        }
    }

    val quantSearch2 = {
      (dim,
        root,
        Opts.option[Int]("mult", "finer multiplier on roots for bounding"),
        threads,
        Opts.option[Long]("seed", "the seed to use, or use nanoTime").orElse(Opts(System.nanoTime())),
        Opts.option[Int]("count", "the number of pairs to check, default = 1000").orElse(Opts(1000)))
        .mapN { (dim, n, k, cont, seed, cnt) =>
          cont { implicit ec =>
            Await.result(VectorSpace.quantBound2Search(dim = dim, n = n, k = k, seed = seed, trials = cnt), Inf)
          }
        }
    }

    val extend6 =
      (threads, tableOpts, VectorSpace.Extend6.opts).mapN { case (cont, (orthPath, ubPath), ex6) =>
        cont { implicit ec =>
          val orthBS = ex6.readPath(true, orthPath)
          val ubBS = ex6.readPath(false, ubPath)
          val f = ex6.run(orthSet = orthBS, mubSet = ubBS)
          Await.result(f, Inf)
        }
      }

    Opts.subcommand("search", "run a search for mubs")(search)
      .orElse(
        Opts.subcommand("search0", "run a parallel search for mubs")(search0))
      .orElse(
        Opts.subcommand("info", "show the count of bases and or mub vectors")(info))
      .orElse(
        Opts.subcommand("write_table", "compute an orthogonality/unbiasedness table and write to file")(writeTable))
      .orElse(
        Opts.subcommand("quant_search", "explore the tightness of the quantization bound")(quantSearch))
      .orElse(
        Opts.subcommand("quant_search2", "explore the tightness of the quantization bound")(quantSearch2))
      .orElse(
        Opts.subcommand("extend6", "try to extend standard product bases")(extend6))
  }

)